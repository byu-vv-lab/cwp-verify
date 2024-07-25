from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker
from antlr4.error.ErrorStrategy import ParseCancellationException
from antlr4.error.ErrorListener import ConsoleErrorListener, ErrorListener
from antlr4.tree.Tree import TerminalNode
from antlr4.Token import Token

from returns.result import Failure, Result, Success
from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result
from returns.functions import not_
from returns.curry import partial

from typing import Tuple

from bpmncwpverify.antlr.StateLexer import StateLexer
from bpmncwpverify.antlr.StateParser import StateParser
from bpmncwpverify.antlr.StateListener import StateListener

from bpmncwpverify.error import (
    Error,
    StateMultipleDefinitionError,
    StateSyntaxError,
    StateUnknownTypeError,
)

from bpmncwpverify import typechecking


class ThrowingErrorListener(ErrorListener):
    def __init__(self):
        super().__init__()

    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        msg = "line {}:{} {}".format(line, column, msg)
        raise ParseCancellationException(msg)


def _get_parser(file_contents: str) -> Result[StateParser, Error]:
    input_stream = InputStream(file_contents)
    lexer = StateLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = StateParser(stream)
    parser.removeErrorListener(ConsoleErrorListener.INSTANCE)
    parser.addErrorListener(ThrowingErrorListener())
    return Success(parser)


def _parse_state(parser: StateParser) -> Result[StateParser.StateContext, Error]:
    try:
        tree = parser.state()
        return Success(tree)
    except ParseCancellationException as exception:
        msg = str(exception)
        failure_value = StateSyntaxError(msg)
        return Failure(failure_value)


class SymbolTable:
    __slots__ = ["_consts", "_enums", "_id2type", "_vars"]

    class _Listener(StateListener):
        __slots__ = ["_duplicates", "_first_def", "_symbol_table"]

        def __init__(self) -> None:
            super().__init__()
            self._duplicates: dict[str, Tuple[int, int]] = dict()
            self._first_def: dict[str, Tuple[int, int]] = dict()
            self._symbol_table: "SymbolTable" = SymbolTable()

        @staticmethod
        def _add_definition(
            definitions: dict[str, Tuple[int, int]], id: str, line: int, column: int
        ) -> None:
            if id in definitions:
                prev_line = definitions[id][0]
                prev_column = definitions[id][1]
                error = StateMultipleDefinitionError(
                    id, line, column, prev_line, prev_column
                )
                raise Exception(error)
            else:
                definitions[id] = (line, column)

        @staticmethod
        def _get_id_and_add_definition(
            definitions: dict[str, Tuple[int, int]], id_node: TerminalNode
        ) -> str:
            id: str = id_node.getText()
            symbol: Token = id_node.getSymbol()
            SymbolTable._Listener._add_definition(
                definitions, id, symbol.line, symbol.column
            )
            return id

        @staticmethod
        def _get_values(
            definitions: dict[str, Tuple[int, int]], ctx: StateParser.Id_setContext
        ) -> set[str]:
            get_id = SymbolTable._Listener._get_id_and_add_definition
            result: set[str] = (
                {get_id(definitions, i) for i in ctx.getChildren()}
                if ctx is not None
                else set()
            )

            return result

        def exitEnum_type_decl(self, ctx: StateParser.Enum_type_declContext):
            get_id = SymbolTable._Listener._get_id_and_add_definition
            id: str = get_id(self._first_def, ctx.ID())
            values: set[str] = SymbolTable._Listener._get_values(
                self._first_def, ctx.id_set()
            )

            self._symbol_table._add_enum_type_decl(id, values)

        def exitConst_var_decl(self, ctx: StateParser.Const_var_declContext):
            get_id = SymbolTable._Listener._get_id_and_add_definition
            id: str = get_id(self._first_def, ctx.ID(0))
            type_: str = ctx.type_().getText()
            init: str = ctx.ID(1).getText()

            self._symbol_table._add_const_decl(id, type_, init)

        def exitVar_decl(self, ctx: StateParser.Var_declContext):
            get_id = SymbolTable._Listener._get_id_and_add_definition
            id: str = get_id(self._first_def, ctx.ID(0))
            type_: str = ctx.type_().getText()
            init: str = ctx.ID(1)

            definitions: dict[str, Tuple[int, int]] = dict()
            values: set[str] = SymbolTable._Listener._get_values(
                definitions, ctx.id_set()
            )

            self._symbol_table._add_var_decl(id, type_, init, values)

    def __init__(self) -> None:
        self._consts: dict[str, Tuple[str, str]] = dict()
        self._enums: dict[str, set[str]] = dict()
        self._id2type: dict[str, str] = dict()
        self._vars: dict[str, Tuple[str, str, set[str]]] = dict()

    def _add_enum_type_decl(self, id: str, values: set[str]) -> None:
        # requires
        assert id not in self._id2type and id not in self._enums
        for i in values:
            assert i not in self._id2type

        self._enums[id] = values
        self._id2type[id] = typechecking.ENUM

        for v in values:
            self._id2type[v] = id

    def _add_const_decl(self, id: str, type: str, init: str) -> Error:
        # requires
        assert id not in self._id2type and id not in self._consts

        self._consts[id] = (type, init)
        self._id2type[id] = type

    def _add_var_decl(self, id: str, type: str, init: str, values: set[str]) -> Error:
        # requires
        assert id not in self._id2type and id not in self._vars

        self._vars[id] = (type, init, values)
        self._id2type[id] = type

    @staticmethod
    def _build(context: StateParser.StateContext) -> Result["SymbolTable", Error]:
        listener = SymbolTable._Listener()
        try:
            ParseTreeWalker.DEFAULT.walk(listener, context)
            return Success(listener._symbol_table)
        except Exception as exception:
            # requires
            assert len(exception.args) == 1
            error: Error = exception.args[0]
            return Failure(error)

    @staticmethod
    def _type_check_consts(symbol_table: "SymbolTable") -> Result["SymbolTable", Error]:
        def get_type_init(init: str) -> Result[str, Error]:
            return (
                symbol_table.get_type(init)
                .bind(get_type_assign)
                .lash(lambda e: typechecking.get_type_literal(e.id))
            )

        for key in symbol_table._consts:
            type_, init = symbol_table._consts[key]
            get_type_assign = partial(typechecking.get_type_assign, type_)
            result: Result[str, Error] = flow(
                init, get_type_init, bind_result(get_type_assign)
            )
            if not_(is_successful)(result):
                return Failure(result.failure())
        return Success(symbol_table)

    @staticmethod
    def _type_check_vars(symbol_table: "SymbolTable") -> Result["SymbolTable", Error]:
        return Failure(NotImplementedError)

    @staticmethod
    def _type_check(symbol_table: "SymbolTable") -> Result["SymbolTable", Error]:
        result: Result["SymbolTable", Error] = flow(
            symbol_table,
            SymbolTable._type_check_consts,
            # bind_result(SymbolTable._type_check_vars),
        )

        return result

    def get_type(self, id: str) -> Result[str, Error]:
        if id in self._id2type:
            return Success(self._id2type[id])
        return Failure(StateUnknownTypeError(id))

    def is_defined(self, id) -> bool:
        return is_successful(self.get_type(id))

    @staticmethod
    def build(state_def: str) -> Result["SymbolTable", Error]:
        result: Result["SymbolTable", Error] = flow(
            state_def,
            _get_parser,
            bind_result(_parse_state),
            bind_result(SymbolTable._build),
            bind_result(SymbolTable._type_check),
        )
        return result
