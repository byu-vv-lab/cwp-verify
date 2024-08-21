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

from typing import Iterable, Any

from bpmncwpverify.antlr.StateLexer import StateLexer
from bpmncwpverify.antlr.StateParser import StateParser
from bpmncwpverify.antlr.StateListener import StateListener

from bpmncwpverify.error import (
    Error,
    StateInitNotInValues,
    StateMultipleDefinitionError,
    StateSyntaxError,
    StateUnknownTypeError,
)

from bpmncwpverify import typechecking


class ThrowingErrorListener(ErrorListener):  # type: ignore[misc]
    def __init__(self) -> None:
        super().__init__()

    def syntaxError(
        self,
        recognizer: Any,
        offendingSymbol: Any,
        line: int,
        column: int,
        msg: str,
        e: Exception,
    ) -> None:
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
        tree: StateParser.StateContext = parser.state()  # type: ignore[no-untyped-call]
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
            self._duplicates: dict[str, tuple[int, int]] = dict()
            self._first_def: dict[str, tuple[int, int]] = dict()
            self._symbol_table: "SymbolTable" = SymbolTable()

        @staticmethod
        def _add_definition(
            definitions: dict[str, tuple[int, int]], id: str, line: int, column: int
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
            definitions: dict[str, tuple[int, int]], id_node: TerminalNode
        ) -> str:
            id: str = id_node.getText()
            symbol: Token = id_node.getSymbol()
            SymbolTable._Listener._add_definition(
                definitions, id, symbol.line, symbol.column
            )
            return id

        @staticmethod
        def _get_values(
            definitions: dict[str, tuple[int, int]], ctx: StateParser.Id_setContext
        ) -> set[str]:
            get_id = SymbolTable._Listener._get_id_and_add_definition
            result: set[str] = (
                {get_id(definitions, i) for i in ctx.getChildren()}
                if ctx is not None
                else set()
            )

            return result

        def exitEnum_type_decl(self, ctx: StateParser.Enum_type_declContext) -> None:
            get_id = SymbolTable._Listener._get_id_and_add_definition
            id: str = get_id(self._first_def, ctx.ID())  # type: ignore[no-untyped-call]
            values: set[str] = SymbolTable._Listener._get_values(
                self._first_def,
                ctx.id_set(),  # type: ignore[no-untyped-call]
            )

            self._symbol_table._add_enum_type_decl(id, values)

        def exitConst_var_decl(self, ctx: StateParser.Const_var_declContext) -> None:
            get_id = SymbolTable._Listener._get_id_and_add_definition
            id: str = get_id(self._first_def, ctx.ID(0))
            type_: str = ctx.type_().getText()  # type: ignore[no-untyped-call]
            init: str = ctx.ID(1).getText()

            self._symbol_table._add_const_decl(id, type_, init)

        def exitVar_decl(self, ctx: StateParser.Var_declContext) -> None:
            get_id = SymbolTable._Listener._get_id_and_add_definition
            id: str = get_id(self._first_def, ctx.ID(0))
            type_: str = ctx.type_().getText()  # type: ignore[no-untyped-call]
            init_node: TerminalNode = ctx.ID(1)
            init: str = init_node.getText()

            definitions: dict[str, tuple[int, int]] = dict()
            values: set[str] = SymbolTable._Listener._get_values(
                definitions,
                ctx.id_set(),  # type: ignore[no-untyped-call]
            )

            if len(values) != 0 and init not in values:
                symbol: Token = init_node.getSymbol()
                error = StateInitNotInValues(init, symbol.line, symbol.column, values)
                raise Exception(error)

            self._symbol_table._add_var_decl(id, type_, init, values)

    def __init__(self) -> None:
        self._consts: dict[str, tuple[str, str]] = dict()
        self._enums: dict[str, set[str]] = dict()
        self._id2type: dict[str, str] = dict()
        self._vars: dict[str, tuple[str, str, set[str]]] = dict()

    def _add_enum_type_decl(self, id: str, values: set[str]) -> None:
        # requires
        assert id not in self._id2type and id not in self._enums
        for i in values:
            assert i not in self._id2type

        self._enums[id] = values
        self._id2type[id] = typechecking.ENUM

        for v in values:
            self._id2type[v] = id

    def _add_const_decl(self, id: str, type: str, init: str) -> None:
        # requires
        assert id not in self._id2type and id not in self._consts

        self._consts[id] = (type, init)
        self._id2type[id] = type

    def _add_var_decl(self, id: str, type: str, init: str, values: set[str]) -> None:
        # requires
        assert (
            id not in self._id2type
            and id not in self._vars
            and (len(values) == 0 or init in values)
        )

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
    def _get_type_init(symbol_table: "SymbolTable", init: str) -> Result[str, Error]:
        def get_type_literal(error: Error) -> Result[str, Error]:
            match error:
                case StateUnknownTypeError(id=id):
                    return typechecking.get_type_literal(id)
                case _:
                    return Failure(error)

        return symbol_table.get_type(init).lash(get_type_literal)

    @staticmethod
    def _type_check_assigns(
        symbol_table: "SymbolTable", ltype: str, values: Iterable[str]
    ) -> Result[tuple[()], Error]:
        get_type_init = partial(SymbolTable._get_type_init, symbol_table)
        get_type_assign = partial(typechecking.get_type_assign, ltype)
        for i in values:
            result: Result[str, Error] = flow(
                i, get_type_init, bind_result(get_type_assign)
            )
            if not_(is_successful)(result):
                return Failure(result.failure())
        return Success(())

    @staticmethod
    def _type_check_consts(symbol_table: "SymbolTable") -> Result["SymbolTable", Error]:
        type_check_assigns = partial(SymbolTable._type_check_assigns, symbol_table)
        for key in symbol_table._consts:
            type_, init = symbol_table._consts[key]
            result = type_check_assigns(type_, [init])
            if not_(is_successful)(result):
                return Failure(result.failure())
        return Success(symbol_table)

    @staticmethod
    def _type_check_vars(symbol_table: "SymbolTable") -> Result["SymbolTable", Error]:
        type_check_assigns = partial(SymbolTable._type_check_assigns, symbol_table)
        for key in symbol_table._vars:
            type_, init, values = symbol_table._vars[key]
            result = type_check_assigns(type_, {init}.union(values))
            if not_(is_successful)(result):
                return Failure(result.failure())
        return Success(symbol_table)

    @staticmethod
    def _type_check(symbol_table: "SymbolTable") -> Result["SymbolTable", Error]:
        result: Result["SymbolTable", Error] = flow(
            symbol_table,
            SymbolTable._type_check_consts,
            bind_result(SymbolTable._type_check_vars),
        )

        return result

    def get_type(self, id: str) -> Result[str, Error]:
        if id in self._id2type:
            return Success(self._id2type[id])
        return Failure(StateUnknownTypeError(id))

    def is_defined(self, id: str) -> bool:
        defined: bool = is_successful(self.get_type(id))
        return defined

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
