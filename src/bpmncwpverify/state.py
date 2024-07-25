from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker
from antlr4.error.ErrorStrategy import ParseCancellationException
from antlr4.error.ErrorListener import ConsoleErrorListener, ErrorListener
from antlr4.tree.Tree import TerminalNode
from antlr4.Token import Token

from returns.result import Failure, Result, Success
from returns.pipeline import flow, is_successful
from returns.pointfree import bind_result

from typing import Tuple

from bpmncwpverify.antlr.StateLexer import StateLexer
from bpmncwpverify.antlr.StateParser import StateParser
from bpmncwpverify.antlr.StateListener import StateListener

from bpmncwpverify.error import (
    Error,
    # Errors,
    StateMultipleDefinitionError,
    StateSyntaxError,
    StateUnknownTypeError,
)

from bpmncwpverify import typechecking

# TODO:
#   * ~Use the __slot__ attribute~
#   * ~Figure out class member variable declaration~
#   * Get rid of magic numbers
#   * ~Group by private and public (rename the nested class and mark all methods private where possible)~
#   * ~Track where the symbol was previously defined and include that information in the Error class (add map in Symbol table to track where things are defined)
#   * ~Rework 'is_defined' to use 'get_type' with 'is_successul'~
#   * ~Rename things to be more sensible (StateDefinedError etc.)~
#   * ~Test __slot__ attribute for errors when using undefined slots~
#   * ~Create methods for the multiple definition checks etc. (make it more modular)~


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
    __slots__ = ["_consts", "_enums", "_id2type"]

    class _Listener(StateListener):
        __slots__ = ["_errors", "_first_def", "_symbol_table"]

        def __init__(self) -> None:
            super().__init__()
            self._errors: list[Error] = []
            self._first_def: dict[str, Tuple[int, int]] = dict()
            self._symbol_table: "SymbolTable" = SymbolTable()

        def _add_definition(self, id: str, line: int, column: int) -> None:
            if id in self._first_def:
                prev_line = self._first_def[id][0]
                prev_column = self._first_def[id][1]
                error = StateMultipleDefinitionError(
                    id, line, column, prev_line, prev_column
                )
                raise Exception(error)
                # self._errors.append(
                #     StateMultipleDefinitionError(
                #         id, line, column, prev_line, prev_column
                #     )
                # )
            else:
                self._first_def[id] = (line, column)

        def _get_id_and_add_definition(self, id_node: TerminalNode) -> str:
            id: str = id_node.getText()
            symbol: Token = id_node.getSymbol()
            self._add_definition(id, symbol.line, symbol.column)
            return id

        def exitEnum_type_decl(self, ctx: StateParser.Enum_type_declContext):
            id: str = self._get_id_and_add_definition(ctx.ID())
            values: set[str] = {
                self._get_id_and_add_definition(i) for i in ctx.id_set().getChildren()
            }
            self._symbol_table._add_enum_type_decl(id, values)

        def exitConst_var_decl(self, ctx: StateParser.Const_var_declContext):
            pass

    def __init__(self) -> None:
        self._consts: dict[str, Tuple[str, str]] = dict()
        self._enums: dict[str, set[str]] = dict()
        self._id2type: dict[str, str] = dict()

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

    def _build(self, context: StateParser.StateContext) -> Result["SymbolTable", Error]:
        listener = SymbolTable._Listener()
        try:
            ParseTreeWalker.DEFAULT.walk(listener, context)
            return Success(listener._symbol_table)
        except Exception as exception:
            # requires
            assert len(exception.args) == 1
            error: Error = exception.args[0]
            return Failure(error)
        # if len(listener._errors) == 0:
        #     return Success(listener._symbol_table)
        # return Failure(Errors(listener._errors))

    def get_type(self, id: str) -> Result[str, Error]:
        if id in self._id2type:
            return Success(self._id2type[id])
        return Failure(StateUnknownTypeError(id))

    def is_defined(self, id) -> bool:
        return is_successful(self.get_type(id))

    @staticmethod
    def build(state_def: str) -> Result["SymbolTable", Error]:
        symbol_table = SymbolTable()

        result: Result["SymbolTable", Error] = flow(
            state_def,
            _get_parser,
            bind_result(_parse_state),
            bind_result(symbol_table._build),
            # Add type-check...
        )
        return result
