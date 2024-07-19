from antlr4 import CommonTokenStream, InputStream, ParseTreeWalker
from antlr4.error.ErrorStrategy import ParseCancellationException
from antlr4.error.ErrorListener import ConsoleErrorListener, ErrorListener
from antlr4.tree.Tree import TerminalNode
from antlr4.Token import Token

from returns.result import safe, Failure, Result, Success
from returns.pipeline import flow
from returns.pointfree import bind_result

from typing import Final

from bpmncwpverify.antlr.StateLexer import StateLexer
from bpmncwpverify.antlr.StateParser import StateParser
from bpmncwpverify.antlr.StateListener import StateListener

from bpmncwpverify.error import (
    Error,
    StateSyntaxError,
    StateNoTypeError,
    StateDefinedError,
)

# TODO:
#   * Use the __slot__ attribute
#   * Figure out class member variable declaration
#   * Get rid of magic numbers
#   * Group by private and public (rename the nested class and mark all methods private where possible)
#   * Track where the symbol was previously defined and include that information in the Error class
#   * Rename things to be more sensible (StateDefinedError etc.)


class SymbolTable:
    PRIMITIVES: Final[set[str]] = {
        "BIT",
        "BOOL",
        "BYTE",
        "ENUM",
        "INT",
        "SHORT",
    }

    # maps the enum ID to the values for the enum
    enums: dict[str, set[str]]

    # consts: dict[str, (str, str)]
    # vars: dict[str, (str, set[str])]

    # maps an ID to a type
    id2type: dict[str, str]

    class _Listener(StateListener):
        #  __slots__ = ('source', 'type', 'channel', 'start', 'stop', 'tokenIndex', 'line', 'column', '_text')
        errors: list[Error]
        symbol_table: "SymbolTable"

        def __init__(self) -> None:
            super().__init__()
            self.errors = []
            self.symbol_table = SymbolTable()

        def _add_error(self, error: Error) -> None:
            self.error.append(error)

        def exitEnum_type_decl(self, ctx: StateParser.Enum_type_declContext):
            id_ctx: TerminalNode = ctx.ID()
            id: str = id_ctx.getText()
            if self.symbol_table.is_defined(id):
                symbol: Token = id_ctx.getSymbol()
                self._add_error(StateDefinedError(id, symbol.line, symbol.column))

            values: set[str] = set()
            for i in ctx.id_set().getChildren():
                value = i.getText()
                if value in values:
                    value_symbol: Token = i.getSymbol()
                    self._add_error(
                        StateDefinedError(id, value_symbol.line, value_symbol.column)
                    )
                values.add(value)

            self.symbol_table._add_enum_type_decl(id, values)

    def __init__(self) -> None:
        self.enums = dict()
        self.id2type = dict()

    def is_defined(self, id) -> bool:
        return (id in self.enums) or (id in self.id2type)

    def _add_enum_type_decl(self, id: str, values: set[str]) -> None:
        self.enums[id] = values
        self.id2type[id] = "ENUM"

        for v in values:
            self.id2type[v] = id

    def _build(self, context: StateParser.StateContext) -> Result["SymbolTable", Error]:
        listener = SymbolTable._Listener()
        ParseTreeWalker.DEFAULT.walk(listener, context)
        if len(listener.errors) == 0:
            return Success(listener.symbol_table)
        return Failure(Error("TODO: implemenent Errors message"))

    def get_type(self, id: str) -> Result[str, Error]:
        if id in self.id2type:
            return Success(self.id2type[id])
        return Failure(StateNoTypeError(id))

    @staticmethod
    def build(state_def: str) -> Result["SymbolTable", Error]:
        symbol_table = SymbolTable()

        result: Result["SymbolTable", Error] = flow(
            state_def,
            _get_parser,
            bind_result(_parse_state),
            bind_result(symbol_table._build),
        )
        return result


# class Type(Enum):
#     BIT = auto()
#     BOOL = auto()
#     BYTE = auto()
#     ENUM = auto()
#     INT = auto()
#     SHORT = auto()


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


@safe
def _get_symbol_table(context):
    print(context)
    return context


@safe
def get_symbol_table(file_contents: str):
    pass
    # input_stream = InputStream(file_contents)
    # lexer = StateLexer(input_stream)
    # stream = CommonTokenStream(lexer)
    # parser = StateParser(stream)
    # parser: StateParser = _get_parser(str)

    # tree = flow(parser, _parse_state, bind_result(_get_symbol_table))

    # print(tree)
    # # input_stream = InputStream(file_contents)
    # lexer = StateLexer(input_stream)
    # stream = CommonTokenStream(lexer)
    # parser = StateParser(stream)
    # tree = parser.state()
    # return tree
