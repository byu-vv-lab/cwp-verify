from antlr4 import CommonTokenStream, InputStream
from antlr4.error.ErrorStrategy import ParseCancellationException
from antlr4.error.ErrorListener import ConsoleErrorListener, ErrorListener

from returns.result import safe, Failure, Result, Success
# from returns.pipeline import flow
# from returns.pointfree import bind_result

from bpmncwpverify.antlr.StateLexer import StateLexer
from bpmncwpverify.antlr.StateParser import StateParser
from bpmncwpverify.error import Error, StateSyntaxError


# class Type(Enum):
#     BOOL = auto()
#     BYTE = auto()
#     ENUM = auto()
#     INT = auto()
#     SHORT = auto()


# class Declaration:
#     bpmn: str
#     cwp: str
#     initial: str
#     allowed_values: list[str]


# class Constant:
#     value: int


# class Variable:
#     value: int


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
