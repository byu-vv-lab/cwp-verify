from enum import Enum, auto
from antlr4 import CommonTokenStream, InputStream
from returns.result import safe
from returns.pipeline import flow
from returns.pointfree import bind_result

from bpmncwpverify.antlr.StateLexer import StateLexer
from bpmncwpverify.antlr.StateParser import StateParser


class Type(Enum):
    BOOL = auto()
    BYTE = auto()
    ENUM = auto()
    INT = auto()
    SHORT = auto()


class Declaration:
    bpmn: str
    cwp: str
    initial: str
    allowed_values: list[str]


class Constant:
    value: int


class Variable:
    value: int


@safe
def _get_parser(file_contents: str) -> StateParser:
    input_stream = InputStream(file_contents)
    lexer = StateLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = StateParser(stream)
    return parser


@safe
def _parse_file(parser: StateParser):
    try:
        x = parser.state()
        return x
    except Exception as err:
        print(err)
        raise err


@safe
def _get_symbol_table(context):
    print(context)
    return context


@safe
def get_symbol_table(file_contents: str):
    # input_stream = InputStream(file_contents)
    # lexer = StateLexer(input_stream)
    # stream = CommonTokenStream(lexer)
    # parser = StateParser(stream)
    parser: StateParser = _get_parser(str)

    tree = flow(parser, _parse_file, bind_result(_get_symbol_table))

    print(tree)
    # input_stream = InputStream(file_contents)
    # lexer = StateLexer(input_stream)
    # stream = CommonTokenStream(lexer)
    # parser = StateParser(stream)
    # tree = parser.state()
    return tree
