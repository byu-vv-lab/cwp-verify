from antlr4 import CommonTokenStream, InputStream
from antlr4.error.ErrorStrategy import ParseCancellationException
from antlr4.error.ErrorListener import ConsoleErrorListener, ErrorListener

from pytest import raises
from bpmncwpverify.antlr import StateLexer, StateParser
from io import StringIO


class ThrowingErrorListener(ErrorListener):
    def __init__(self):
        super().__init__()

    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        msg = "line {}:{} {}".format(line, column, msg)
        raise ParseCancellationException(msg)


def test_given_syntax_error_when_parse_state_then_ParseCancelationException():
    # given
    input = "enum MyEnum {a b c d} const MYCONST : foo = 10 var myenum my : MyEnum = a {b c d}"
    input_stream = InputStream(input)
    lexer = StateLexer.StateLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = StateParser.StateParser(stream)
    parser.removeErrorListener(ConsoleErrorListener.INSTANCE)
    parser.addErrorListener(ThrowingErrorListener())

    # when
    with raises(ParseCancellationException) as exception:
        _ = parser.state()

    # then
    assert parser.getNumberOfSyntaxErrors() == 1
    assert "line 1:58 extraneous input 'my' expecting ':'" == exception.value.args[0]


def test_given_good_input_when_parse_state_then_tree_not_none():
    # given
    input = (
        "enum MyEnum {a b c d} const MYCONST : foo = 10 var myenum: MyEnum = a {b c d}"
    )
    input_stream = InputStream(input)
    lexer = StateLexer.StateLexer(input_stream)
    stream = CommonTokenStream(lexer)
    msg = ""
    parser = StateParser.StateParser(stream, StringIO(msg))

    # when
    tree = parser.state()

    # then
    assert 0 == parser.getNumberOfSyntaxErrors()
    assert tree is not None
