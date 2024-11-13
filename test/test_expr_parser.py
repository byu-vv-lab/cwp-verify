from bpmncwpverify.expr import ExpressionListener
import pytest
from bpmncwpverify.antlr.ExprLexer import ExprLexer
from bpmncwpverify.antlr.ExprParser import ExprParser

from antlr4.error.ErrorListener import ErrorListener
from returns.pipeline import is_successful

from bpmncwpverify.state import SymbolTable

from antlr4 import CommonTokenStream, InputStream


from typing import Iterable


@pytest.fixture(scope="module")
def parenthesis_input() -> Iterable[str]:
    yield "(1 + 1)"


@pytest.fixture(scope="module")
def id_input() -> Iterable[str]:
    yield "a"


@pytest.fixture(scope="module")
def negator_input() -> Iterable[str]:
    yield "-1"


@pytest.fixture(scope="module")
def mult_input() -> Iterable[str]:
    yield "1 * 1"


@pytest.fixture(scope="module")
def div_input() -> Iterable[str]:
    yield "1/1"


@pytest.fixture(scope="module")
def addition_input() -> Iterable[str]:
    yield "1 + 1"


@pytest.fixture(scope="module")
def subtraction_input() -> Iterable[str]:
    yield "1 - 1"


@pytest.fixture(scope="module")
def rel_input() -> Iterable[str]:
    yield "1 == 1"


@pytest.fixture(scope="module")
def not_input() -> Iterable[str]:
    yield "!1"


@pytest.fixture(scope="module")
def and_input() -> Iterable[str]:
    yield "1 && 1"


@pytest.fixture(scope="module")
def or_input() -> Iterable[str]:
    yield "1 || 1"


def test_parenthesis_input_test(parenthesis_input):
    input_stream = InputStream(parenthesis_input)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    id = parser.atom()
    assert id is not None


def test_id_input_test(id_input):
    input_stream = InputStream(id_input)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    id = parser.atom()
    assert id is not None


def test_negator_input_test(negator_input):
    input_stream = InputStream(negator_input)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    # tree = parser.start()
    # print("Parse Tree Structure:", tree.toStringTree(recog=parser))
    id = parser.unaryExpr()
    assert id is not None


def test_mult_input_test(mult_input):
    input_stream = InputStream(mult_input)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    id = parser.mulDivExpr()
    assert id is not None


def test_div_input_test(div_input):
    input_stream = InputStream(div_input)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    id = parser.mulDivExpr()
    assert id is not None


def test_add_input_test(addition_input):
    input_stream = InputStream(addition_input)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    id = parser.addSubExpr()
    assert id is not None


def test_subtract_input_test(subtraction_input):
    input_stream = InputStream(subtraction_input)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    id = parser.addSubExpr()
    assert id is not None


def test_rel_input_test(rel_input):
    input_stream = InputStream(rel_input)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    id = parser.relExpr()
    assert id is not None


def test_not_input_test(not_input):
    input_stream = InputStream(not_input)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    id = parser.notExpr()
    assert id is not None


def test_and_input_test(and_input):
    input_stream = InputStream(and_input)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    id = parser.andExpr()
    assert id is not None


def test_or_input_test(or_input):
    input_stream = InputStream(or_input)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)
    id = parser.orExpr()
    assert id is not None


class ThrowingErrorListener(ErrorListener):
    def __init__(self):
        super(ThrowingErrorListener, self).__init__()

    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        raise SyntaxError(f"line {line}:{column} {msg}")


def parse_input(input_text):
    input_stream = InputStream(input_text)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)

    parser.removeErrorListeners()
    lexer.removeErrorListeners()

    error_listener = ThrowingErrorListener()
    parser.addErrorListener(error_listener)
    lexer.addErrorListener(error_listener)

    tree = parser.expr()
    return tree


@pytest.mark.parametrize(
    "input_text",
    [
        "(x + y) != (z + t)",
        "!((a - b) == (c * d))",
        "(x > y) && (y < z)",
        "(p >= q) || (r <= s)",
        "a > b && b < c",
        "a && b < c",
        "!((x + (y * z)) == ((a / b) - c))",
        "(((x)) + ((y))) > ((z))",
        "((a + b) > c) && ((d - e) <= f) || !(g == h)",
        "(x1 + y3d) == (y2 - yy_2)",
        "(a * b + c / d - e) != (f + g)",
    ],
)
def test_valid_inputs(input_text):
    try:
        parse_input(input_text)
        assert True
    except SyntaxError as e:
        pytest.fail(f"Valid input raised SyntaxError: {e}")


@pytest.mark.parametrize(
    "input_text",
    [
        "(x y)",
        "((a + b) > c",
        "(a + b) > c$",
        "(a ++ b) == c",
        "(a + b c) == c",
        "",
        "(a +- 1.2.3) == b",
        "( +- 1.2.3) == b",
    ],
)
def test_invalid_inputs(input_text):
    with pytest.raises(SyntaxError):
        parse_input(input_text)


@pytest.mark.parametrize(
    "state, expression",
    [
        ("const a: bit = 0 var i : bit = 0 {0 1}", "a != i"),
        ("const x: int = 0 var y : int = 0 {0 1} var z : int = 0", "(x > y) + (y < z)"),
        # ("var a: short = 0 var b: short = 3 var c: int = 4 var d: int = 5 var e: int = 6 var f: int = 7 var g: int = 8 var h: int = 9, "((a + b) > c) && ((d - e) <= f) || !(g == h)"),
    ],
)
def test_given_good_state_when_build_then_success(state, expression):
    sym_table_result = SymbolTable.build(state)

    assert is_successful(sym_table_result)
    symbol_table: SymbolTable = sym_table_result.unwrap()

    expr_checker_result = ExpressionListener.build(expression, symbol_table)

    assert is_successful(expr_checker_result)
