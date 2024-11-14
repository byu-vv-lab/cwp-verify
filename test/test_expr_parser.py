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
    def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
        raise SyntaxError(f"Syntax error at line {line}:{column} - {msg}")


def parse_input(expression: str):
    input_stream = InputStream(expression)
    lexer = ExprLexer(input_stream)
    stream = CommonTokenStream(lexer)
    parser = ExprParser(stream)

    parser.removeErrorListeners()
    parser.addErrorListener(ThrowingErrorListener())

    return parser.start()


@pytest.mark.parametrize(
    "input_text",
    [
        "a",
        "(a)",
        "a + b",
        "a * b",
        "-a",
        # Unary and Binary Operations
        "-a + b",
        "a + b * c",
        "a * b + c",
        "(a + b) * c",
        "-a * -b",
        # Logical and Relational Operations
        "a < b",
        "a <= b",
        "a == b",
        "a > b",
        "a >= b",
        "!a",
        "!(a && b)",
        "a && b",
        "a || b",
        "a && b || c",
        "(a || b) && c",
        "a < b && c > d",
        "a + b == c - d",
        "(a < b) && (c >= d)",
        # Complex Nested Expressions
        "a * (b + c) / d",
        "a + b * (c - d) / e",
        "-a + (b * c) / (-d + e)",
        "a && (b || !c)",
        "!(a < b) && (c > d)",
        "a < b + c * d",
        "(a + b) <= (c - d * e)",
        "!(a == b) || (c != d)",
        "a + b * c == d / e - f",
        "!a || !b && !c",
        "a < b || (c >= d && e < f)",
        # Complex Combinations
        "((a + b) * c < d) && e",
        "(a / b) * (c + d) - e",
        "a && b || c && d",
        "(a < b || c > d) && (e >= f || g <= h)",
        "(a < b || c > d) && e >= f || g <= h",
        "((a < b || c > d) && e >= f || g <= h) > (a - b - (c - d - g * h))",
        "a + (b * (c - d / e)) >= f",
        "((a && b) || !c) && d",
        # Edge Cases with Nested Parentheses and Unary Operators
        "((((a))))",
        "-(a + b * c)",
        "!(!(a && b))",
        "((((a + b)) * (c - d)))",
        "a * -(b + c)",
        "!((a + b) * (c - d) / e)",
        "((a && b) || (c && d))",
        "!(!(!a))",
        "((a || b) && (!c || d))",
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
        "a +",
        "&& b",
        "a ||",
        "(a + b",
        "a + (b * c",
        "a b + c",
        "a * * b",
        "!",
        "a < < b",
        "(a && b))",
        "a + (b * (c - d)",
        "((a + b) * c < d && e",
        "a * (b + c))",
        "a || (b && c",
        "a && b ||",
        "(a || b &&",
        "(a + b))",
        "a && (b || c",
        "((a + b)",
        "a && || b",
        "a || && b",
        "a + * b",
        "a < > b",
        "a * + b",
        "a / && b",
        "a || b +",
        "! && a",
        "+",
        "*",
        "&&",
        "||",
        "(",
        ")",
        "!((a && b) ||)",
        "((a || b) && c ||)",
        "((a && b) || (c < d &&))",
        "((a || (b * c))) || + d",
        "(a || b)) * c",
    ],
)
def test_invalid_inputs(input_text):
    with pytest.raises(SyntaxError):
        parse_input(input_text)


@pytest.mark.parametrize(
    "state, expression, expression_type",
    [
        ("var a: bit = 1 var b: bit = 0", "a != b", "bool"),
        ("const x: int = 0 var y: short = 1 var z: short = 0", "x + y - z", "int"),
        ("var a: int = 10 var b: byte = 5", "a > b", "bool"),
        ("const x: bool = true var y: bool = false", "!x || y", "bool"),
        (
            "var m: int = 20 var n: short = 10 var o: bool = true",
            "(m >= n) && !o",
            "bool",
        ),
        (
            "var p: int = 15 var q: short = 3 var r: byte = 2",
            "(p + q) * r == p",
            "bool",
        ),
        ("var a: byte = 1 var b: bit = 0", "(a != b) || (a > b)", "bool"),
        (
            "const x: int = 4 var y: short = 2 var z: byte = 1",
            "x * (y + z) < x",
            "bool",
        ),
        ("var i: int = 0 var j: short = 1 var k: bit = 0", "(i + j) > k", "bool"),
        ("var a: int = 5 var b: short = 3 var c: bool = true", "(a > b) && !c", "bool"),
    ],
)
def test_given_good_state_when_build_then_success(state, expression, expression_type):
    sym_table_result = SymbolTable.build(state)

    assert is_successful(sym_table_result)
    symbol_table: SymbolTable = sym_table_result.unwrap()

    expr_checker_result = ExpressionListener.build(expression, symbol_table)

    assert is_successful(expr_checker_result)

    assert expr_checker_result.unwrap() == expression_type


@pytest.mark.parametrize(
    "state, expression",
    [
        ("const a: bit = 0 var b: short = 1", "b + c"),
        ("const x: int = 0 var y: short = 1 var z: bit = 0", "x + y - z"),
        ("const a: bit = 0 var b: short = 1 var c: int = 1", "a + (b * c)"),
        ("const a: short = 0 var b: short = 1 var c: short = 1", "a + (b > c)"),
        ("var a: bit = 0", "!a"),
        ("var a: bool = false var b: bit = 0", "a + b"),
    ],
)
def test_given_bad_state_when_build_then_failure(state, expression):
    sym_table_result = SymbolTable.build(state)

    assert is_successful(sym_table_result)
    symbol_table: SymbolTable = sym_table_result.unwrap()

    expr_checker_result = ExpressionListener.build(expression, symbol_table)

    assert not is_successful(expr_checker_result)
