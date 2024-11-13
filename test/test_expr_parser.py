# type: ignore

import pytest

from antlr4 import CommonTokenStream, InputStream

from bpmncwpverify.antlr.ExprLexer import ExprLexer
from bpmncwpverify.antlr.ExprParser import ExprParser

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
