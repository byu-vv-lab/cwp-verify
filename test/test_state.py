from antlr4.error.ErrorStrategy import ParseCancellationException
from pytest import raises, fail, fixture
from returns.pipeline import is_successful
from returns.result import Result, Success
from returns.functions import not_

from typing import Iterable

from bpmncwpverify.antlr.StateParser import StateParser
from bpmncwpverify.error import (
    Error,
    Errors,
    StateSyntaxError,
    StateMultipleDefinitionError,
)
from bpmncwpverify.state import _get_parser, _parse_state, SymbolTable


@fixture(scope="module")
def bad_input() -> Iterable[str]:
    yield "enum MyEnum {a b c d} const MYCONST : foo = 10 var myenum my : MyEnum = a {b c d}"


@fixture(scope="module")
def good_input() -> Iterable[str]:
    yield "enum MyEnum {a b c d} const MYCONST : foo = 10 var myenum : MyEnum = a {b c d}"


class Test_get_parser:
    def test_given_bad_input_when_parse_state_then_ParseCancelationException(
        self, bad_input
    ):
        # given
        parser_result = _get_parser(bad_input)
        assert is_successful(parser_result)
        parser = parser_result.unwrap()

        # when
        with raises(ParseCancellationException, match=r".* extraneous .*") as exception:
            _ = parser.state()

        # then
        assert exception.type is ParseCancellationException
        assert parser.getNumberOfSyntaxErrors() == 1
        assert (
            "line 1:58 extraneous input 'my' expecting ':'" == exception.value.args[0]
        )
        assert "line 1:58 extraneous input 'my' expecting ':'" in str(exception.value)

    def test_given_good_input_when_parse_state_then_tree_not_none(self, good_input):
        # given
        parser_result = _get_parser(good_input)
        assert is_successful(parser_result)
        parser = parser_result.unwrap()

        # when
        try:
            tree = parser.state()
        except Exception as exception:
            fail("ERROR: unexpected {}".format(exception))

        # then
        assert 0 == parser.getNumberOfSyntaxErrors()
        assert tree is not None


class Test_parse_state:
    @fixture(scope="class")
    def bad_parser(self, bad_input):
        result = _get_parser(bad_input)
        yield result

    @fixture(scope="class")
    def good_parser(self, good_input):
        result = _get_parser(good_input)
        yield result

    def test_given_bad_parser_when_parse_state_then_failure(
        self, bad_parser: Result[StateParser, Error]
    ):
        # given
        assert is_successful(bad_parser), "ERROR: unexpected {}".format(str(bad_parser))

        # when
        result = bad_parser.bind(_parse_state)

        # then
        assert not is_successful(result)
        error = result.failure()
        assert isinstance(error, StateSyntaxError)
        assert "line 1:58 extraneous input 'my' expecting ':'" == error.msg

    def test_given_good_parser_when_parse_state_then_success(
        self, good_parser: Result[StateParser, Error]
    ):
        # given
        assert is_successful(good_parser), "ERROR: unexpected {}".format(
            str(good_parser)
        )

        # when
        result = good_parser.bind_result(_parse_state)

        # then
        assert is_successful(result)


# TODO:
#   * Add tests for failed enum declarations
class Test_SymbolTable_build:
    def test_given_good_input_when_build_then_success(self, good_input: str):
        # given
        # good_input

        # when
        result = SymbolTable.build(good_input)

        # then
        assert is_successful(result)

    def test_given_bad_input_when_build_then_failure(self, bad_input: str):
        # given
        # bad_input

        # when
        result = SymbolTable.build(bad_input)

        # then
        assert not_(is_successful)(result)

    def test_given_good_input_when_build_then_declared_enum_have_types(
        self, good_input: str
    ):
        # given
        # good_input

        # when
        result = SymbolTable.build(good_input)

        # then
        assert is_successful(result)
        symbol_table = result.unwrap()
        expected_type = Success("MyEnum")
        assert expected_type == symbol_table.get_type("a")
        assert expected_type == symbol_table.get_type("b")
        assert expected_type == symbol_table.get_type("c")
        assert expected_type == symbol_table.get_type("d")

    @fixture(scope="class")
    def bad_multi_defined_enum_val(self) -> Iterable[str]:
        yield "enum E {e e} var i : E = a {a}"

    def test_given_bad_multi_defined_enum_val_when_build_then_Errors(
        self, bad_multi_defined_enum_val
    ):
        # given
        # multi_defined_enum

        # when
        result = SymbolTable.build(bad_multi_defined_enum_val)

        # then
        assert not_(is_successful)(result)
        errors: Error = result.failure()
        assert type(errors) is Errors
        assert len(errors.errors) == 1

        expected = StateMultipleDefinitionError("e", 1, 10, 1, 8)
        error: Error = errors.errors[0]
        assert expected == error

    @fixture(scope="class")
    def bad_multi_defined_enum_id(self) -> Iterable[str]:
        yield "enum E {e} enum E {f} var i : E = a {a}"

    def test_given_bad_multi_defined_enum_id_when_build_then_Errors(
        self, bad_multi_defined_enum_id
    ):
        # given
        # multi_defined_enum

        # when
        result = SymbolTable.build(bad_multi_defined_enum_id)

        # then
        assert not_(is_successful)(result)
        errors: Error = result.failure()
        assert type(errors) is Errors
        assert len(errors.errors) == 1

        expected = StateMultipleDefinitionError("E", 1, 16, 1, 5)
        error: Error = errors.errors[0]
        assert expected == error

    @fixture(scope="class")
    def bad_multi_defined_enum(self) -> Iterable[str]:
        yield "enum E {e f} enum E {e g} enum E {e h} var i : E = a {a}"

    def test_given_bad_multi_defined_enum_when_build_then_Errors(
        self, bad_multi_defined_enum
    ):
        # given
        # multi_defined_enum

        # when
        result = SymbolTable.build(bad_multi_defined_enum)

        # then
        assert not_(is_successful)(result)
        errors: Error = result.failure()
        assert type(errors) is Errors
        assert len(errors.errors) == 4

        expected: Error = StateMultipleDefinitionError("E", 1, 18, 1, 5)
        error: Error = errors.errors[0]
        assert expected == error

        expected = StateMultipleDefinitionError("e", 1, 21, 1, 8)
        error = errors.errors[1]
        assert expected == error

        expected = StateMultipleDefinitionError("E", 1, 31, 1, 5)
        error = errors.errors[2]
        assert expected == error

        expected = StateMultipleDefinitionError("e", 1, 34, 1, 8)
        error = errors.errors[3]
        assert expected == error
