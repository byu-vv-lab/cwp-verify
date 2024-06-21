from antlr4.error.ErrorStrategy import ParseCancellationException
from pytest import raises, fail, fixture
from returns.pipeline import is_successful
from returns.result import Result
from returns.methods import unwrap_or_failure

from typing import Iterable

from bpmncwpverify.antlr.StateParser import StateParser
from bpmncwpverify.error import Error, StateSyntaxError
from bpmncwpverify.state import _get_parser, _parse_state


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
        error = unwrap_or_failure(result)
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
