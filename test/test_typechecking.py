from returns.result import Failure, Success

from bpmncwpverify.error import TypingNoTypeError, TypingAssignCompatabilityError

from bpmncwpverify.typechecking import BIT, BOOL, get_type_assign, get_type_literal


# TODO
# * Convert the tests to use a yielding fixture for the inputs (or a parameterized fixture)
class Test_get_type_assign:
    def test_given_good_assign_bit_then_success(self):
        # givin
        type = BIT

        # when
        result = get_type_assign(type, type)

        # then
        expected = Success(type)
        assert expected == result

    def test_given_bad_assign_bit_then_failure(self):
        # givin
        type = BIT

        # when
        result = get_type_assign(type, "a")

        # then
        expected = Failure(TypingAssignCompatabilityError(type, "a"))
        assert expected == result

    def test_given_good_assign_bool_then_success(self):
        # givin
        type = BOOL

        # when
        result = get_type_assign(type, type)

        # then
        expected = Success(type)
        assert expected == result

    def test_given_bad_assign_bool_then_failure(self):
        # givin
        type = BOOL

        # when
        result = get_type_assign(type, "a")

        # then
        expected = Failure(TypingAssignCompatabilityError(type, "a"))
        assert expected == result


class Test_get_type_literal:
    def test_given_good_literal_bit_then_success(self):
        # givin
        literal = "1"

        # when
        result = get_type_literal(literal)

        # then
        expected = Success(BIT)
        assert expected == result

    def test_given_bad_literal_bit_then_failure(self):
        # givin
        literal = "a"

        # when
        result = get_type_literal(literal)

        # then
        expected = Failure(TypingNoTypeError("a"))
        assert expected == result

    def test_given_good_literal_bool_then_success(self):
        # givin
        literal = "false"

        # when
        result = get_type_literal(literal)

        # then
        expected = Success(BOOL)
        assert expected == result

    def test_given_bad_literal_bool_then_failure(self):
        # givin
        literal = "a"

        # when
        result = get_type_literal(literal)

        # then
        expected = Failure(TypingNoTypeError("a"))
        assert expected == result

    def test_given_good_literal_byte_then_success(self):
        pass
