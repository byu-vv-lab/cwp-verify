# type: ignore
import pytest

from bpmncwpverify.core.error import (
    Error,
    NotImplementedError,
    StateInitNotInValues,
    StateMultipleDefinitionError,
    StateSyntaxError,
    TypingAssignCompatabilityError,
    TypingNoTypeError,
    get_error_message,
)

test_inputs: list[tuple[Error, str]] = [
    (NotImplementedError("notImplemented"), "ERROR: not implemented 'notImplemented'"),
    (
        StateInitNotInValues("a", 0, 1, {"b", "c"}),
        "STATE ERROR: init value 'a' at line 0:1 not in allowed values ['b', 'c']",
    ),
    (
        StateMultipleDefinitionError("a", 42, 43, 0, 1),
        "STATE ERROR: multiple definition of 'a' at line 42:43, previously defined at line 0:1",
    ),
    (StateSyntaxError("bad syntax"), "STATE SYNTAX ERROR: bad syntax"),
    (
        TypingAssignCompatabilityError("enum", "int"),
        "TYPING ERROR: something of type 'int' cannot by assigned to something of type 'enum'",
    ),
    (TypingNoTypeError("a"), "TYPING ERROR: literal 'a' has an unknown type"),
]
test_ids: list[str] = [
    "NotImplementedError",
    "StateInitNotInValues",
    "StateMultipleDefinitionError",
    "StateSyntaxError",
    "TypeingAssignCompatabilityError",
    "TypingNoTypeError",
]


@pytest.mark.parametrize(
    scope="function",
    argnames=["error", "expected"],
    argvalues=test_inputs,
    ids=test_ids,
)
def test_given_error_when_get_error_message_then_message_equals_expected(
    error: Error, expected: str
):
    # given
    # error

    # when
    result = get_error_message(error)

    # then
    assert expected == result
