# TODO: create a "match" function on Failure(Error) and create standard error messaging.
import typing
import builtins


class Error:
    def __init__(self) -> None:
        pass


class BpmnNodeNotFound(Error):
    __slots__ = ["node_id"]

    def __init__(self, node_id: str):
        super().__init__()
        self.node_id = node_id


class NotImplementedError(Error):
    __slots__ = ["function"]

    def __init__(self, function: str) -> None:
        super().__init__()
        self.function = function


class MessageError(Error):
    __slots__ = ["msg"]

    def __init__(self, msg: str) -> None:
        super().__init__()
        self.msg = msg


class StateInitNotInValues(Error):
    __slots__ = ["id", "line", "column", "values"]

    def __init__(self, id: str, line: int, column: int, values: set[str]) -> None:
        super().__init__()
        self.id = id
        self.line = line
        self.column = column
        self.values = values

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, StateInitNotInValues):
            return (
                self.id == other.id
                and self.line == other.line
                and self.column == other.column
                and self.values == other.values
            )
        return False


class StateMultipleDefinitionError(Error):
    __slots__ = ("id", "line", "column", "prev_line", "prev_column")

    def __init__(
        self, id: str, line: int, column: int, prev_line: int, prev_column: int
    ) -> None:
        super().__init__()
        self.id = id
        self.line = line
        self.column = column
        self.prev_line = prev_line
        self.prev_column = prev_column

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, StateMultipleDefinitionError):
            return (
                self.id == other.id
                and self.line == other.line
                and self.column == other.column
                and self.prev_line == other.prev_line
                and self.prev_column == other.prev_column
            )
        return False


class StateSyntaxError(Error):
    __slots__ = "msg"

    def __init__(self, msg: str) -> None:
        self.msg = msg
        super().__init__()


class TypingAssignCompatabilityError(Error):
    __slots__ = ["ltype", "rtype"]

    def __init__(self, ltype: str, rtype: str) -> None:
        super().__init__()
        self.ltype = ltype
        self.rtype = rtype

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, TypingAssignCompatabilityError):
            return self.ltype == other.ltype and self.rtype == other.rtype
        return False


class TypingNoTypeError(Error):
    __slots__ = ["id"]

    def __init__(self, id: str) -> None:
        super().__init__()
        self.id = id

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, TypingNoTypeError):
            return self.id == other.id
        return False


def _get_exception_message(error: Exception) -> str:
    return "ERROR: {0} ({1})".format(type(error), error)


def _get_error_message(error: Error) -> str:
    match error:
        case BpmnNodeNotFound(node_id=node_id):
            return f"BPMN ERROR: node with id: {node_id} not found in graph."
        case NotImplementedError(function=function):
            return "ERROR: not implemented '{}'".format(function)
        case MessageError(msg=msg):
            return f"Message Error: {msg}"
        case StateInitNotInValues(id=id, line=line, column=column, values=values):
            # Convert to a list since Python sets are not stable
            return "STATE ERROR: init value '{}' at line {}:{} not in allowed values {}".format(
                id, line, column, sorted(values)
            )
        case StateMultipleDefinitionError(
            id=id,
            line=line,
            column=column,
            prev_line=prev_line,
            prev_column=prev_column,
        ):
            return "STATE ERROR: multiple definition of '{}' at line {}:{}, previously defined at line {}:{}".format(
                id, line, column, prev_line, prev_column
            )
        case StateSyntaxError(msg=msg):
            return "STATE SYNTAX ERROR: {}".format(msg)
        case TypingAssignCompatabilityError(ltype=ltype, rtype=rtype):
            return "TYPING ERROR: something of type '{}' cannot by assigned to something of type '{}'".format(
                rtype, ltype
            )
        case TypingNoTypeError(id=id):
            return "TYPING ERROR: literal '{}' has an unknown type".format(id)
        case _:
            raise builtins.NotImplementedError


def get_error_message(error: Error | Exception) -> str:
    match error:
        case Exception():
            return _get_exception_message(error)
        case Error():
            return _get_error_message(error)
