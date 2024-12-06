# TODO: create a "match" function on Failure(Error) and create standard error messaging.
import typing
import builtins


class Error:
    def __init__(self) -> None:
        pass


class BpmnNodeNotFound(Error):
    __slots__ = ["node_id"]

    def __init__(self, node_id: str) -> None:
        super().__init__()
        self.node_id = node_id


class BpmnStructureError(Error):
    __slots__ = ["node_id", "error_msg"]

    def __init__(self, node_id: str, error_msg: str) -> None:
        super().__init__()
        self.node_id = node_id
        self.error_msg = error_msg


class ExpressionComputationCompatabilityError(Error):
    __slots__ = ["ltype", "rtype"]

    def __init__(self, ltype: str, rtype: str) -> None:
        super().__init__()
        self.ltype = ltype
        self.rtype = rtype

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, ExpressionComputationCompatabilityError):
            return self.ltype == other.ltype and self.rtype == other.rtype
        return False


class ExpressionNegatorError(Error):
    __slots__ = ["_type"]

    def __init__(self, type: str) -> None:
        super().__init__()
        self._type = type

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, ExpressionNegatorError):
            return self._type == other._type
        return False


class ExpressionRelationCompatabilityError(Error):
    __slots__ = ["ltype", "rtype"]

    def __init__(self, ltype: str, rtype: str) -> None:
        super().__init__()
        self.ltype = ltype
        self.rtype = rtype

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, ExpressionComputationCompatabilityError):
            return self.ltype == other.ltype and self.rtype == other.rtype
        return False


class ExpressionRelationalNotError(Error):
    __slots__ = ["_type"]

    def __init__(self, type: str) -> None:
        super().__init__()
        self._type = type

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, ExpressionRelationalNotError):
            return self._type == other._type
        return False


class ExpressionUnrecognizedID(Error):
    __slots__ = ["_id"]

    def __init__(self, id: str) -> None:
        super().__init__()
        self._id = id

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, ExpressionUnrecognizedID):
            return self._id == other._id
        return False


class NotImplementedError(Error):
    __slots__ = ["function"]

    def __init__(self, function: str) -> None:
        super().__init__()
        self.function = function


class MessageError(Error):
    __slots__ = ["node_id", "error_msg"]

    def __init__(self, node_id: str, error_msg: str) -> None:
        super().__init__()
        self.node_id = node_id
        self.error_msg = error_msg


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
        case BpmnStructureError(node_id=node_id, error_msg=error_msg):
            return f"BPMN ERROR at node: {node_id}. {error_msg}"
        case ExpressionComputationCompatabilityError(ltype=ltype, rtype=rtype):
            return "EXPR ERROR: sometion of type '{}' cannot be computed with something of type '{}'".format(
                rtype, ltype
            )
        case ExpressionNegatorError(_type=_type):
            return "EXPR ERROR: sometiong of type '{}' cannot be used with a mathmatical negator".format(
                _type
            )
        case ExpressionRelationCompatabilityError(ltype=ltype, rtype=rtype):
            return "EXPR ERROR: sometion of type '{}' cannot be related with something of type '{}'".format(
                rtype, ltype
            )
        case ExpressionRelationalNotError(_type=_type):
            return "EXPR ERROR: sometiong of type '{}' cannot be used with a relational not".format(
                _type
            )
        case ExpressionUnrecognizedID(_id=_id):
            return "EXPR ERROR: '{}' is not recognized as a literal or something stored in the symbol table".format(
                _id
            )
        case NotImplementedError(function=function):
            return "ERROR: not implemented '{}'".format(function)
        case MessageError(node_id=node_id, error_msg=error_msg):
            return f"Inter-process message error at node: {node_id}. {error_msg}"
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
