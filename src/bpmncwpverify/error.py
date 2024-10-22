# TODO: create a "match" function on Failure(Error) and create standard error messaging.
import typing


class Error:
    __slots__ = ()

    def __init__(self) -> None:
        pass


class ExpressionSyntaxError(Error):
    __slots__ = "msg"

    def __init__(self, msg: str) -> None:
        self.msg = msg
        super().__init__()


class ExpressionUnknownVariableError(Error):
    __slots__ = "id"

    def __init__(self, id: str) -> None:
        super().__init__()
        self.id = id


class ExpressionVariableCompatabilityError(Error):
    __slots__ = ("ltype", "rtype")

    def __init__(self, ltype: str, rtype: str) -> None:
        super().__init__()
        self.ltype = ltype
        self.rtype = rtype

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, ExpressionVariableCompatabilityError):
            return self.ltype == other.ltype and self.rtype == other.rtype
        return False


class NotImplementedError(Error):
    def __init__(self) -> None:
        super().__init__()


class StateInitNotInValues(Error):
    __slots__ = ("id", "line", "column", "values")

    def __init__(self, id: str, line: int, column: int, values: set[str]) -> None:
        super().__init__()
        self.id = (id,)
        self.line = (line,)
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

        # msg: str = str.format("ERROR: {} at line {}:{} previously", id, line, column)

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


class StateUnknownTypeError(Error):
    __slots__ = "id"

    def __init__(self, id: str) -> None:
        super().__init__()
        self.id = id


class TypingAssignCompatabilityError(Error):
    __slots__ = ("ltype", "rtype")

    def __init__(self, ltype: str, rtype: str) -> None:
        super().__init__()
        self.ltype = ltype
        self.rtype = rtype

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, TypingAssignCompatabilityError):
            return self.ltype == other.ltype and self.rtype == other.rtype
        return False


class TypingNoTypeError(Error):
    __slots__ = "id"

    def __init__(self, literal: str) -> None:
        super().__init__()
        self.id = id

    def __eq__(self, other: typing.Any) -> bool:
        if isinstance(other, TypingNoTypeError):
            return self.id == other.id
        return False
