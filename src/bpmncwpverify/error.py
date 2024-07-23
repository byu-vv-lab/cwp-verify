# TODO: create a "match" function on Failure(Error) and create standard error messaging.


class Error:
    __slots__ = ()

    def __init__(self) -> None:
        pass


class NotImplementedError(Error):
    def __init__(self) -> None:
        super().__init__()


class Errors(Error):
    _slots__ = "errors"

    def __init__(self, errors: list[Error]) -> None:
        super().__init__()
        self.errors = errors


class StateAssignmentCompatibleError(Error):
    __slots__ = ("ltype", "rtype")

    def __init__(self, ltype: str, rtype) -> None:
        super().__init__()
        self.ltype = ltype
        self.rtype = rtype


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

    def __eq__(self, other) -> bool:
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
    __slots__ = ("type", "init")

    def __init__(self, type: str, init: str) -> None:
        super().__init__()
        self.type = type
        self.init = init

    def __eq__(self, other) -> bool:
        if isinstance(other, TypingAssignCompatabilityError):
            return self.type == other.type and self.init == other.init
        return False


class TypingNoTypeError(Error):
    __slots__ = "literal"

    def __init__(self, literal: str) -> None:
        super().__init__()
        self.literal = literal

    def __eq__(self, other) -> bool:
        if isinstance(other, TypingNoTypeError):
            return self.literal == other.literal
        return False
