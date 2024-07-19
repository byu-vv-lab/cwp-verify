# TODO: create a "match" function on Failure(Error) and create standard error messaging.


class Error:
    def __init__(self, msg: str) -> None:
        self.msg = msg


class StateSyntaxError(Error):
    def __init__(self, msg: str) -> None:
        super().__init__(msg)


class StateNoTypeError(Error):
    def __init__(self, id: str) -> None:
        msg: str = str.format("ERROR: {} has no type", id)
        super().__init__(msg)


class StateDefinedError(Error):
    def __init__(self, id: str, line: int, column: int) -> None:
        msg: str = str.format("ERROR: {} at line {}:{} previously", id, line, column)
        super().__init__(msg)
