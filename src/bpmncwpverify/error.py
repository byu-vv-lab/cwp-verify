class Error:
    def __init__(self, msg: str) -> None:
        self.msg = msg


class StateSyntaxError(Error):
    def __init__(self, msg: str) -> None:
        super().__init__(msg)
