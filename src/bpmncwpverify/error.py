class Error:
    def __init__(self, msg: str):
        self.msg = msg


class StateSyntaxError(Error):
    def __init__(self, msg: str):
        super().__init__(msg)
