from returns.result import Failure, Result, Success
from typing import Final

from bpmncwpverify.error import (
    TypingAssignCompatabilityError,
    TypingNoTypeError,
)

# from bpmncwpverify.typing import BIT

BIT: Final[str] = "bit"
BOOL: Final[str] = "bool"
BYTE: Final[str] = "byte"
ENUM: Final[str] = "enum"
SHORT: Final[str] = "short"
INT: Final[str] = "int"

BYTEMIN: Final[int] = 0
BYTEMAX: Final[int] = 255
SHORTMIN: Final[int] = -32768
SHORTMAX: Final[int] = 32767
INTMIN: Final[int] = -2147483648
INTMAX: Final[int] = 2147483647


def get_type_assign(ltype: str, rtype: str) -> Result[str, TypingNoTypeError]:
    if ltype == rtype:
        return Success(ltype)
    if ltype == BYTE and (rtype == BIT):
        return Success(ltype)
    if ltype == SHORT and (rtype == BIT or rtype == BYTE):
        return Success(ltype)
    if ltype == INT and (rtype == BIT or rtype == BYTE or rtype == SHORT):
        return Success(ltype)
    return Failure(TypingAssignCompatabilityError(ltype, rtype))


def get_type_literal(literal: str) -> Result[str, TypingNoTypeError]:
    if literal == "false" or literal == "true":
        return Success(BOOL)

    try:
        value: int = int(literal)
        if value == 0 or value == 1:
            return Success(BIT)
        if BYTEMIN <= value and value <= BYTEMAX:
            return Success(BYTE)
        elif SHORTMIN <= value and value <= SHORTMAX:
            return Success(SHORT)
        elif INTMIN <= value and value <= INTMAX:
            return Success(INT)
    except ValueError:
        pass

    return Failure(TypingNoTypeError(literal))


# class Type:
#     __slots__ = ()

#     def __init__(self) -> None:
#         pass

#     def check_init_compatible(init: str) -> Result[Tuple, TypingInitCompatabilityError]:
#         pass

# class Bit:
#     text: Final[str] = "bit"

#     def check_init_compatible(init: str) -> Result[Tuple, TypingInitCompatabilityError]:
#         if init == "0" or init == "1":
#             return Success(())
#         return Failure(TypingInitCompatabilityError(Bit.text, init))
