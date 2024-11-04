# Generated from antlr/Expr.g4 by ANTLR 4.13.2
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
    from typing import TextIO
else:
    from typing.io import TextIO


def serializedATN():
    return [
        4,0,8,68,6,-1,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,
        6,7,6,2,7,7,7,1,0,4,0,19,8,0,11,0,12,0,20,1,1,4,1,24,8,1,11,1,12,
        1,25,1,1,1,1,1,2,1,2,1,3,1,3,1,4,1,4,1,4,1,4,3,4,38,8,4,1,5,1,5,
        1,5,1,5,1,5,3,5,45,8,5,1,6,1,6,1,6,1,6,1,6,1,6,1,6,1,6,3,6,55,8,
        6,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,1,7,3,7,67,8,7,0,0,8,1,1,3,
        2,5,3,7,4,9,5,11,6,13,7,15,8,1,0,5,4,0,48,57,65,90,95,95,97,122,
        3,0,9,10,13,13,32,32,2,0,42,42,47,47,2,0,37,37,43,43,2,0,60,60,62,
        62,78,0,1,1,0,0,0,0,3,1,0,0,0,0,5,1,0,0,0,0,7,1,0,0,0,0,9,1,0,0,
        0,0,11,1,0,0,0,0,13,1,0,0,0,0,15,1,0,0,0,1,18,1,0,0,0,3,23,1,0,0,
        0,5,29,1,0,0,0,7,31,1,0,0,0,9,37,1,0,0,0,11,44,1,0,0,0,13,54,1,0,
        0,0,15,66,1,0,0,0,17,19,7,0,0,0,18,17,1,0,0,0,19,20,1,0,0,0,20,18,
        1,0,0,0,20,21,1,0,0,0,21,2,1,0,0,0,22,24,7,1,0,0,23,22,1,0,0,0,24,
        25,1,0,0,0,25,23,1,0,0,0,25,26,1,0,0,0,26,27,1,0,0,0,27,28,6,1,0,
        0,28,4,1,0,0,0,29,30,5,33,0,0,30,6,1,0,0,0,31,32,5,45,0,0,32,8,1,
        0,0,0,33,38,7,2,0,0,34,35,5,47,0,0,35,38,5,47,0,0,36,38,7,3,0,0,
        37,33,1,0,0,0,37,34,1,0,0,0,37,36,1,0,0,0,38,10,1,0,0,0,39,45,7,
        4,0,0,40,41,5,62,0,0,41,45,5,61,0,0,42,43,5,60,0,0,43,45,5,61,0,
        0,44,39,1,0,0,0,44,40,1,0,0,0,44,42,1,0,0,0,45,12,1,0,0,0,46,47,
        5,38,0,0,47,55,5,38,0,0,48,49,5,124,0,0,49,55,5,124,0,0,50,51,5,
        61,0,0,51,55,5,61,0,0,52,53,5,33,0,0,53,55,5,61,0,0,54,46,1,0,0,
        0,54,48,1,0,0,0,54,50,1,0,0,0,54,52,1,0,0,0,55,14,1,0,0,0,56,57,
        5,61,0,0,57,58,5,61,0,0,58,67,5,62,0,0,59,60,5,60,0,0,60,61,5,61,
        0,0,61,67,5,61,0,0,62,63,5,60,0,0,63,64,5,61,0,0,64,65,5,61,0,0,
        65,67,5,62,0,0,66,56,1,0,0,0,66,59,1,0,0,0,66,62,1,0,0,0,67,16,1,
        0,0,0,7,0,20,25,37,44,54,66,1,6,0,0
    ]

class ExprLexer(Lexer):

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    ID = 1
    WS = 2
    NOT = 3
    MINUS = 4
    NUMERIC_COMPUTATION = 5
    NUMERIC_RELATIONAL = 6
    BINARYOP = 7
    IMPLIESOP = 8

    channelNames = [ u"DEFAULT_TOKEN_CHANNEL", u"HIDDEN" ]

    modeNames = [ "DEFAULT_MODE" ]

    literalNames = [ "<INVALID>",
            "'!'", "'-'" ]

    symbolicNames = [ "<INVALID>",
            "ID", "WS", "NOT", "MINUS", "NUMERIC_COMPUTATION", "NUMERIC_RELATIONAL", 
            "BINARYOP", "IMPLIESOP" ]

    ruleNames = [ "ID", "WS", "NOT", "MINUS", "NUMERIC_COMPUTATION", "NUMERIC_RELATIONAL", 
                  "BINARYOP", "IMPLIESOP" ]

    grammarFileName = "Expr.g4"

    def __init__(self, input=None, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.2")
        self._interp = LexerATNSimulator(self, self.atn, self.decisionsToDFA, PredictionContextCache())
        self._actions = None
        self._predicates = None


