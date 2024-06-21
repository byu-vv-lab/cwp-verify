# Generated from antlr/State.g4 by ANTLR 4.13.1
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
    from typing import TextIO
else:
    from typing.io import TextIO


def serializedATN():
    return [
        4,0,9,54,6,-1,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,2,
        6,7,6,2,7,7,7,2,8,7,8,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,
        2,1,2,1,2,1,3,1,3,1,4,1,4,1,5,1,5,1,6,1,6,1,6,1,6,1,7,4,7,44,8,7,
        11,7,12,7,45,1,8,4,8,49,8,8,11,8,12,8,50,1,8,1,8,0,0,9,1,1,3,2,5,
        3,7,4,9,5,11,6,13,7,15,8,17,9,1,0,2,4,0,48,57,65,90,95,95,97,122,
        3,0,9,10,13,13,32,32,55,0,1,1,0,0,0,0,3,1,0,0,0,0,5,1,0,0,0,0,7,
        1,0,0,0,0,9,1,0,0,0,0,11,1,0,0,0,0,13,1,0,0,0,0,15,1,0,0,0,0,17,
        1,0,0,0,1,19,1,0,0,0,3,21,1,0,0,0,5,27,1,0,0,0,7,32,1,0,0,0,9,34,
        1,0,0,0,11,36,1,0,0,0,13,38,1,0,0,0,15,43,1,0,0,0,17,48,1,0,0,0,
        19,20,5,58,0,0,20,2,1,0,0,0,21,22,5,99,0,0,22,23,5,111,0,0,23,24,
        5,110,0,0,24,25,5,115,0,0,25,26,5,116,0,0,26,4,1,0,0,0,27,28,5,101,
        0,0,28,29,5,110,0,0,29,30,5,117,0,0,30,31,5,109,0,0,31,6,1,0,0,0,
        32,33,5,61,0,0,33,8,1,0,0,0,34,35,5,123,0,0,35,10,1,0,0,0,36,37,
        5,125,0,0,37,12,1,0,0,0,38,39,5,118,0,0,39,40,5,97,0,0,40,41,5,114,
        0,0,41,14,1,0,0,0,42,44,7,0,0,0,43,42,1,0,0,0,44,45,1,0,0,0,45,43,
        1,0,0,0,45,46,1,0,0,0,46,16,1,0,0,0,47,49,7,1,0,0,48,47,1,0,0,0,
        49,50,1,0,0,0,50,48,1,0,0,0,50,51,1,0,0,0,51,52,1,0,0,0,52,53,6,
        8,0,0,53,18,1,0,0,0,3,0,45,50,1,6,0,0
    ]

class StateLexer(Lexer):

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    COLON = 1
    CONST = 2
    ENUM = 3
    EQUALS = 4
    LCURLY = 5
    RCURLY = 6
    VAR = 7
    ID = 8
    WS = 9

    channelNames = [ u"DEFAULT_TOKEN_CHANNEL", u"HIDDEN" ]

    modeNames = [ "DEFAULT_MODE" ]

    literalNames = [ "<INVALID>",
            "':'", "'const'", "'enum'", "'='", "'{'", "'}'", "'var'" ]

    symbolicNames = [ "<INVALID>",
            "COLON", "CONST", "ENUM", "EQUALS", "LCURLY", "RCURLY", "VAR", 
            "ID", "WS" ]

    ruleNames = [ "COLON", "CONST", "ENUM", "EQUALS", "LCURLY", "RCURLY", 
                  "VAR", "ID", "WS" ]

    grammarFileName = "State.g4"

    def __init__(self, input=None, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.1")
        self._interp = LexerATNSimulator(self, self.atn, self.decisionsToDFA, PredictionContextCache())
        self._actions = None
        self._predicates = None


