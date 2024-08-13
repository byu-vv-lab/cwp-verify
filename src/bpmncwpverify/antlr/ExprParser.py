# Generated from antlr/Expr.g4 by ANTLR 4.13.2
# encoding: utf-8
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
	from typing import TextIO
else:
	from typing.io import TextIO

def serializedATN():
    return [
        4,1,12,7,2,0,7,0,1,0,1,0,1,0,1,0,1,0,0,0,1,0,0,0,5,0,2,1,0,0,0,2,
        3,5,8,0,0,3,4,5,11,0,0,4,5,5,8,0,0,5,1,1,0,0,0,0
    ]

class ExprParser ( Parser ):

    grammarFileName = "Expr.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "':'", "'const'", "'enum'", "'='", "'{'", 
                     "'}'", "'var'" ]

    symbolicNames = [ "<INVALID>", "COLON", "CONST", "ENUM", "EQUALS", "LCURLY", 
                      "RCURLY", "VAR", "ID", "WS", "ANDOR", "BINARYOP", 
                      "IMPLYOP" ]

    RULE_binary_expr = 0

    ruleNames =  [ "binary_expr" ]

    EOF = Token.EOF
    COLON=1
    CONST=2
    ENUM=3
    EQUALS=4
    LCURLY=5
    RCURLY=6
    VAR=7
    ID=8
    WS=9
    ANDOR=10
    BINARYOP=11
    IMPLYOP=12

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.2")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class Binary_exprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.ID)
            else:
                return self.getToken(ExprParser.ID, i)

        def BINARYOP(self):
            return self.getToken(ExprParser.BINARYOP, 0)

        def getRuleIndex(self):
            return ExprParser.RULE_binary_expr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterBinary_expr" ):
                listener.enterBinary_expr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitBinary_expr" ):
                listener.exitBinary_expr(self)




    def binary_expr(self):

        localctx = ExprParser.Binary_exprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_binary_expr)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 2
            self.match(ExprParser.ID)
            self.state = 3
            self.match(ExprParser.BINARYOP)
            self.state = 4
            self.match(ExprParser.ID)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





