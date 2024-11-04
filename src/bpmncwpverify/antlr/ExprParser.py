# Generated from antlr/Expr.g4 by ANTLR 4.13.2
# encoding: utf-8
# type: ignore
from antlr4 import *
from io import StringIO
import sys
if sys.version_info[1] > 5:
	from typing import TextIO
else:
	from typing.io import TextIO

def serializedATN():
    return [
        4,1,8,82,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,1,0,5,0,12,8,0,
        10,0,12,0,15,9,0,1,0,5,0,18,8,0,10,0,12,0,21,9,0,1,0,4,0,24,8,0,
        11,0,12,0,25,1,0,1,0,1,1,1,1,1,1,3,1,33,8,1,1,1,1,1,1,1,1,1,3,1,
        39,8,1,1,2,1,2,1,2,3,2,44,8,2,1,2,1,2,1,2,1,2,3,2,50,8,2,1,3,1,3,
        1,3,1,3,1,3,1,3,3,3,58,8,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,3,3,67,8,
        3,1,4,1,4,1,4,1,4,3,4,73,8,4,1,4,1,4,1,4,1,4,1,4,3,4,80,8,4,1,4,
        0,0,5,0,2,4,6,8,0,1,1,0,4,5,93,0,13,1,0,0,0,2,32,1,0,0,0,4,43,1,
        0,0,0,6,57,1,0,0,0,8,72,1,0,0,0,10,12,3,2,1,0,11,10,1,0,0,0,12,15,
        1,0,0,0,13,11,1,0,0,0,13,14,1,0,0,0,14,19,1,0,0,0,15,13,1,0,0,0,
        16,18,3,6,3,0,17,16,1,0,0,0,18,21,1,0,0,0,19,17,1,0,0,0,19,20,1,
        0,0,0,20,23,1,0,0,0,21,19,1,0,0,0,22,24,3,8,4,0,23,22,1,0,0,0,24,
        25,1,0,0,0,25,23,1,0,0,0,25,26,1,0,0,0,26,27,1,0,0,0,27,28,5,0,0,
        1,28,1,1,0,0,0,29,33,5,1,0,0,30,31,5,4,0,0,31,33,5,1,0,0,32,29,1,
        0,0,0,32,30,1,0,0,0,33,34,1,0,0,0,34,38,7,0,0,0,35,39,5,1,0,0,36,
        37,5,4,0,0,37,39,5,1,0,0,38,35,1,0,0,0,38,36,1,0,0,0,39,3,1,0,0,
        0,40,44,5,1,0,0,41,42,5,4,0,0,42,44,5,1,0,0,43,40,1,0,0,0,43,41,
        1,0,0,0,44,45,1,0,0,0,45,49,5,6,0,0,46,50,5,1,0,0,47,48,5,4,0,0,
        48,50,5,1,0,0,49,46,1,0,0,0,49,47,1,0,0,0,50,5,1,0,0,0,51,58,5,1,
        0,0,52,53,5,3,0,0,53,58,5,1,0,0,54,58,3,4,2,0,55,56,5,3,0,0,56,58,
        3,4,2,0,57,51,1,0,0,0,57,52,1,0,0,0,57,54,1,0,0,0,57,55,1,0,0,0,
        58,59,1,0,0,0,59,66,5,7,0,0,60,67,5,1,0,0,61,62,5,3,0,0,62,67,5,
        1,0,0,63,67,3,4,2,0,64,65,5,3,0,0,65,67,3,4,2,0,66,60,1,0,0,0,66,
        61,1,0,0,0,66,63,1,0,0,0,66,64,1,0,0,0,67,7,1,0,0,0,68,73,5,1,0,
        0,69,70,5,3,0,0,70,73,5,1,0,0,71,73,3,6,3,0,72,68,1,0,0,0,72,69,
        1,0,0,0,72,71,1,0,0,0,73,74,1,0,0,0,74,79,5,8,0,0,75,80,5,1,0,0,
        76,77,5,3,0,0,77,80,5,1,0,0,78,80,3,6,3,0,79,75,1,0,0,0,79,76,1,
        0,0,0,79,78,1,0,0,0,80,9,1,0,0,0,11,13,19,25,32,38,43,49,57,66,72,
        79
    ]

class ExprParser ( Parser ):

    grammarFileName = "Expr.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "'!'", "'-'" ]

    symbolicNames = [ "<INVALID>", "ID", "WS", "NOT", "MINUS", "NUMERIC_COMPUTATION", 
                      "NUMERIC_RELATIONAL", "BINARYOP", "IMPLIESOP" ]

    RULE_expr = 0
    RULE_numeric_computational_expr = 1
    RULE_numeric_relational_expr = 2
    RULE_binary_expr = 3
    RULE_implies_expr = 4

    ruleNames =  [ "expr", "numeric_computational_expr", "numeric_relational_expr", 
                   "binary_expr", "implies_expr" ]

    EOF = Token.EOF
    ID=1
    WS=2
    NOT=3
    MINUS=4
    NUMERIC_COMPUTATION=5
    NUMERIC_RELATIONAL=6
    BINARYOP=7
    IMPLIESOP=8

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.2")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class ExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def EOF(self):
            return self.getToken(ExprParser.EOF, 0)

        def numeric_computational_expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ExprParser.Numeric_computational_exprContext)
            else:
                return self.getTypedRuleContext(ExprParser.Numeric_computational_exprContext,i)


        def binary_expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ExprParser.Binary_exprContext)
            else:
                return self.getTypedRuleContext(ExprParser.Binary_exprContext,i)


        def implies_expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ExprParser.Implies_exprContext)
            else:
                return self.getTypedRuleContext(ExprParser.Implies_exprContext,i)


        def getRuleIndex(self):
            return ExprParser.RULE_expr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterExpr" ):
                listener.enterExpr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitExpr" ):
                listener.exitExpr(self)




    def expr(self):

        localctx = ExprParser.ExprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_expr)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 13
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,0,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    self.state = 10
                    self.numeric_computational_expr() 
                self.state = 15
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,0,self._ctx)

            self.state = 19
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,1,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    self.state = 16
                    self.binary_expr() 
                self.state = 21
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,1,self._ctx)

            self.state = 23 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 22
                self.implies_expr()
                self.state = 25 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not ((((_la) & ~0x3f) == 0 and ((1 << _la) & 26) != 0)):
                    break

            self.state = 27
            self.match(ExprParser.EOF)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Numeric_computational_exprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def MINUS(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.MINUS)
            else:
                return self.getToken(ExprParser.MINUS, i)

        def NUMERIC_COMPUTATION(self):
            return self.getToken(ExprParser.NUMERIC_COMPUTATION, 0)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.ID)
            else:
                return self.getToken(ExprParser.ID, i)

        def getRuleIndex(self):
            return ExprParser.RULE_numeric_computational_expr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterNumeric_computational_expr" ):
                listener.enterNumeric_computational_expr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitNumeric_computational_expr" ):
                listener.exitNumeric_computational_expr(self)




    def numeric_computational_expr(self):

        localctx = ExprParser.Numeric_computational_exprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_numeric_computational_expr)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 32
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [1]:
                self.state = 29
                self.match(ExprParser.ID)
                pass
            elif token in [4]:
                self.state = 30
                self.match(ExprParser.MINUS)
                self.state = 31
                self.match(ExprParser.ID)
                pass
            else:
                raise NoViableAltException(self)

            self.state = 34
            _la = self._input.LA(1)
            if not(_la==4 or _la==5):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
            self.state = 38
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [1]:
                self.state = 35
                self.match(ExprParser.ID)
                pass
            elif token in [4]:
                self.state = 36
                self.match(ExprParser.MINUS)
                self.state = 37
                self.match(ExprParser.ID)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Numeric_relational_exprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.ID)
            else:
                return self.getToken(ExprParser.ID, i)

        def MINUS(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.MINUS)
            else:
                return self.getToken(ExprParser.MINUS, i)

        def NUMERIC_RELATIONAL(self):
            return self.getToken(ExprParser.NUMERIC_RELATIONAL, 0)

        def getRuleIndex(self):
            return ExprParser.RULE_numeric_relational_expr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterNumeric_relational_expr" ):
                listener.enterNumeric_relational_expr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitNumeric_relational_expr" ):
                listener.exitNumeric_relational_expr(self)




    def numeric_relational_expr(self):

        localctx = ExprParser.Numeric_relational_exprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_numeric_relational_expr)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 43
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [1]:
                self.state = 40
                self.match(ExprParser.ID)
                pass
            elif token in [4]:
                self.state = 41
                self.match(ExprParser.MINUS)
                self.state = 42
                self.match(ExprParser.ID)
                pass
            else:
                raise NoViableAltException(self)

            self.state = 45
            self.match(ExprParser.NUMERIC_RELATIONAL)
            self.state = 49
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [1]:
                self.state = 46
                self.match(ExprParser.ID)
                pass
            elif token in [4]:
                self.state = 47
                self.match(ExprParser.MINUS)
                self.state = 48
                self.match(ExprParser.ID)
                pass
            else:
                raise NoViableAltException(self)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Binary_exprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def BINARYOP(self):
            return self.getToken(ExprParser.BINARYOP, 0)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.ID)
            else:
                return self.getToken(ExprParser.ID, i)

        def NOT(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.NOT)
            else:
                return self.getToken(ExprParser.NOT, i)

        def numeric_relational_expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ExprParser.Numeric_relational_exprContext)
            else:
                return self.getTypedRuleContext(ExprParser.Numeric_relational_exprContext,i)


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
        self.enterRule(localctx, 6, self.RULE_binary_expr)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 57
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,7,self._ctx)
            if la_ == 1:
                self.state = 51
                self.match(ExprParser.ID)
                pass

            elif la_ == 2:
                self.state = 52
                self.match(ExprParser.NOT)
                self.state = 53
                self.match(ExprParser.ID)
                pass

            elif la_ == 3:
                self.state = 54
                self.numeric_relational_expr()
                pass

            elif la_ == 4:
                self.state = 55
                self.match(ExprParser.NOT)
                self.state = 56
                self.numeric_relational_expr()
                pass


            self.state = 59
            self.match(ExprParser.BINARYOP)
            self.state = 66
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,8,self._ctx)
            if la_ == 1:
                self.state = 60
                self.match(ExprParser.ID)
                pass

            elif la_ == 2:
                self.state = 61
                self.match(ExprParser.NOT)
                self.state = 62
                self.match(ExprParser.ID)
                pass

            elif la_ == 3:
                self.state = 63
                self.numeric_relational_expr()
                pass

            elif la_ == 4:
                self.state = 64
                self.match(ExprParser.NOT)
                self.state = 65
                self.numeric_relational_expr()
                pass


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Implies_exprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def IMPLIESOP(self):
            return self.getToken(ExprParser.IMPLIESOP, 0)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.ID)
            else:
                return self.getToken(ExprParser.ID, i)

        def NOT(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.NOT)
            else:
                return self.getToken(ExprParser.NOT, i)

        def binary_expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ExprParser.Binary_exprContext)
            else:
                return self.getTypedRuleContext(ExprParser.Binary_exprContext,i)


        def getRuleIndex(self):
            return ExprParser.RULE_implies_expr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterImplies_expr" ):
                listener.enterImplies_expr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitImplies_expr" ):
                listener.exitImplies_expr(self)




    def implies_expr(self):

        localctx = ExprParser.Implies_exprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_implies_expr)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 72
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,9,self._ctx)
            if la_ == 1:
                self.state = 68
                self.match(ExprParser.ID)
                pass

            elif la_ == 2:
                self.state = 69
                self.match(ExprParser.NOT)
                self.state = 70
                self.match(ExprParser.ID)
                pass

            elif la_ == 3:
                self.state = 71
                self.binary_expr()
                pass


            self.state = 74
            self.match(ExprParser.IMPLIESOP)
            self.state = 79
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,10,self._ctx)
            if la_ == 1:
                self.state = 75
                self.match(ExprParser.ID)
                pass

            elif la_ == 2:
                self.state = 76
                self.match(ExprParser.NOT)
                self.state = 77
                self.match(ExprParser.ID)
                pass

            elif la_ == 3:
                self.state = 78
                self.binary_expr()
                pass


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





