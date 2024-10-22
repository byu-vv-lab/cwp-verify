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
        4,1,7,63,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,1,0,5,0,10,8,0,10,0,12,
        0,13,9,0,1,0,5,0,16,8,0,10,0,12,0,19,9,0,1,0,4,0,22,8,0,11,0,12,
        0,23,1,0,1,0,1,1,1,1,1,1,3,1,31,8,1,1,1,1,1,1,1,1,1,3,1,37,8,1,1,
        2,1,2,1,2,3,2,42,8,2,1,2,1,2,1,2,1,2,3,2,48,8,2,1,3,1,3,1,3,1,3,
        3,3,54,8,3,1,3,1,3,1,3,1,3,1,3,3,3,61,8,3,1,3,0,0,4,0,2,4,6,0,1,
        1,0,4,5,69,0,11,1,0,0,0,2,30,1,0,0,0,4,41,1,0,0,0,6,53,1,0,0,0,8,
        10,3,2,1,0,9,8,1,0,0,0,10,13,1,0,0,0,11,9,1,0,0,0,11,12,1,0,0,0,
        12,17,1,0,0,0,13,11,1,0,0,0,14,16,3,4,2,0,15,14,1,0,0,0,16,19,1,
        0,0,0,17,15,1,0,0,0,17,18,1,0,0,0,18,21,1,0,0,0,19,17,1,0,0,0,20,
        22,3,6,3,0,21,20,1,0,0,0,22,23,1,0,0,0,23,21,1,0,0,0,23,24,1,0,0,
        0,24,25,1,0,0,0,25,26,5,0,0,1,26,1,1,0,0,0,27,31,5,1,0,0,28,29,5,
        4,0,0,29,31,5,1,0,0,30,27,1,0,0,0,30,28,1,0,0,0,31,32,1,0,0,0,32,
        36,7,0,0,0,33,37,5,1,0,0,34,35,5,4,0,0,35,37,5,1,0,0,36,33,1,0,0,
        0,36,34,1,0,0,0,37,3,1,0,0,0,38,42,5,1,0,0,39,40,5,3,0,0,40,42,5,
        1,0,0,41,38,1,0,0,0,41,39,1,0,0,0,42,43,1,0,0,0,43,47,5,6,0,0,44,
        48,5,1,0,0,45,46,5,3,0,0,46,48,5,1,0,0,47,44,1,0,0,0,47,45,1,0,0,
        0,48,5,1,0,0,0,49,54,5,1,0,0,50,51,5,3,0,0,51,54,5,1,0,0,52,54,3,
        4,2,0,53,49,1,0,0,0,53,50,1,0,0,0,53,52,1,0,0,0,54,55,1,0,0,0,55,
        60,5,7,0,0,56,61,5,1,0,0,57,58,5,3,0,0,58,61,5,1,0,0,59,61,3,4,2,
        0,60,56,1,0,0,0,60,57,1,0,0,0,60,59,1,0,0,0,61,7,1,0,0,0,9,11,17,
        23,30,36,41,47,53,60
    ]

class ExprParser ( Parser ):

    grammarFileName = "Expr.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "'!'", "'-'" ]

    symbolicNames = [ "<INVALID>", "ID", "WS", "NOT", "MINUS", "STRICTLY_MATH", 
                      "BINARYOP", "IMPLIESOP" ]

    RULE_expr = 0
    RULE_strictly_math_expr = 1
    RULE_binary_expr = 2
    RULE_implies_expr = 3

    ruleNames =  [ "expr", "strictly_math_expr", "binary_expr", "implies_expr" ]

    EOF = Token.EOF
    ID=1
    WS=2
    NOT=3
    MINUS=4
    STRICTLY_MATH=5
    BINARYOP=6
    IMPLIESOP=7

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

        def strictly_math_expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ExprParser.Strictly_math_exprContext)
            else:
                return self.getTypedRuleContext(ExprParser.Strictly_math_exprContext,i)


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
            self.state = 11
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,0,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    self.state = 8
                    self.strictly_math_expr() 
                self.state = 13
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,0,self._ctx)

            self.state = 17
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,1,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    self.state = 14
                    self.binary_expr() 
                self.state = 19
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,1,self._ctx)

            self.state = 21 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 20
                self.implies_expr()
                self.state = 23 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==1 or _la==3):
                    break

            self.state = 25
            self.match(ExprParser.EOF)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Strictly_math_exprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def MINUS(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.MINUS)
            else:
                return self.getToken(ExprParser.MINUS, i)

        def STRICTLY_MATH(self):
            return self.getToken(ExprParser.STRICTLY_MATH, 0)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(ExprParser.ID)
            else:
                return self.getToken(ExprParser.ID, i)

        def getRuleIndex(self):
            return ExprParser.RULE_strictly_math_expr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterStrictly_math_expr" ):
                listener.enterStrictly_math_expr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitStrictly_math_expr" ):
                listener.exitStrictly_math_expr(self)




    def strictly_math_expr(self):

        localctx = ExprParser.Strictly_math_exprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_strictly_math_expr)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 30
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [1]:
                self.state = 27
                self.match(ExprParser.ID)
                pass
            elif token in [4]:
                self.state = 28
                self.match(ExprParser.MINUS)
                self.state = 29
                self.match(ExprParser.ID)
                pass
            else:
                raise NoViableAltException(self)

            self.state = 32
            _la = self._input.LA(1)
            if not(_la==4 or _la==5):
                self._errHandler.recoverInline(self)
            else:
                self._errHandler.reportMatch(self)
                self.consume()
            self.state = 36
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [1]:
                self.state = 33
                self.match(ExprParser.ID)
                pass
            elif token in [4]:
                self.state = 34
                self.match(ExprParser.MINUS)
                self.state = 35
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
        self.enterRule(localctx, 4, self.RULE_binary_expr)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 41
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [1]:
                self.state = 38
                self.match(ExprParser.ID)
                pass
            elif token in [3]:
                self.state = 39
                self.match(ExprParser.NOT)
                self.state = 40
                self.match(ExprParser.ID)
                pass
            else:
                raise NoViableAltException(self)

            self.state = 43
            self.match(ExprParser.BINARYOP)
            self.state = 47
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [1]:
                self.state = 44
                self.match(ExprParser.ID)
                pass
            elif token in [3]:
                self.state = 45
                self.match(ExprParser.NOT)
                self.state = 46
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
        self.enterRule(localctx, 6, self.RULE_implies_expr)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 53
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,7,self._ctx)
            if la_ == 1:
                self.state = 49
                self.match(ExprParser.ID)
                pass

            elif la_ == 2:
                self.state = 50
                self.match(ExprParser.NOT)
                self.state = 51
                self.match(ExprParser.ID)
                pass

            elif la_ == 3:
                self.state = 52
                self.binary_expr()
                pass


            self.state = 55
            self.match(ExprParser.IMPLIESOP)
            self.state = 60
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,8,self._ctx)
            if la_ == 1:
                self.state = 56
                self.match(ExprParser.ID)
                pass

            elif la_ == 2:
                self.state = 57
                self.match(ExprParser.NOT)
                self.state = 58
                self.match(ExprParser.ID)
                pass

            elif la_ == 3:
                self.state = 59
                self.binary_expr()
                pass


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





