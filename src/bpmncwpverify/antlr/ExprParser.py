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
        4,1,12,72,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,2,5,7,5,1,0,1,
        0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,5,1,22,8,1,10,1,12,1,25,9,1,1,2,1,
        2,1,2,1,2,1,2,1,2,3,2,33,8,2,1,2,1,2,1,2,5,2,38,8,2,10,2,12,2,41,
        9,2,1,3,1,3,1,3,3,3,46,8,3,1,4,1,4,1,4,1,4,1,5,1,5,1,5,1,5,3,5,56,
        8,5,1,5,1,5,1,5,1,5,3,5,62,8,5,1,5,1,5,1,5,5,5,67,8,5,10,5,12,5,
        70,9,5,1,5,0,3,2,4,10,6,0,2,4,6,8,10,0,1,1,0,6,7,72,0,12,1,0,0,0,
        2,15,1,0,0,0,4,32,1,0,0,0,6,45,1,0,0,0,8,47,1,0,0,0,10,61,1,0,0,
        0,12,13,3,2,1,0,13,14,5,0,0,1,14,1,1,0,0,0,15,16,6,1,-1,0,16,17,
        3,4,2,0,17,23,1,0,0,0,18,19,10,2,0,0,19,20,5,10,0,0,20,22,3,2,1,
        3,21,18,1,0,0,0,22,25,1,0,0,0,23,21,1,0,0,0,23,24,1,0,0,0,24,3,1,
        0,0,0,25,23,1,0,0,0,26,27,6,2,-1,0,27,33,3,6,3,0,28,29,5,1,0,0,29,
        30,3,4,2,0,30,31,5,2,0,0,31,33,1,0,0,0,32,26,1,0,0,0,32,28,1,0,0,
        0,33,39,1,0,0,0,34,35,10,3,0,0,35,36,5,9,0,0,36,38,3,4,2,4,37,34,
        1,0,0,0,38,41,1,0,0,0,39,37,1,0,0,0,39,40,1,0,0,0,40,5,1,0,0,0,41,
        39,1,0,0,0,42,43,5,5,0,0,43,46,3,8,4,0,44,46,3,8,4,0,45,42,1,0,0,
        0,45,44,1,0,0,0,46,7,1,0,0,0,47,48,3,10,5,0,48,49,5,8,0,0,49,50,
        3,10,5,0,50,9,1,0,0,0,51,55,6,5,-1,0,52,56,5,3,0,0,53,54,5,6,0,0,
        54,56,5,3,0,0,55,52,1,0,0,0,55,53,1,0,0,0,56,62,1,0,0,0,57,58,5,
        1,0,0,58,59,3,10,5,0,59,60,5,2,0,0,60,62,1,0,0,0,61,51,1,0,0,0,61,
        57,1,0,0,0,62,68,1,0,0,0,63,64,10,3,0,0,64,65,7,0,0,0,65,67,3,10,
        5,4,66,63,1,0,0,0,67,70,1,0,0,0,68,66,1,0,0,0,68,69,1,0,0,0,69,11,
        1,0,0,0,70,68,1,0,0,0,7,23,32,39,45,55,61,68
    ]

class ExprParser ( Parser ):

    grammarFileName = "Expr.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'('", "')'", "<INVALID>", "<INVALID>", 
                     "'!'", "'-'" ]

    symbolicNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "ID", "WS", 
                      "NOT", "MINUS", "NUMERIC_COMPUTATION", "NUMERIC_RELATIONAL", 
                      "BINARYOP", "IMPLIESOP", "NEWLINE", "INT" ]

    RULE_prog = 0
    RULE_expr = 1
    RULE_binary_expr = 2
    RULE_relational_expr = 3
    RULE_relational_comparison = 4
    RULE_numeric_computational_expr = 5

    ruleNames =  [ "prog", "expr", "binary_expr", "relational_expr", "relational_comparison", 
                   "numeric_computational_expr" ]

    EOF = Token.EOF
    T__0=1
    T__1=2
    ID=3
    WS=4
    NOT=5
    MINUS=6
    NUMERIC_COMPUTATION=7
    NUMERIC_RELATIONAL=8
    BINARYOP=9
    IMPLIESOP=10
    NEWLINE=11
    INT=12

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.2")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class ProgContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def expr(self):
            return self.getTypedRuleContext(ExprParser.ExprContext,0)


        def EOF(self):
            return self.getToken(ExprParser.EOF, 0)

        def getRuleIndex(self):
            return ExprParser.RULE_prog

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterProg" ):
                listener.enterProg(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitProg" ):
                listener.exitProg(self)




    def prog(self):

        localctx = ExprParser.ProgContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_prog)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 12
            self.expr(0)
            self.state = 13
            self.match(ExprParser.EOF)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class ExprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def binary_expr(self):
            return self.getTypedRuleContext(ExprParser.Binary_exprContext,0)


        def expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ExprParser.ExprContext)
            else:
                return self.getTypedRuleContext(ExprParser.ExprContext,i)


        def IMPLIESOP(self):
            return self.getToken(ExprParser.IMPLIESOP, 0)

        def getRuleIndex(self):
            return ExprParser.RULE_expr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterExpr" ):
                listener.enterExpr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitExpr" ):
                listener.exitExpr(self)



    def expr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = ExprParser.ExprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 2
        self.enterRecursionRule(localctx, 2, self.RULE_expr, _p)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 16
            self.binary_expr(0)
            self._ctx.stop = self._input.LT(-1)
            self.state = 23
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,0,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    localctx = ExprParser.ExprContext(self, _parentctx, _parentState)
                    self.pushNewRecursionContext(localctx, _startState, self.RULE_expr)
                    self.state = 18
                    if not self.precpred(self._ctx, 2):
                        from antlr4.error.Errors import FailedPredicateException
                        raise FailedPredicateException(self, "self.precpred(self._ctx, 2)")
                    self.state = 19
                    self.match(ExprParser.IMPLIESOP)
                    self.state = 20
                    self.expr(3) 
                self.state = 25
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,0,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class Binary_exprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def relational_expr(self):
            return self.getTypedRuleContext(ExprParser.Relational_exprContext,0)


        def binary_expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ExprParser.Binary_exprContext)
            else:
                return self.getTypedRuleContext(ExprParser.Binary_exprContext,i)


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



    def binary_expr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = ExprParser.Binary_exprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 4
        self.enterRecursionRule(localctx, 4, self.RULE_binary_expr, _p)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 32
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,1,self._ctx)
            if la_ == 1:
                self.state = 27
                self.relational_expr()
                pass

            elif la_ == 2:
                self.state = 28
                self.match(ExprParser.T__0)
                self.state = 29
                self.binary_expr(0)
                self.state = 30
                self.match(ExprParser.T__1)
                pass


            self._ctx.stop = self._input.LT(-1)
            self.state = 39
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,2,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    localctx = ExprParser.Binary_exprContext(self, _parentctx, _parentState)
                    self.pushNewRecursionContext(localctx, _startState, self.RULE_binary_expr)
                    self.state = 34
                    if not self.precpred(self._ctx, 3):
                        from antlr4.error.Errors import FailedPredicateException
                        raise FailedPredicateException(self, "self.precpred(self._ctx, 3)")
                    self.state = 35
                    self.match(ExprParser.BINARYOP)
                    self.state = 36
                    self.binary_expr(4) 
                self.state = 41
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,2,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class Relational_exprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def NOT(self):
            return self.getToken(ExprParser.NOT, 0)

        def relational_comparison(self):
            return self.getTypedRuleContext(ExprParser.Relational_comparisonContext,0)


        def getRuleIndex(self):
            return ExprParser.RULE_relational_expr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterRelational_expr" ):
                listener.enterRelational_expr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitRelational_expr" ):
                listener.exitRelational_expr(self)




    def relational_expr(self):

        localctx = ExprParser.Relational_exprContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_relational_expr)
        try:
            self.state = 45
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [5]:
                self.enterOuterAlt(localctx, 1)
                self.state = 42
                self.match(ExprParser.NOT)
                self.state = 43
                self.relational_comparison()
                pass
            elif token in [1, 3, 6]:
                self.enterOuterAlt(localctx, 2)
                self.state = 44
                self.relational_comparison()
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


    class Relational_comparisonContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def numeric_computational_expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ExprParser.Numeric_computational_exprContext)
            else:
                return self.getTypedRuleContext(ExprParser.Numeric_computational_exprContext,i)


        def NUMERIC_RELATIONAL(self):
            return self.getToken(ExprParser.NUMERIC_RELATIONAL, 0)

        def getRuleIndex(self):
            return ExprParser.RULE_relational_comparison

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterRelational_comparison" ):
                listener.enterRelational_comparison(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitRelational_comparison" ):
                listener.exitRelational_comparison(self)




    def relational_comparison(self):

        localctx = ExprParser.Relational_comparisonContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_relational_comparison)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 47
            self.numeric_computational_expr(0)
            self.state = 48
            self.match(ExprParser.NUMERIC_RELATIONAL)
            self.state = 49
            self.numeric_computational_expr(0)
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

        def ID(self):
            return self.getToken(ExprParser.ID, 0)

        def MINUS(self):
            return self.getToken(ExprParser.MINUS, 0)

        def numeric_computational_expr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ExprParser.Numeric_computational_exprContext)
            else:
                return self.getTypedRuleContext(ExprParser.Numeric_computational_exprContext,i)


        def NUMERIC_COMPUTATION(self):
            return self.getToken(ExprParser.NUMERIC_COMPUTATION, 0)

        def getRuleIndex(self):
            return ExprParser.RULE_numeric_computational_expr

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterNumeric_computational_expr" ):
                listener.enterNumeric_computational_expr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitNumeric_computational_expr" ):
                listener.exitNumeric_computational_expr(self)



    def numeric_computational_expr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = ExprParser.Numeric_computational_exprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 10
        self.enterRecursionRule(localctx, 10, self.RULE_numeric_computational_expr, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 61
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [3, 6]:
                self.state = 55
                self._errHandler.sync(self)
                token = self._input.LA(1)
                if token in [3]:
                    self.state = 52
                    self.match(ExprParser.ID)
                    pass
                elif token in [6]:
                    self.state = 53
                    self.match(ExprParser.MINUS)
                    self.state = 54
                    self.match(ExprParser.ID)
                    pass
                else:
                    raise NoViableAltException(self)

                pass
            elif token in [1]:
                self.state = 57
                self.match(ExprParser.T__0)
                self.state = 58
                self.numeric_computational_expr(0)
                self.state = 59
                self.match(ExprParser.T__1)
                pass
            else:
                raise NoViableAltException(self)

            self._ctx.stop = self._input.LT(-1)
            self.state = 68
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,6,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    localctx = ExprParser.Numeric_computational_exprContext(self, _parentctx, _parentState)
                    self.pushNewRecursionContext(localctx, _startState, self.RULE_numeric_computational_expr)
                    self.state = 63
                    if not self.precpred(self._ctx, 3):
                        from antlr4.error.Errors import FailedPredicateException
                        raise FailedPredicateException(self, "self.precpred(self._ctx, 3)")
                    self.state = 64
                    _la = self._input.LA(1)
                    if not(_la==6 or _la==7):
                        self._errHandler.recoverInline(self)
                    else:
                        self._errHandler.reportMatch(self)
                        self.consume()
                    self.state = 65
                    self.numeric_computational_expr(4) 
                self.state = 70
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,6,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx



    def sempred(self, localctx:RuleContext, ruleIndex:int, predIndex:int):
        if self._predicates == None:
            self._predicates = dict()
        self._predicates[1] = self.expr_sempred
        self._predicates[2] = self.binary_expr_sempred
        self._predicates[5] = self.numeric_computational_expr_sempred
        pred = self._predicates.get(ruleIndex, None)
        if pred is None:
            raise Exception("No predicate with index:" + str(ruleIndex))
        else:
            return pred(localctx, predIndex)

    def expr_sempred(self, localctx:ExprContext, predIndex:int):
            if predIndex == 0:
                return self.precpred(self._ctx, 2)
         

    def binary_expr_sempred(self, localctx:Binary_exprContext, predIndex:int):
            if predIndex == 1:
                return self.precpred(self._ctx, 3)
         

    def numeric_computational_expr_sempred(self, localctx:Numeric_computational_exprContext, predIndex:int):
            if predIndex == 2:
                return self.precpred(self._ctx, 3)
         




