# Generated from antlr/State.g4 by ANTLR 4.13.1
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
        4,1,9,60,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,1,0,5,0,10,8,0,10,0,12,
        0,13,9,0,1,0,5,0,16,8,0,10,0,12,0,19,9,0,1,0,4,0,22,8,0,11,0,12,
        0,23,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,1,2,1,2,1,2,4,2,39,
        8,2,11,2,12,2,40,1,2,1,2,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,4,3,53,
        8,3,11,3,12,3,54,1,3,3,3,58,8,3,1,3,0,0,4,0,2,4,6,0,0,61,0,11,1,
        0,0,0,2,27,1,0,0,0,4,34,1,0,0,0,6,44,1,0,0,0,8,10,3,4,2,0,9,8,1,
        0,0,0,10,13,1,0,0,0,11,9,1,0,0,0,11,12,1,0,0,0,12,17,1,0,0,0,13,
        11,1,0,0,0,14,16,3,2,1,0,15,14,1,0,0,0,16,19,1,0,0,0,17,15,1,0,0,
        0,17,18,1,0,0,0,18,21,1,0,0,0,19,17,1,0,0,0,20,22,3,6,3,0,21,20,
        1,0,0,0,22,23,1,0,0,0,23,21,1,0,0,0,23,24,1,0,0,0,24,25,1,0,0,0,
        25,26,5,0,0,1,26,1,1,0,0,0,27,28,5,2,0,0,28,29,5,8,0,0,29,30,5,1,
        0,0,30,31,5,8,0,0,31,32,5,4,0,0,32,33,5,8,0,0,33,3,1,0,0,0,34,35,
        5,3,0,0,35,36,5,8,0,0,36,38,5,5,0,0,37,39,5,8,0,0,38,37,1,0,0,0,
        39,40,1,0,0,0,40,38,1,0,0,0,40,41,1,0,0,0,41,42,1,0,0,0,42,43,5,
        6,0,0,43,5,1,0,0,0,44,45,5,7,0,0,45,46,5,8,0,0,46,47,5,1,0,0,47,
        48,5,8,0,0,48,49,5,4,0,0,49,57,5,8,0,0,50,52,5,5,0,0,51,53,5,8,0,
        0,52,51,1,0,0,0,53,54,1,0,0,0,54,52,1,0,0,0,54,55,1,0,0,0,55,56,
        1,0,0,0,56,58,5,6,0,0,57,50,1,0,0,0,57,58,1,0,0,0,58,7,1,0,0,0,6,
        11,17,23,40,54,57
    ]

class StateParser ( Parser ):

    grammarFileName = "State.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "':'", "'const'", "'enum'", "'='", "'{'", 
                     "'}'", "'var'" ]

    symbolicNames = [ "<INVALID>", "COLON", "CONST", "ENUM", "EQUALS", "LCURLY", 
                      "RCURLY", "VAR", "ID", "WS" ]

    RULE_state = 0
    RULE_const_var_decl = 1
    RULE_enum_type_decl = 2
    RULE_var_decl = 3

    ruleNames =  [ "state", "const_var_decl", "enum_type_decl", "var_decl" ]

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

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.13.1")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class StateContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def EOF(self):
            return self.getToken(StateParser.EOF, 0)

        def enum_type_decl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateParser.Enum_type_declContext)
            else:
                return self.getTypedRuleContext(StateParser.Enum_type_declContext,i)


        def const_var_decl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateParser.Const_var_declContext)
            else:
                return self.getTypedRuleContext(StateParser.Const_var_declContext,i)


        def var_decl(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(StateParser.Var_declContext)
            else:
                return self.getTypedRuleContext(StateParser.Var_declContext,i)


        def getRuleIndex(self):
            return StateParser.RULE_state

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterState" ):
                listener.enterState(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitState" ):
                listener.exitState(self)




    def state(self):

        localctx = StateParser.StateContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_state)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 11
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==3:
                self.state = 8
                self.enum_type_decl()
                self.state = 13
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 17
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==2:
                self.state = 14
                self.const_var_decl()
                self.state = 19
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 21 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 20
                self.var_decl()
                self.state = 23 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==7):
                    break

            self.state = 25
            self.match(StateParser.EOF)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Const_var_declContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def CONST(self):
            return self.getToken(StateParser.CONST, 0)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(StateParser.ID)
            else:
                return self.getToken(StateParser.ID, i)

        def COLON(self):
            return self.getToken(StateParser.COLON, 0)

        def EQUALS(self):
            return self.getToken(StateParser.EQUALS, 0)

        def getRuleIndex(self):
            return StateParser.RULE_const_var_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterConst_var_decl" ):
                listener.enterConst_var_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitConst_var_decl" ):
                listener.exitConst_var_decl(self)




    def const_var_decl(self):

        localctx = StateParser.Const_var_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 2, self.RULE_const_var_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 27
            self.match(StateParser.CONST)
            self.state = 28
            self.match(StateParser.ID)
            self.state = 29
            self.match(StateParser.COLON)
            self.state = 30
            self.match(StateParser.ID)
            self.state = 31
            self.match(StateParser.EQUALS)
            self.state = 32
            self.match(StateParser.ID)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Enum_type_declContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ENUM(self):
            return self.getToken(StateParser.ENUM, 0)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(StateParser.ID)
            else:
                return self.getToken(StateParser.ID, i)

        def LCURLY(self):
            return self.getToken(StateParser.LCURLY, 0)

        def RCURLY(self):
            return self.getToken(StateParser.RCURLY, 0)

        def getRuleIndex(self):
            return StateParser.RULE_enum_type_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterEnum_type_decl" ):
                listener.enterEnum_type_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitEnum_type_decl" ):
                listener.exitEnum_type_decl(self)




    def enum_type_decl(self):

        localctx = StateParser.Enum_type_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_enum_type_decl)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 34
            self.match(StateParser.ENUM)
            self.state = 35
            self.match(StateParser.ID)
            self.state = 36
            self.match(StateParser.LCURLY)
            self.state = 38 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 37
                self.match(StateParser.ID)
                self.state = 40 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==8):
                    break

            self.state = 42
            self.match(StateParser.RCURLY)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Var_declContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def VAR(self):
            return self.getToken(StateParser.VAR, 0)

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(StateParser.ID)
            else:
                return self.getToken(StateParser.ID, i)

        def COLON(self):
            return self.getToken(StateParser.COLON, 0)

        def EQUALS(self):
            return self.getToken(StateParser.EQUALS, 0)

        def LCURLY(self):
            return self.getToken(StateParser.LCURLY, 0)

        def RCURLY(self):
            return self.getToken(StateParser.RCURLY, 0)

        def getRuleIndex(self):
            return StateParser.RULE_var_decl

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterVar_decl" ):
                listener.enterVar_decl(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitVar_decl" ):
                listener.exitVar_decl(self)




    def var_decl(self):

        localctx = StateParser.Var_declContext(self, self._ctx, self.state)
        self.enterRule(localctx, 6, self.RULE_var_decl)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 44
            self.match(StateParser.VAR)
            self.state = 45
            self.match(StateParser.ID)
            self.state = 46
            self.match(StateParser.COLON)
            self.state = 47
            self.match(StateParser.ID)
            self.state = 48
            self.match(StateParser.EQUALS)
            self.state = 49
            self.match(StateParser.ID)
            self.state = 57
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==5:
                self.state = 50
                self.match(StateParser.LCURLY)
                self.state = 52 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                while True:
                    self.state = 51
                    self.match(StateParser.ID)
                    self.state = 54 
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)
                    if not (_la==8):
                        break

                self.state = 56
                self.match(StateParser.RCURLY)


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





