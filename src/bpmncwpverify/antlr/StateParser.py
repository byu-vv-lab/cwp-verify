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
        4,1,9,60,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,1,0,5,0,12,8,0,
        10,0,12,0,15,9,0,1,0,5,0,18,8,0,10,0,12,0,21,9,0,1,0,4,0,24,8,0,
        11,0,12,0,25,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,2,4,2,37,8,2,11,2,
        12,2,38,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,4,1,4,1,4,1,4,1,4,1,4,1,4,
        1,4,1,4,1,4,3,4,58,8,4,1,4,0,0,5,0,2,4,6,8,0,0,59,0,13,1,0,0,0,2,
        29,1,0,0,0,4,36,1,0,0,0,6,40,1,0,0,0,8,47,1,0,0,0,10,12,3,2,1,0,
        11,10,1,0,0,0,12,15,1,0,0,0,13,11,1,0,0,0,13,14,1,0,0,0,14,19,1,
        0,0,0,15,13,1,0,0,0,16,18,3,6,3,0,17,16,1,0,0,0,18,21,1,0,0,0,19,
        17,1,0,0,0,19,20,1,0,0,0,20,23,1,0,0,0,21,19,1,0,0,0,22,24,3,8,4,
        0,23,22,1,0,0,0,24,25,1,0,0,0,25,23,1,0,0,0,25,26,1,0,0,0,26,27,
        1,0,0,0,27,28,5,0,0,1,28,1,1,0,0,0,29,30,5,3,0,0,30,31,5,8,0,0,31,
        32,5,5,0,0,32,33,3,4,2,0,33,34,5,6,0,0,34,3,1,0,0,0,35,37,5,8,0,
        0,36,35,1,0,0,0,37,38,1,0,0,0,38,36,1,0,0,0,38,39,1,0,0,0,39,5,1,
        0,0,0,40,41,5,2,0,0,41,42,5,8,0,0,42,43,5,1,0,0,43,44,5,8,0,0,44,
        45,5,4,0,0,45,46,5,8,0,0,46,7,1,0,0,0,47,48,5,7,0,0,48,49,5,8,0,
        0,49,50,5,1,0,0,50,51,5,8,0,0,51,52,5,4,0,0,52,57,5,8,0,0,53,54,
        5,5,0,0,54,55,3,4,2,0,55,56,5,6,0,0,56,58,1,0,0,0,57,53,1,0,0,0,
        57,58,1,0,0,0,58,9,1,0,0,0,5,13,19,25,38,57
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
    RULE_enum_type_decl = 1
    RULE_id_set = 2
    RULE_const_var_decl = 3
    RULE_var_decl = 4

    ruleNames =  [ "state", "enum_type_decl", "id_set", "const_var_decl", 
                   "var_decl" ]

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
            self.state = 13
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==3:
                self.state = 10
                self.enum_type_decl()
                self.state = 15
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 19
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==2:
                self.state = 16
                self.const_var_decl()
                self.state = 21
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 23 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 22
                self.var_decl()
                self.state = 25 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==7):
                    break

            self.state = 27
            self.match(StateParser.EOF)
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

        def ID(self):
            return self.getToken(StateParser.ID, 0)

        def LCURLY(self):
            return self.getToken(StateParser.LCURLY, 0)

        def id_set(self):
            return self.getTypedRuleContext(StateParser.Id_setContext,0)


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
        self.enterRule(localctx, 2, self.RULE_enum_type_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 29
            self.match(StateParser.ENUM)
            self.state = 30
            self.match(StateParser.ID)
            self.state = 31
            self.match(StateParser.LCURLY)
            self.state = 32
            self.id_set()
            self.state = 33
            self.match(StateParser.RCURLY)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class Id_setContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def ID(self, i:int=None):
            if i is None:
                return self.getTokens(StateParser.ID)
            else:
                return self.getToken(StateParser.ID, i)

        def getRuleIndex(self):
            return StateParser.RULE_id_set

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterId_set" ):
                listener.enterId_set(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitId_set" ):
                listener.exitId_set(self)




    def id_set(self):

        localctx = StateParser.Id_setContext(self, self._ctx, self.state)
        self.enterRule(localctx, 4, self.RULE_id_set)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 36 
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while True:
                self.state = 35
                self.match(StateParser.ID)
                self.state = 38 
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                if not (_la==8):
                    break

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
        self.enterRule(localctx, 6, self.RULE_const_var_decl)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 40
            self.match(StateParser.CONST)
            self.state = 41
            self.match(StateParser.ID)
            self.state = 42
            self.match(StateParser.COLON)
            self.state = 43
            self.match(StateParser.ID)
            self.state = 44
            self.match(StateParser.EQUALS)
            self.state = 45
            self.match(StateParser.ID)
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

        def id_set(self):
            return self.getTypedRuleContext(StateParser.Id_setContext,0)


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
        self.enterRule(localctx, 8, self.RULE_var_decl)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 47
            self.match(StateParser.VAR)
            self.state = 48
            self.match(StateParser.ID)
            self.state = 49
            self.match(StateParser.COLON)
            self.state = 50
            self.match(StateParser.ID)
            self.state = 51
            self.match(StateParser.EQUALS)
            self.state = 52
            self.match(StateParser.ID)
            self.state = 57
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==5:
                self.state = 53
                self.match(StateParser.LCURLY)
                self.state = 54
                self.id_set()
                self.state = 55
                self.match(StateParser.RCURLY)


        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx





