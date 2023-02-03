# Generated from ImpLanguage.g4 by ANTLR 4.11.1
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
        4,1,34,145,2,0,7,0,2,1,7,1,2,2,7,2,2,3,7,3,2,4,7,4,1,0,5,0,12,8,
        0,10,0,12,0,15,9,0,1,0,1,0,1,1,1,1,1,1,1,1,1,1,1,1,1,1,3,1,26,8,
        1,1,1,1,1,1,1,1,1,1,1,1,1,5,1,34,8,1,10,1,12,1,37,9,1,1,2,1,2,1,
        2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,
        2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,1,2,3,2,67,8,2,1,2,1,2,1,2,1,2,
        1,2,1,2,5,2,75,8,2,10,2,12,2,78,9,2,1,3,1,3,1,3,1,3,1,3,1,3,1,3,
        1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,1,3,
        1,3,1,3,1,3,1,3,5,3,107,8,3,10,3,12,3,110,9,3,1,3,1,3,3,3,114,8,
        3,3,3,116,8,3,1,3,1,3,1,3,5,3,121,8,3,10,3,12,3,124,9,3,1,4,1,4,
        1,4,1,4,1,4,1,4,5,4,132,8,4,10,4,12,4,135,9,4,1,4,1,4,3,4,139,8,
        4,1,4,1,4,1,4,1,4,1,4,0,3,2,4,6,5,0,2,4,6,8,0,1,1,0,29,30,164,0,
        13,1,0,0,0,2,25,1,0,0,0,4,66,1,0,0,0,6,115,1,0,0,0,8,125,1,0,0,0,
        10,12,3,8,4,0,11,10,1,0,0,0,12,15,1,0,0,0,13,11,1,0,0,0,13,14,1,
        0,0,0,14,16,1,0,0,0,15,13,1,0,0,0,16,17,3,6,3,0,17,1,1,0,0,0,18,
        19,6,1,-1,0,19,26,5,32,0,0,20,26,5,31,0,0,21,22,5,3,0,0,22,23,3,
        2,1,0,23,24,5,4,0,0,24,26,1,0,0,0,25,18,1,0,0,0,25,20,1,0,0,0,25,
        21,1,0,0,0,26,35,1,0,0,0,27,28,10,3,0,0,28,29,5,1,0,0,29,34,3,2,
        1,4,30,31,10,2,0,0,31,32,5,2,0,0,32,34,3,2,1,3,33,27,1,0,0,0,33,
        30,1,0,0,0,34,37,1,0,0,0,35,33,1,0,0,0,35,36,1,0,0,0,36,3,1,0,0,
        0,37,35,1,0,0,0,38,39,6,2,-1,0,39,67,7,0,0,0,40,41,3,2,1,0,41,42,
        5,5,0,0,42,43,3,2,1,0,43,67,1,0,0,0,44,45,3,2,1,0,45,46,5,6,0,0,
        46,47,3,2,1,0,47,67,1,0,0,0,48,49,3,2,1,0,49,50,5,7,0,0,50,51,3,
        2,1,0,51,67,1,0,0,0,52,53,3,2,1,0,53,54,5,8,0,0,54,55,3,2,1,0,55,
        67,1,0,0,0,56,57,3,2,1,0,57,58,5,9,0,0,58,59,3,2,1,0,59,67,1,0,0,
        0,60,61,5,10,0,0,61,67,3,4,2,4,62,63,5,3,0,0,63,64,3,4,2,0,64,65,
        5,4,0,0,65,67,1,0,0,0,66,38,1,0,0,0,66,40,1,0,0,0,66,44,1,0,0,0,
        66,48,1,0,0,0,66,52,1,0,0,0,66,56,1,0,0,0,66,60,1,0,0,0,66,62,1,
        0,0,0,67,76,1,0,0,0,68,69,10,3,0,0,69,70,5,11,0,0,70,75,3,4,2,4,
        71,72,10,2,0,0,72,73,5,12,0,0,73,75,3,4,2,3,74,68,1,0,0,0,74,71,
        1,0,0,0,75,78,1,0,0,0,76,74,1,0,0,0,76,77,1,0,0,0,77,5,1,0,0,0,78,
        76,1,0,0,0,79,80,6,3,-1,0,80,116,5,13,0,0,81,116,5,14,0,0,82,83,
        5,32,0,0,83,84,5,15,0,0,84,116,3,2,1,0,85,86,5,16,0,0,86,116,3,4,
        2,0,87,88,5,17,0,0,88,89,3,4,2,0,89,90,5,18,0,0,90,91,3,6,3,0,91,
        92,5,19,0,0,92,93,3,6,3,0,93,94,5,20,0,0,94,116,1,0,0,0,95,96,5,
        21,0,0,96,97,3,4,2,0,97,98,5,22,0,0,98,99,3,6,3,0,99,100,5,23,0,
        0,100,116,1,0,0,0,101,113,5,32,0,0,102,103,5,3,0,0,103,108,3,2,1,
        0,104,105,5,24,0,0,105,107,3,2,1,0,106,104,1,0,0,0,107,110,1,0,0,
        0,108,106,1,0,0,0,108,109,1,0,0,0,109,111,1,0,0,0,110,108,1,0,0,
        0,111,112,5,4,0,0,112,114,1,0,0,0,113,102,1,0,0,0,113,114,1,0,0,
        0,114,116,1,0,0,0,115,79,1,0,0,0,115,81,1,0,0,0,115,82,1,0,0,0,115,
        85,1,0,0,0,115,87,1,0,0,0,115,95,1,0,0,0,115,101,1,0,0,0,116,122,
        1,0,0,0,117,118,10,1,0,0,118,119,5,25,0,0,119,121,3,6,3,2,120,117,
        1,0,0,0,121,124,1,0,0,0,122,120,1,0,0,0,122,123,1,0,0,0,123,7,1,
        0,0,0,124,122,1,0,0,0,125,126,5,26,0,0,126,138,5,32,0,0,127,128,
        5,3,0,0,128,133,3,2,1,0,129,130,5,24,0,0,130,132,3,2,1,0,131,129,
        1,0,0,0,132,135,1,0,0,0,133,131,1,0,0,0,133,134,1,0,0,0,134,136,
        1,0,0,0,135,133,1,0,0,0,136,137,5,4,0,0,137,139,1,0,0,0,138,127,
        1,0,0,0,138,139,1,0,0,0,139,140,1,0,0,0,140,141,5,27,0,0,141,142,
        3,6,3,0,142,143,5,28,0,0,143,9,1,0,0,0,13,13,25,33,35,66,74,76,108,
        113,115,122,133,138
    ]

class ImpLanguageParser ( Parser ):

    grammarFileName = "ImpLanguage.g4"

    atn = ATNDeserializer().deserialize(serializedATN())

    decisionsToDFA = [ DFA(ds, i) for i, ds in enumerate(atn.decisionToState) ]

    sharedContextCache = PredictionContextCache()

    literalNames = [ "<INVALID>", "'+'", "'-'", "'('", "')'", "'<='", "'<'", 
                     "'>='", "'>'", "'=='", "'not'", "'and'", "'or'", "'skip'", 
                     "'fail'", "'='", "'assert'", "'if'", "'then'", "'else'", 
                     "'fi'", "'while'", "'do'", "'od'", "','", "';'", "'macro'", 
                     "'begin'", "'end'", "'true'", "'false'" ]

    symbolicNames = [ "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "<INVALID>", "<INVALID>", "<INVALID>", 
                      "<INVALID>", "TRUE", "FALSE", "NUM", "ID", "WS", "COMMENT" ]

    RULE_start = 0
    RULE_aexpr = 1
    RULE_bexpr = 2
    RULE_imp = 3
    RULE_macrodef = 4

    ruleNames =  [ "start", "aexpr", "bexpr", "imp", "macrodef" ]

    EOF = Token.EOF
    T__0=1
    T__1=2
    T__2=3
    T__3=4
    T__4=5
    T__5=6
    T__6=7
    T__7=8
    T__8=9
    T__9=10
    T__10=11
    T__11=12
    T__12=13
    T__13=14
    T__14=15
    T__15=16
    T__16=17
    T__17=18
    T__18=19
    T__19=20
    T__20=21
    T__21=22
    T__22=23
    T__23=24
    T__24=25
    T__25=26
    T__26=27
    T__27=28
    TRUE=29
    FALSE=30
    NUM=31
    ID=32
    WS=33
    COMMENT=34

    def __init__(self, input:TokenStream, output:TextIO = sys.stdout):
        super().__init__(input, output)
        self.checkVersion("4.11.1")
        self._interp = ParserATNSimulator(self, self.atn, self.decisionsToDFA, self.sharedContextCache)
        self._predicates = None




    class StartContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser

        def imp(self):
            return self.getTypedRuleContext(ImpLanguageParser.ImpContext,0)


        def macrodef(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.MacrodefContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.MacrodefContext,i)


        def getRuleIndex(self):
            return ImpLanguageParser.RULE_start

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterStart" ):
                listener.enterStart(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitStart" ):
                listener.exitStart(self)




    def start(self):

        localctx = ImpLanguageParser.StartContext(self, self._ctx, self.state)
        self.enterRule(localctx, 0, self.RULE_start)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 13
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            while _la==26:
                self.state = 10
                self.macrodef()
                self.state = 15
                self._errHandler.sync(self)
                _la = self._input.LA(1)

            self.state = 16
            self.imp(0)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx


    class AexprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return ImpLanguageParser.RULE_aexpr

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class AddContext(AexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.AexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def aexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.AexprContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.AexprContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterAdd" ):
                listener.enterAdd(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitAdd" ):
                listener.exitAdd(self)


    class SubContext(AexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.AexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def aexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.AexprContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.AexprContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSub" ):
                listener.enterSub(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSub" ):
                listener.exitSub(self)


    class CstContext(AexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.AexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def NUM(self):
            return self.getToken(ImpLanguageParser.NUM, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterCst" ):
                listener.enterCst(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitCst" ):
                listener.exitCst(self)


    class VarContext(AexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.AexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(ImpLanguageParser.ID, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterVar" ):
                listener.enterVar(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitVar" ):
                listener.exitVar(self)


    class AparContext(AexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.AexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def aexpr(self):
            return self.getTypedRuleContext(ImpLanguageParser.AexprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterApar" ):
                listener.enterApar(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitApar" ):
                listener.exitApar(self)



    def aexpr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = ImpLanguageParser.AexprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 2
        self.enterRecursionRule(localctx, 2, self.RULE_aexpr, _p)
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 25
            self._errHandler.sync(self)
            token = self._input.LA(1)
            if token in [32]:
                localctx = ImpLanguageParser.VarContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx

                self.state = 19
                self.match(ImpLanguageParser.ID)
                pass
            elif token in [31]:
                localctx = ImpLanguageParser.CstContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 20
                self.match(ImpLanguageParser.NUM)
                pass
            elif token in [3]:
                localctx = ImpLanguageParser.AparContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 21
                self.match(ImpLanguageParser.T__2)
                self.state = 22
                self.aexpr(0)
                self.state = 23
                self.match(ImpLanguageParser.T__3)
                pass
            else:
                raise NoViableAltException(self)

            self._ctx.stop = self._input.LT(-1)
            self.state = 35
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,3,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 33
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,2,self._ctx)
                    if la_ == 1:
                        localctx = ImpLanguageParser.AddContext(self, ImpLanguageParser.AexprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_aexpr)
                        self.state = 27
                        if not self.precpred(self._ctx, 3):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 3)")
                        self.state = 28
                        self.match(ImpLanguageParser.T__0)
                        self.state = 29
                        self.aexpr(4)
                        pass

                    elif la_ == 2:
                        localctx = ImpLanguageParser.SubContext(self, ImpLanguageParser.AexprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_aexpr)
                        self.state = 30
                        if not self.precpred(self._ctx, 2):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 2)")
                        self.state = 31
                        self.match(ImpLanguageParser.T__1)
                        self.state = 32
                        self.aexpr(3)
                        pass

             
                self.state = 37
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,3,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class BexprContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return ImpLanguageParser.RULE_bexpr

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class BgeContext(BexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.BexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def aexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.AexprContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.AexprContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterBge" ):
                listener.enterBge(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitBge" ):
                listener.exitBge(self)


    class BparContext(BexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.BexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def bexpr(self):
            return self.getTypedRuleContext(ImpLanguageParser.BexprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterBpar" ):
                listener.enterBpar(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitBpar" ):
                listener.exitBpar(self)


    class BorContext(BexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.BexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def bexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.BexprContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.BexprContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterBor" ):
                listener.enterBor(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitBor" ):
                listener.exitBor(self)


    class BleContext(BexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.BexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def aexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.AexprContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.AexprContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterBle" ):
                listener.enterBle(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitBle" ):
                listener.exitBle(self)


    class BltContext(BexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.BexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def aexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.AexprContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.AexprContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterBlt" ):
                listener.enterBlt(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitBlt" ):
                listener.exitBlt(self)


    class BandContext(BexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.BexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def bexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.BexprContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.BexprContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterBand" ):
                listener.enterBand(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitBand" ):
                listener.exitBand(self)


    class BcstContext(BexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.BexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def TRUE(self):
            return self.getToken(ImpLanguageParser.TRUE, 0)
        def FALSE(self):
            return self.getToken(ImpLanguageParser.FALSE, 0)

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterBcst" ):
                listener.enterBcst(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitBcst" ):
                listener.exitBcst(self)


    class BgtContext(BexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.BexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def aexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.AexprContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.AexprContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterBgt" ):
                listener.enterBgt(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitBgt" ):
                listener.exitBgt(self)


    class BeqContext(BexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.BexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def aexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.AexprContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.AexprContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterBeq" ):
                listener.enterBeq(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitBeq" ):
                listener.exitBeq(self)


    class BnotContext(BexprContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.BexprContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def bexpr(self):
            return self.getTypedRuleContext(ImpLanguageParser.BexprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterBnot" ):
                listener.enterBnot(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitBnot" ):
                listener.exitBnot(self)



    def bexpr(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = ImpLanguageParser.BexprContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 4
        self.enterRecursionRule(localctx, 4, self.RULE_bexpr, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 66
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,4,self._ctx)
            if la_ == 1:
                localctx = ImpLanguageParser.BcstContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx

                self.state = 39
                _la = self._input.LA(1)
                if not(_la==29 or _la==30):
                    self._errHandler.recoverInline(self)
                else:
                    self._errHandler.reportMatch(self)
                    self.consume()
                pass

            elif la_ == 2:
                localctx = ImpLanguageParser.BleContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 40
                self.aexpr(0)
                self.state = 41
                self.match(ImpLanguageParser.T__4)
                self.state = 42
                self.aexpr(0)
                pass

            elif la_ == 3:
                localctx = ImpLanguageParser.BltContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 44
                self.aexpr(0)
                self.state = 45
                self.match(ImpLanguageParser.T__5)
                self.state = 46
                self.aexpr(0)
                pass

            elif la_ == 4:
                localctx = ImpLanguageParser.BgeContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 48
                self.aexpr(0)
                self.state = 49
                self.match(ImpLanguageParser.T__6)
                self.state = 50
                self.aexpr(0)
                pass

            elif la_ == 5:
                localctx = ImpLanguageParser.BgtContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 52
                self.aexpr(0)
                self.state = 53
                self.match(ImpLanguageParser.T__7)
                self.state = 54
                self.aexpr(0)
                pass

            elif la_ == 6:
                localctx = ImpLanguageParser.BeqContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 56
                self.aexpr(0)
                self.state = 57
                self.match(ImpLanguageParser.T__8)
                self.state = 58
                self.aexpr(0)
                pass

            elif la_ == 7:
                localctx = ImpLanguageParser.BnotContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 60
                self.match(ImpLanguageParser.T__9)
                self.state = 61
                self.bexpr(4)
                pass

            elif la_ == 8:
                localctx = ImpLanguageParser.BparContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 62
                self.match(ImpLanguageParser.T__2)
                self.state = 63
                self.bexpr(0)
                self.state = 64
                self.match(ImpLanguageParser.T__3)
                pass


            self._ctx.stop = self._input.LT(-1)
            self.state = 76
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,6,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    self.state = 74
                    self._errHandler.sync(self)
                    la_ = self._interp.adaptivePredict(self._input,5,self._ctx)
                    if la_ == 1:
                        localctx = ImpLanguageParser.BandContext(self, ImpLanguageParser.BexprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_bexpr)
                        self.state = 68
                        if not self.precpred(self._ctx, 3):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 3)")
                        self.state = 69
                        self.match(ImpLanguageParser.T__10)
                        self.state = 70
                        self.bexpr(4)
                        pass

                    elif la_ == 2:
                        localctx = ImpLanguageParser.BorContext(self, ImpLanguageParser.BexprContext(self, _parentctx, _parentState))
                        self.pushNewRecursionContext(localctx, _startState, self.RULE_bexpr)
                        self.state = 71
                        if not self.precpred(self._ctx, 2):
                            from antlr4.error.Errors import FailedPredicateException
                            raise FailedPredicateException(self, "self.precpred(self._ctx, 2)")
                        self.state = 72
                        self.match(ImpLanguageParser.T__11)
                        self.state = 73
                        self.bexpr(3)
                        pass

             
                self.state = 78
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,6,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class ImpContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser


        def getRuleIndex(self):
            return ImpLanguageParser.RULE_imp

     
        def copyFrom(self, ctx:ParserRuleContext):
            super().copyFrom(ctx)


    class AffContext(ImpContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.ImpContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(ImpLanguageParser.ID, 0)
        def aexpr(self):
            return self.getTypedRuleContext(ImpLanguageParser.AexprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterAff" ):
                listener.enterAff(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitAff" ):
                listener.exitAff(self)


    class ErrContext(ImpContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.ImpContext
            super().__init__(parser)
            self.copyFrom(ctx)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterErr" ):
                listener.enterErr(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitErr" ):
                listener.exitErr(self)


    class AssertContext(ImpContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.ImpContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def bexpr(self):
            return self.getTypedRuleContext(ImpLanguageParser.BexprContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterAssert" ):
                listener.enterAssert(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitAssert" ):
                listener.exitAssert(self)


    class LoopContext(ImpContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.ImpContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def bexpr(self):
            return self.getTypedRuleContext(ImpLanguageParser.BexprContext,0)

        def imp(self):
            return self.getTypedRuleContext(ImpLanguageParser.ImpContext,0)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterLoop" ):
                listener.enterLoop(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitLoop" ):
                listener.exitLoop(self)


    class SkipContext(ImpContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.ImpContext
            super().__init__(parser)
            self.copyFrom(ctx)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSkip" ):
                listener.enterSkip(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSkip" ):
                listener.exitSkip(self)


    class IteContext(ImpContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.ImpContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def bexpr(self):
            return self.getTypedRuleContext(ImpLanguageParser.BexprContext,0)

        def imp(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.ImpContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.ImpContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterIte" ):
                listener.enterIte(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitIte" ):
                listener.exitIte(self)


    class MacrocallContext(ImpContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.ImpContext
            super().__init__(parser)
            self.name = None # Token
            self.copyFrom(ctx)

        def ID(self):
            return self.getToken(ImpLanguageParser.ID, 0)
        def aexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.AexprContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.AexprContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterMacrocall" ):
                listener.enterMacrocall(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitMacrocall" ):
                listener.exitMacrocall(self)


    class SeqContext(ImpContext):

        def __init__(self, parser, ctx:ParserRuleContext): # actually a ImpLanguageParser.ImpContext
            super().__init__(parser)
            self.copyFrom(ctx)

        def imp(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.ImpContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.ImpContext,i)


        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterSeq" ):
                listener.enterSeq(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitSeq" ):
                listener.exitSeq(self)



    def imp(self, _p:int=0):
        _parentctx = self._ctx
        _parentState = self.state
        localctx = ImpLanguageParser.ImpContext(self, self._ctx, _parentState)
        _prevctx = localctx
        _startState = 6
        self.enterRecursionRule(localctx, 6, self.RULE_imp, _p)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 115
            self._errHandler.sync(self)
            la_ = self._interp.adaptivePredict(self._input,9,self._ctx)
            if la_ == 1:
                localctx = ImpLanguageParser.SkipContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx

                self.state = 80
                self.match(ImpLanguageParser.T__12)
                pass

            elif la_ == 2:
                localctx = ImpLanguageParser.ErrContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 81
                self.match(ImpLanguageParser.T__13)
                pass

            elif la_ == 3:
                localctx = ImpLanguageParser.AffContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 82
                self.match(ImpLanguageParser.ID)
                self.state = 83
                self.match(ImpLanguageParser.T__14)
                self.state = 84
                self.aexpr(0)
                pass

            elif la_ == 4:
                localctx = ImpLanguageParser.AssertContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 85
                self.match(ImpLanguageParser.T__15)
                self.state = 86
                self.bexpr(0)
                pass

            elif la_ == 5:
                localctx = ImpLanguageParser.IteContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 87
                self.match(ImpLanguageParser.T__16)
                self.state = 88
                self.bexpr(0)
                self.state = 89
                self.match(ImpLanguageParser.T__17)
                self.state = 90
                self.imp(0)
                self.state = 91
                self.match(ImpLanguageParser.T__18)
                self.state = 92
                self.imp(0)
                self.state = 93
                self.match(ImpLanguageParser.T__19)
                pass

            elif la_ == 6:
                localctx = ImpLanguageParser.LoopContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 95
                self.match(ImpLanguageParser.T__20)
                self.state = 96
                self.bexpr(0)
                self.state = 97
                self.match(ImpLanguageParser.T__21)
                self.state = 98
                self.imp(0)
                self.state = 99
                self.match(ImpLanguageParser.T__22)
                pass

            elif la_ == 7:
                localctx = ImpLanguageParser.MacrocallContext(self, localctx)
                self._ctx = localctx
                _prevctx = localctx
                self.state = 101
                localctx.name = self.match(ImpLanguageParser.ID)
                self.state = 113
                self._errHandler.sync(self)
                la_ = self._interp.adaptivePredict(self._input,8,self._ctx)
                if la_ == 1:
                    self.state = 102
                    self.match(ImpLanguageParser.T__2)
                    self.state = 103
                    self.aexpr(0)
                    self.state = 108
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)
                    while _la==24:
                        self.state = 104
                        self.match(ImpLanguageParser.T__23)
                        self.state = 105
                        self.aexpr(0)
                        self.state = 110
                        self._errHandler.sync(self)
                        _la = self._input.LA(1)

                    self.state = 111
                    self.match(ImpLanguageParser.T__3)


                pass


            self._ctx.stop = self._input.LT(-1)
            self.state = 122
            self._errHandler.sync(self)
            _alt = self._interp.adaptivePredict(self._input,10,self._ctx)
            while _alt!=2 and _alt!=ATN.INVALID_ALT_NUMBER:
                if _alt==1:
                    if self._parseListeners is not None:
                        self.triggerExitRuleEvent()
                    _prevctx = localctx
                    localctx = ImpLanguageParser.SeqContext(self, ImpLanguageParser.ImpContext(self, _parentctx, _parentState))
                    self.pushNewRecursionContext(localctx, _startState, self.RULE_imp)
                    self.state = 117
                    if not self.precpred(self._ctx, 1):
                        from antlr4.error.Errors import FailedPredicateException
                        raise FailedPredicateException(self, "self.precpred(self._ctx, 1)")
                    self.state = 118
                    self.match(ImpLanguageParser.T__24)
                    self.state = 119
                    self.imp(2) 
                self.state = 124
                self._errHandler.sync(self)
                _alt = self._interp.adaptivePredict(self._input,10,self._ctx)

        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.unrollRecursionContexts(_parentctx)
        return localctx


    class MacrodefContext(ParserRuleContext):
        __slots__ = 'parser'

        def __init__(self, parser, parent:ParserRuleContext=None, invokingState:int=-1):
            super().__init__(parent, invokingState)
            self.parser = parser
            self.name = None # Token

        def imp(self):
            return self.getTypedRuleContext(ImpLanguageParser.ImpContext,0)


        def ID(self):
            return self.getToken(ImpLanguageParser.ID, 0)

        def aexpr(self, i:int=None):
            if i is None:
                return self.getTypedRuleContexts(ImpLanguageParser.AexprContext)
            else:
                return self.getTypedRuleContext(ImpLanguageParser.AexprContext,i)


        def getRuleIndex(self):
            return ImpLanguageParser.RULE_macrodef

        def enterRule(self, listener:ParseTreeListener):
            if hasattr( listener, "enterMacrodef" ):
                listener.enterMacrodef(self)

        def exitRule(self, listener:ParseTreeListener):
            if hasattr( listener, "exitMacrodef" ):
                listener.exitMacrodef(self)




    def macrodef(self):

        localctx = ImpLanguageParser.MacrodefContext(self, self._ctx, self.state)
        self.enterRule(localctx, 8, self.RULE_macrodef)
        self._la = 0 # Token type
        try:
            self.enterOuterAlt(localctx, 1)
            self.state = 125
            self.match(ImpLanguageParser.T__25)
            self.state = 126
            localctx.name = self.match(ImpLanguageParser.ID)
            self.state = 138
            self._errHandler.sync(self)
            _la = self._input.LA(1)
            if _la==3:
                self.state = 127
                self.match(ImpLanguageParser.T__2)
                self.state = 128
                self.aexpr(0)
                self.state = 133
                self._errHandler.sync(self)
                _la = self._input.LA(1)
                while _la==24:
                    self.state = 129
                    self.match(ImpLanguageParser.T__23)
                    self.state = 130
                    self.aexpr(0)
                    self.state = 135
                    self._errHandler.sync(self)
                    _la = self._input.LA(1)

                self.state = 136
                self.match(ImpLanguageParser.T__3)


            self.state = 140
            self.match(ImpLanguageParser.T__26)
            self.state = 141
            self.imp(0)
            self.state = 142
            self.match(ImpLanguageParser.T__27)
        except RecognitionException as re:
            localctx.exception = re
            self._errHandler.reportError(self, re)
            self._errHandler.recover(self, re)
        finally:
            self.exitRule()
        return localctx



    def sempred(self, localctx:RuleContext, ruleIndex:int, predIndex:int):
        if self._predicates == None:
            self._predicates = dict()
        self._predicates[1] = self.aexpr_sempred
        self._predicates[2] = self.bexpr_sempred
        self._predicates[3] = self.imp_sempred
        pred = self._predicates.get(ruleIndex, None)
        if pred is None:
            raise Exception("No predicate with index:" + str(ruleIndex))
        else:
            return pred(localctx, predIndex)

    def aexpr_sempred(self, localctx:AexprContext, predIndex:int):
            if predIndex == 0:
                return self.precpred(self._ctx, 3)
         

            if predIndex == 1:
                return self.precpred(self._ctx, 2)
         

    def bexpr_sempred(self, localctx:BexprContext, predIndex:int):
            if predIndex == 2:
                return self.precpred(self._ctx, 3)
         

            if predIndex == 3:
                return self.precpred(self._ctx, 2)
         

    def imp_sempred(self, localctx:ImpContext, predIndex:int):
            if predIndex == 4:
                return self.precpred(self._ctx, 1)
         




