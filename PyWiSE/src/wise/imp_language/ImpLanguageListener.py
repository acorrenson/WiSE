# Generated from ImpLanguage.g4 by ANTLR 4.11.1
from antlr4 import *
if __name__ is not None and "." in __name__:
    from .ImpLanguageParser import ImpLanguageParser
else:
    from ImpLanguageParser import ImpLanguageParser

# This class defines a complete listener for a parse tree produced by ImpLanguageParser.
class ImpLanguageListener(ParseTreeListener):

    # Enter a parse tree produced by ImpLanguageParser#start.
    def enterStart(self, ctx:ImpLanguageParser.StartContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#start.
    def exitStart(self, ctx:ImpLanguageParser.StartContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#add.
    def enterAdd(self, ctx:ImpLanguageParser.AddContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#add.
    def exitAdd(self, ctx:ImpLanguageParser.AddContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#sub.
    def enterSub(self, ctx:ImpLanguageParser.SubContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#sub.
    def exitSub(self, ctx:ImpLanguageParser.SubContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#cst.
    def enterCst(self, ctx:ImpLanguageParser.CstContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#cst.
    def exitCst(self, ctx:ImpLanguageParser.CstContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#var.
    def enterVar(self, ctx:ImpLanguageParser.VarContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#var.
    def exitVar(self, ctx:ImpLanguageParser.VarContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#apar.
    def enterApar(self, ctx:ImpLanguageParser.AparContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#apar.
    def exitApar(self, ctx:ImpLanguageParser.AparContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#bge.
    def enterBge(self, ctx:ImpLanguageParser.BgeContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#bge.
    def exitBge(self, ctx:ImpLanguageParser.BgeContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#bpar.
    def enterBpar(self, ctx:ImpLanguageParser.BparContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#bpar.
    def exitBpar(self, ctx:ImpLanguageParser.BparContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#bor.
    def enterBor(self, ctx:ImpLanguageParser.BorContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#bor.
    def exitBor(self, ctx:ImpLanguageParser.BorContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#ble.
    def enterBle(self, ctx:ImpLanguageParser.BleContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#ble.
    def exitBle(self, ctx:ImpLanguageParser.BleContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#blt.
    def enterBlt(self, ctx:ImpLanguageParser.BltContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#blt.
    def exitBlt(self, ctx:ImpLanguageParser.BltContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#band.
    def enterBand(self, ctx:ImpLanguageParser.BandContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#band.
    def exitBand(self, ctx:ImpLanguageParser.BandContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#bcst.
    def enterBcst(self, ctx:ImpLanguageParser.BcstContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#bcst.
    def exitBcst(self, ctx:ImpLanguageParser.BcstContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#bgt.
    def enterBgt(self, ctx:ImpLanguageParser.BgtContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#bgt.
    def exitBgt(self, ctx:ImpLanguageParser.BgtContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#beq.
    def enterBeq(self, ctx:ImpLanguageParser.BeqContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#beq.
    def exitBeq(self, ctx:ImpLanguageParser.BeqContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#bnot.
    def enterBnot(self, ctx:ImpLanguageParser.BnotContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#bnot.
    def exitBnot(self, ctx:ImpLanguageParser.BnotContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#aff.
    def enterAff(self, ctx:ImpLanguageParser.AffContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#aff.
    def exitAff(self, ctx:ImpLanguageParser.AffContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#err.
    def enterErr(self, ctx:ImpLanguageParser.ErrContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#err.
    def exitErr(self, ctx:ImpLanguageParser.ErrContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#assert.
    def enterAssert(self, ctx:ImpLanguageParser.AssertContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#assert.
    def exitAssert(self, ctx:ImpLanguageParser.AssertContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#loop.
    def enterLoop(self, ctx:ImpLanguageParser.LoopContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#loop.
    def exitLoop(self, ctx:ImpLanguageParser.LoopContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#skip.
    def enterSkip(self, ctx:ImpLanguageParser.SkipContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#skip.
    def exitSkip(self, ctx:ImpLanguageParser.SkipContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#ite.
    def enterIte(self, ctx:ImpLanguageParser.IteContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#ite.
    def exitIte(self, ctx:ImpLanguageParser.IteContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#macrocall.
    def enterMacrocall(self, ctx:ImpLanguageParser.MacrocallContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#macrocall.
    def exitMacrocall(self, ctx:ImpLanguageParser.MacrocallContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#seq.
    def enterSeq(self, ctx:ImpLanguageParser.SeqContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#seq.
    def exitSeq(self, ctx:ImpLanguageParser.SeqContext):
        pass


    # Enter a parse tree produced by ImpLanguageParser#macrodef.
    def enterMacrodef(self, ctx:ImpLanguageParser.MacrodefContext):
        pass

    # Exit a parse tree produced by ImpLanguageParser#macrodef.
    def exitMacrodef(self, ctx:ImpLanguageParser.MacrodefContext):
        pass



del ImpLanguageParser