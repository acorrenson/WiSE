from typing import Dict, Optional, Tuple, cast, Generator, TypeVar, Union

import antlr4
from antlr4 import InputStream, ParserRuleContext, RuleContext
from antlr4.Token import CommonToken

from wise.helpers import eassert
from wise.imp import (
    Imp,
    Aexpr,
    Skip,
    Var,
    Aff,
    Cst,
    Add,
    Sub,
    Ite,
    Ble,
    Err,
    Bcst,
    Beq,
    Bnot,
    Band,
    Bor,
    Seq,
    Loop,
    Assert,
    Bexpr,
)
from wise.imp_language.ImpLanguageLexer import ImpLanguageLexer
from wise.imp_language.ImpLanguageListener import ImpLanguageListener
from wise.imp_language.ImpLanguageParser import ImpLanguageParser


class BailPrintErrorStrategy(antlr4.BailErrorStrategy):
    def recover(self, recognizer: antlr4.Parser, e: antlr4.RecognitionException):
        recognizer._errHandler.reportError(recognizer, e)
        super().recover(recognizer, e)


def parse_tree_text(elem: RuleContext | CommonToken) -> str:
    if isinstance(elem, CommonToken):
        return elem.text
    else:
        return elem.getText()


class ImpEmitter(ImpLanguageListener):
    def __init__(self):
        self.__result: Optional[Imp] = None

        self.aexprs: Dict[ParserRuleContext, Aexpr] = {}
        self.bexprs: Dict[ParserRuleContext, Bexpr] = {}
        self.progs: Dict[ParserRuleContext, Imp] = {}
        self.macros: Dict[str, Tuple[Tuple[Var], Imp]] = {}

    def result(self):
        assert self.__result is not None
        return self.__result

    def exitStart(self, ctx: ImpLanguageParser.StartContext):
        self.__result = self.progs[ctx.imp()]

    def exitVar(self, ctx: ImpLanguageParser.VarContext):
        self.aexprs[ctx] = Var(parse_tree_text(ctx.ID()))

    def exitCst(self, ctx: ImpLanguageParser.CstContext):
        self.aexprs[ctx] = Cst(int(parse_tree_text(ctx.NUM())))

    def exitAdd(self, ctx: ImpLanguageParser.AddContext):
        self.aexprs[ctx] = Add(
            self.aexprs[ctx.aexpr(0)], self.aexprs[ctx.aexpr(1)]
        )

    def exitSub(self, ctx: ImpLanguageParser.SubContext):
        self.aexprs[ctx] = Sub(
            self.aexprs[ctx.aexpr(0)], self.aexprs[ctx.aexpr(1)]
        )

    def exitApar(self, ctx: ImpLanguageParser.AparContext):
        self.aexprs[ctx] = self.aexprs[ctx.aexpr()]

    def exitBcst(self, ctx: ImpLanguageParser.BcstContext):
        self.bexprs[ctx] = Bcst(ctx.FALSE() is None)

    def exitBle(self, ctx: ImpLanguageParser.BleContext):
        self.bexprs[ctx] = Ble(
            self.aexprs[ctx.aexpr(0)], self.aexprs[ctx.aexpr(1)]
        )

    def exitBlt(self, ctx: ImpLanguageParser.BltContext):
        left = self.aexprs[ctx.aexpr(0)]
        right = self.aexprs[ctx.aexpr(1)]

        # a < b <==> a <= b and not a == b
        self.bexprs[ctx] = Band(Ble(left, right), Bnot(Beq(left, right)))

    def exitBge(self, ctx: ImpLanguageParser.BgeContext):
        left = self.aexprs[ctx.aexpr(0)]
        right = self.aexprs[ctx.aexpr(1)]

        # a >= b <==> b <= a
        self.bexprs[ctx] = Ble(right, left)

    def exitBgt(self, ctx: ImpLanguageParser.BgeContext):
        left = self.aexprs[ctx.aexpr(0)]
        right = self.aexprs[ctx.aexpr(1)]

        # a > b <==> b <= a and not a == b
        self.bexprs[ctx] = Band(Ble(right, left), Bnot(Beq(left, right)))

    def exitBeq(self, ctx: ImpLanguageParser.BeqContext):
        self.bexprs[ctx] = Beq(
            self.aexprs[ctx.aexpr(0)], self.aexprs[ctx.aexpr(1)]
        )

    def exitBnot(self, ctx: ImpLanguageParser.BnotContext):
        self.bexprs[ctx] = Bnot(self.bexprs[ctx.bexpr()])

    def exitBand(self, ctx: ImpLanguageParser.BandContext):
        self.bexprs[ctx] = Band(
            self.bexprs[ctx.bexpr(0)], self.bexprs[ctx.bexpr(1)]
        )

    def exitBor(self, ctx: ImpLanguageParser.BorContext):
        self.bexprs[ctx] = Bor(
            self.bexprs[ctx.bexpr(0)], self.bexprs[ctx.bexpr(1)]
        )

    def exitBpar(self, ctx: ImpLanguageParser.BparContext):
        self.bexprs[ctx] = self.bexprs[ctx.bexpr()]

    def exitSkip(self, ctx: ImpLanguageParser.SkipContext):
        self.progs[ctx] = Skip()

    def exitIte(self, ctx: ImpLanguageParser.IteContext):
        self.progs[ctx] = Ite(
            self.bexprs[ctx.bexpr()],
            self.progs[ctx.imp(0)],
            self.progs[ctx.imp(1)],
        )

    def exitSeq(self, ctx: ImpLanguageParser.SeqContext):
        self.progs[ctx] = Seq(self.progs[ctx.imp(0)], self.progs[ctx.imp(1)])

    def exitAff(self, ctx: ImpLanguageParser.AffContext):
        self.progs[ctx] = Aff(parse_tree_text(ctx.ID()), self.aexprs[ctx.aexpr()])

    def exitAssert(self, ctx: ImpLanguageParser.AssertContext):
        self.progs[ctx] = Assert(self.bexprs[ctx.bexpr()])

    def exitErr(self, ctx: ImpLanguageParser.ErrContext):
        self.progs[ctx] = Err()

    def exitLoop(self, ctx: ImpLanguageParser.LoopContext):
        self.progs[ctx] = Loop(self.bexprs[ctx.bexpr()], self.progs[ctx.imp()])

    def exitMacrodef(self, ctx: ImpLanguageParser.MacrodefContext):
        name = parse_tree_text(ctx.name)
        params = tuple([cast(Var, self.aexprs[var]) for var in ctx.aexpr()])
        assert all(isinstance(elem, Var) for elem in params)
        prog = self.progs[ctx.imp()]
        assert all(
            not isinstance(elem, Var) or elem in params for elem in walk_imp(prog)
        )

        self.macros[name] = (params, prog)

    def exitMacrocall(self, ctx: ImpLanguageParser.MacrocallContext):
        name = parse_tree_text(ctx.name)
        args = [self.aexprs[param] for param in ctx.aexpr()]
        assert name in self.macros
        assert len(args) == len(self.macros[name][0])
        self.progs[ctx] = replace_imp(
            self.macros[name][1], dict(zip(self.macros[name][0], args))
        )


T = TypeVar("T", bound=Union[Aexpr, Bexpr, Imp])


def replace_imp(orig: T, repl_dict: Dict) -> T:
    if orig in repl_dict:
        return repl_dict[orig]

    match orig:
        case Var(_) | Cst(_) | Bcst(_) | Skip() | Err():
            return orig
        case Bnot(a):
            return Bnot(replace_imp(a, repl_dict))
        case Add(a, b):
            return Add(replace_imp(a, repl_dict), replace_imp(b, repl_dict))
        case Sub(a, b):
            return Sub(replace_imp(a, repl_dict), replace_imp(b, repl_dict))
        case Ble(a, b):
            return Ble(replace_imp(a, repl_dict), replace_imp(b, repl_dict))
        case Beq(a, b):
            return Beq(replace_imp(a, repl_dict), replace_imp(b, repl_dict))
        case Band(a, b):
            return Band(replace_imp(a, repl_dict), replace_imp(b, repl_dict))
        case Seq(a, b):
            return Seq(replace_imp(a, repl_dict), replace_imp(b, repl_dict))
        case Aff(var, expr):
            new_lhs = replace_imp(Var(var), repl_dict)
            assert isinstance(new_lhs, Var)
            return Aff(new_lhs.ident, replace_imp(expr, repl_dict))
        case Ite(g, t, e):
            return Ite(
                replace_imp(g, repl_dict),
                replace_imp(t, repl_dict),
                replace_imp(e, repl_dict),
            )
        case Loop(g, b):
            return Loop(replace_imp(g, repl_dict), replace_imp(b, repl_dict))
        case _:
            assert False


def walk_imp(elem: Aexpr | Bexpr | Imp) -> Generator[Aexpr | Bexpr | Imp, None, None]:
    yield elem
    match elem:
        case Var(_) | Cst(_) | Bcst(_) | Skip() | Err():
            pass
        case Bnot(a):
            yield from walk_imp(a)
        case Add(a, b) | Sub(a, b) | Ble(a, b) | Beq(a, b) | Band(a, b) | Seq(a, b):
            yield from walk_imp(a)
            yield from walk_imp(b)
        case Aff(var, expr):
            yield Var(var)
            yield from walk_imp(expr)
        case Ite(g, t, e):
            yield from walk_imp(g)
            yield from walk_imp(t)
            yield from walk_imp(e)
        case Loop(g, b):
            yield from walk_imp(g)
            yield from walk_imp(b)
        case _:
            assert False


def parse_imp(inp: str) -> Imp:
    lexer = ImpLanguageLexer(InputStream(inp))
    parser = ImpLanguageParser(antlr4.CommonTokenStream(lexer))
    parser._errHandler = BailPrintErrorStrategy()
    imp_emitter = ImpEmitter()
    antlr4.ParseTreeWalker().walk(imp_emitter, parser.start())
    return imp_emitter.result()


def parse_bexpr(inp: str) -> Bexpr:
    lexer = ImpLanguageLexer(InputStream(inp))
    parser = ImpLanguageParser(antlr4.CommonTokenStream(lexer))
    parser._errHandler = BailPrintErrorStrategy()
    imp_emitter = ImpEmitter()
    ctx = parser.bexpr()
    antlr4.ParseTreeWalker().walk(imp_emitter, ctx)
    return imp_emitter.bexprs[ctx]
