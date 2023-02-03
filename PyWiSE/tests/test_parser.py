import unittest

from wise.imp import *
from wise.parser import parse_imp, parse_bexpr


class TestParser(unittest.TestCase):
    def test_simple_programs(self):
        self.assertEqual(Skip(), parse_imp("skip"))
        self.assertEqual(
            Aff("x", Add(Cst(17), Cst(23))),
            parse_imp("x = 17 + 23"),
        )
        self.assertEqual(
            Aff("x", Sub(Cst(17), Add(Cst(23), Var("y")))),
            parse_imp("x = 17 - (23 + y)"),
        )
        self.assertEqual(
            Aff("x", Add(Sub(Cst(17), Cst(23)), Var("y"))),
            parse_imp("x = (17 - 23) + y"),
        )
        self.assertEqual(
            Ite(
                Band(Bnot(Beq(Var("x"), Var("y"))), Beq(Var("x"), Var("y"))),
                Skip(),
                Err(),
            ),
            parse_imp("if not x == y and x == y then skip else fail fi"),
        )
        self.assertEqual(
            Ite(
                Bnot(Band(Beq(Var("x"), Var("y")), Beq(Var("x"), Cst(17)))),
                Skip(),
                Err(),
            ),
            parse_imp("if not(x == y and x == 17) then skip else fail fi"),
        )
        self.assertEqual(
            Seq(Seq(Aff("a", Var("b")), Aff("c", Cst(17))), Err()),
            parse_imp("a = b ; c = 17 ; fail"),
        )
        self.assertEqual(Loop(Bcst(True), Skip()), parse_imp("while true do skip od"))
        self.assertEqual(Ite(Bcst(False), Skip(), Err()), parse_imp("assert false"))

    def test_nonparametric_macro(self):
        result = parse_imp("macro useless begin skip end useless")
        self.assertEqual(Skip(), result)

    def test_macro_calls_in_macro(self):
        result = parse_imp(
            """
        macro useless 
        begin skip end
         
        macro useless2 
        begin useless end
        
        useless2"""
        )

        self.assertEqual(Skip(), result)

    def test_subadd_macro(self):
        result = parse_imp(
            """
        macro subadd1(x, y)
        begin
          x = x - y ;
          x = x + 1
        end
        subadd1(a, b);
        a = 0"""
        )

        expected = Seq(
            Seq(Aff("a", Sub(Var("a"), Var("b"))), Aff("a", Add(Var("a"), Cst(1)))),
            Aff("a", Cst(0)),
        )

        self.assertEqual(expected, result)

    def test_parse_bexpr(self):
        result = parse_bexpr("a >= b and not a==b")
        expected = Band(Ble(Var("b"), Var("a")), Bnot(Beq(Var("a"), Var("b"))))
        self.assertEqual(expected, result)


if __name__ == "__main__":
    unittest.main()
