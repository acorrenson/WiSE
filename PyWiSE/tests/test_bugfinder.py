import unittest
from typing import List, cast

from wise.bugfinder import (
    find_bugs,
    BugFound,
    find_bugs_depth_first,
    find_bugs_assuming,
    Finished,
)
from wise.helpers import is_unsat, simplify_expr, simplify_store
from wise.imp import *
from wise.parser import parse_imp, parse_bexpr
from wise.streams import peek
from wise.symex import NonEmptySymStore, Id


class TestBugfinder(unittest.TestCase):
    def test_simple_bug(self):
        """
        Example my_prog :=
          Ite
            (Beq (Var "x"%string) (Cst 0%Z))
            Err
            Skip.

        Compute (peek 10 (find_bugs my_prog)).
        """
        my_prog = Ite(Beq(Var("x"), Cst(0)), Err(), Skip())

        bug_path = Band(
            left=Bcst(b=True),
            right=Beq(left=Var(ident="x"), right=Cst(num=0)),
        )
        bug_store = Id()
        bug = BugFound((bug_path, bug_store, Err()))

        self.assertIn(bug, peek(10, find_bugs(my_prog)))

    def test_simple_bug_2(self):
        my_prog = Ite(Beq(Var("x"), Cst(0)), Seq(Aff("x", Cst(17)), Err()), Skip())

        bug_path = Band(
            left=Bcst(b=True),
            right=Beq(left=Var(ident="x"), right=Cst(num=0)),
        )
        bug_store = NonEmptySymStore(var="x", val=Cst(num=17), s=Id())
        bug = BugFound((bug_path, bug_store, Err()))

        self.assertIn(bug, peek(10, find_bugs(my_prog)))

    def test_gcd_correct(self):
        with open("../examples/gcd_correct.imp", "r") as f:
            gcd_correct = parse_imp(f.read())

        assumptions = parse_bexpr("a > 0 and b > 0")
        result = peek(100, find_bugs_assuming(gcd_correct, assumptions))

        self.assertTrue(not any(isinstance(elem, BugFound) for elem in result))

    def test_gcd_buggy(self):
        with open("../examples/gcd_buggy.imp", "r") as f:
            gcd_buggy = parse_imp(f.read())

        assumptions = parse_bexpr("a > 0 and b > 0")
        result = peek(60, find_bugs_assuming(gcd_buggy, assumptions))
        bugs: List[BugFound] = cast(
            List[BugFound], list(filter(BugFound.__instancecheck__, result))
        )

        # 0 <= a and not (0 == a) and 0 <= b and not (0 == b) and not (a <= 0) and
        #   not (b <= 0) and not (a == b) and not (a <= b) and not (0 <= (a + b)
        #   and 0 <= b and b <= 0 and not (b == 0))
        simplified_bug_path = Band(
            Ble(Cst(0), Var("a")),
            Band(
                Bnot(Beq(Cst(0), Var("a"))),
                Band(
                    Ble(Cst(0), Var("b")),
                    Band(
                        Bnot(Beq(Cst(0), Var("b"))),
                        Band(
                            Bnot(Ble(Var("a"), Cst(0))),
                            Band(
                                Bnot(Ble(Var("b"), Cst(0))),
                                Band(
                                    Bnot(Beq(Var("a"), Var("b"))),
                                    Band(
                                        Bnot(Ble(Var("a"), Var("b"))),
                                        Bnot(
                                            Band(
                                                Ble(Cst(0), Add(Var("a"), Var("b"))),
                                                Band(
                                                    Ble(Cst(0), Var("b")),
                                                    Band(
                                                        Ble(Var("b"), Cst(0)),
                                                        Bnot(Beq(Var("b"), Cst(0))),
                                                    ),
                                                ),
                                            )
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )

        self.assertFalse(is_unsat(simplified_bug_path))

        # {}{old_a -> a}{old_b -> b}{a -> (a + b)}
        bug_store = NonEmptySymStore(
            "a",
            Add(Var("a"), Var("b")),
            NonEmptySymStore(
                "old_b", Var("b"), NonEmptySymStore("old_a", Var("a"), Id())
            ),
        )

        self.assertTrue(
            any(
                simplify_expr(elem.s[0]) == simplified_bug_path
                and elem.s[1] == bug_store
                for elem in bugs
            )
        )

    def test_true_assertion(self):
        prog = parse_imp("x = -1 ; assert x <= 0")
        result = peek(20, find_bugs(prog))
        self.assertTrue(
            all(
                not isinstance(elem, BugFound)
                or elem.s[0] == Band(Bcst(True), Bnot(Ble(Cst(-1), Cst(0))))  # unsat
                for elem in result
            )
        )

    def test_nested_loop(self):
        with open("../examples/nested_loop.imp", "r") as f:
            prog = parse_imp(f.read())

        result_breadth_first = peek(14, find_bugs(prog))
        result_depth_first = peek(100, find_bugs_depth_first(prog))

        def contains_satisfiable_bug(results):
            return any(
                isinstance(elem, BugFound) and not is_unsat(elem.s[0])
                for elem in results
            )

        self.assertTrue(contains_satisfiable_bug(result_breadth_first))
        self.assertFalse(contains_satisfiable_bug(result_depth_first))

    def test_integer_square_root(self):
        with open("../examples/integer_sqrt_buggy.imp", "r") as f:
            prog = parse_imp(f.read())

        result = peek(250, find_bugs(prog))

        def contains_satisfiable_bug(results):
            return any(
                isinstance(elem, BugFound) and not is_unsat(elem.s[0])
                # not `path ==> x <= 0`
                and not is_unsat(Bnot(Bor(Bnot(elem.s[0]), Ble(Var("x"), Cst(0)))))
                for elem in results
            )

        self.assertTrue(contains_satisfiable_bug(result))

    def test_factorial_correct(self):
        with open("../examples/factorial.imp", "r") as f:
            prog = parse_imp(f.read())

        assumption = parse_bexpr("n >= 2")
        result = peek(300, find_bugs_assuming(prog, assumption))

        assert not any(isinstance(elem, BugFound) for elem in result)

    def test_factorial_correct_exhaustive_with_assumption(self):
        with open("../examples/factorial.imp", "r") as f:
            prog = parse_imp(f.read())

        assumption = parse_bexpr("n >= 2 and n < 4")
        result = peek(200, find_bugs_assuming(prog, assumption))
        self.assertTrue(isinstance(result[-1], Finished))

    def test_factorial_buggy(self):
        with open("../examples/factorial_buggy.imp", "r") as f:
            prog = parse_imp(f.read())

        assumption = parse_bexpr("n >= 2")
        result = peek(300, find_bugs_assuming(prog, assumption))
        bugs: List[BugFound] = cast(
            List[BugFound], list(filter(BugFound.__instancecheck__, result))
        )

        # 2 <= n and 1 <= n and not (3 <= n)
        simplified_bug_path = Band(
            Ble(Cst(2), Var("n")),
            Band(Ble(Cst(1), Var("n")), Bnot(Ble(Cst(3), Var("n")))),
        )

        # {}{factorial -> 1}{i -> 1}{mul_result -> 1}{_i -> 1}{factorial -> 1}{i -> 2}
        # {mul_result -> 1}{_i -> 1}{mul_result -> 3}{_i -> 2}{factorial -> 3}{i -> 3}
        # {_i -> 2}{_m -> 3}{_d -> 0}{_d -> 1}{_m -> 1}
        simplified_store = NonEmptySymStore(
            "_m",
            Cst(1),
            NonEmptySymStore(
                "_d",
                Cst(1),
                NonEmptySymStore(
                    "_d",
                    Cst(0),
                    NonEmptySymStore(
                        "_m",
                        Cst(3),
                        NonEmptySymStore(
                            "_i",
                            Cst(2),
                            NonEmptySymStore(
                                "i",
                                Cst(3),
                                NonEmptySymStore(
                                    "factorial",
                                    Cst(3),
                                    NonEmptySymStore(
                                        "_i",
                                        Cst(2),
                                        NonEmptySymStore(
                                            "mul_result",
                                            Cst(3),
                                            NonEmptySymStore(
                                                "_i",
                                                Cst(1),
                                                NonEmptySymStore(
                                                    "mul_result",
                                                    Cst(1),
                                                    NonEmptySymStore(
                                                        "i",
                                                        Cst(2),
                                                        NonEmptySymStore(
                                                            "factorial",
                                                            Cst(1),
                                                            NonEmptySymStore(
                                                                "_i",
                                                                Cst(1),
                                                                NonEmptySymStore(
                                                                    "mul_result",
                                                                    Cst(1),
                                                                    NonEmptySymStore(
                                                                        "i",
                                                                        Cst(1),
                                                                        NonEmptySymStore(
                                                                            "factorial",
                                                                            Cst(1),
                                                                            Id(),
                                                                        ),
                                                                    ),
                                                                ),
                                                            ),
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )

        self.assertTrue(
            any(
                simplify_expr(bug.s[0]) == simplified_bug_path
                and simplify_store(bug.s[1]) == simplified_store
                for bug in bugs
            )
        )

    def Xtest_is_prime(self):
        # TODO
        with open("../examples/is_prime.imp", "r") as f:
            prog = parse_imp(f.read())

        for elem in peek(300, find_bugs(prog)):
            if not isinstance(elem, BugFound):
                continue

            if is_unsat(elem.s[0]):
                continue

            print(simplify_expr(elem.s[0]))


if __name__ == "__main__":
    unittest.main()
