import functools
from functools import reduce
from typing import Optional, cast, TypeVar, Callable

import sympy

from wise.imp import *
from wise.symex import SymStore, Id, NonEmptySymStore

T = TypeVar("T")


def eassert(expr: T, assertion: Callable[[T], bool]) -> T:
    assert assertion(expr)
    return expr


def is_unsat(expr: Bexpr) -> bool:
    solver = z3.Solver()
    solver.add(expr.to_smt())
    return solver.check() == z3.unsat


S = TypeVar("S", Aexpr, Bexpr)


def simplify_expr(expr: S) -> S:
    result = convert_z3_expr(z3.simplify(expr.to_smt()))
    return expr if result is None else result


def simplify_sympy(expr: S) -> sympy.Expr | Boolean:
    return expr.to_sym().simplify()


def simplify_store(store: SymStore) -> SymStore:
    if isinstance(store, Id):
        return store
    assert isinstance(store, NonEmptySymStore)
    return NonEmptySymStore(
        store.var, simplify_expr(store.val), simplify_store(store.s)
    )


def simplify_store_sympy(store: SymStore) -> SymStore:
    if isinstance(store, Id):
        return store
    assert isinstance(store, NonEmptySymStore)
    return NonEmptySymStore(
        store.var, simplify_sympy(store.val), simplify_store_sympy(store.s)
    )


def convert_z3_expr(expr: z3.ExprRef) -> Optional[Aexpr | Bexpr]:
    if z3.is_int_value(expr):
        return Cst(cast(z3.IntVal, expr).as_long())
    elif z3.is_const(expr):
        return Var(str(expr))

    children_results = list(map(convert_z3_expr, expr.children()))
    if any(child_result is None for child_result in children_results):
        return None

    match expr.decl().kind():
        case z3.Z3_OP_TRUE:
            return Bcst(True)
        case z3.Z3_OP_FALSE:
            return Bcst(False)
        case z3.Z3_OP_LE:
            return Ble(*children_results)
        case z3.Z3_OP_LT:
            return Band(Ble(*children_results), Bnot(Beq(*children_results)))
        case z3.Z3_OP_GE:
            return Ble(*reversed(list(children_results)))
        case z3.Z3_OP_GT:
            return Band(
                Ble(*reversed(list(children_results))), Bnot(Beq(*children_results))
            )
        case z3.Z3_OP_EQ:
            return Beq(*children_results)
        case z3.Z3_OP_NOT:
            return Bnot(*children_results)
        case z3.Z3_OP_AND:
            return functools.reduce(
                lambda acc, elem: cast(Bexpr, Band(elem, acc)),
                reversed(children_results),
            )
        case z3.Z3_OP_OR:
            return functools.reduce(
                lambda acc, elem: cast(Bexpr, Bor(elem, acc)),
                reversed(children_results),
            )
        case z3.Z3_OP_ADD:
            return Add(*children_results)
        case z3.Z3_OP_SUB:
            return Sub(*children_results)
        case _:
            return None
