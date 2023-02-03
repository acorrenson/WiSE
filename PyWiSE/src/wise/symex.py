"""
(** A symbolic state is a path constraint expressed as a [bexpr] and a symbolic store *)
Definition sym_state := (bexpr * sym_store)%type.
"""
from abc import abstractmethod
from dataclasses import dataclass
from typing import Tuple

from wise.imp import Bexpr, Ident, Aexpr, Var, Cst, Add, Sub, Bcst, Ble, Beq, Band, \
    Bnot, Imp


@dataclass
class SymStore:
    """
    (** Symbolic stores are simply substitutions (of variable with expressions) *)
    Definition sym_store :=
      ident -> aexpr.
    """

    @abstractmethod
    def __call__(self, x: Ident) -> Aexpr:
        raise NotImplementedError()


@dataclass
class Id(SymStore):
    """
    Definition id : sym_store := fun x => Var x.
    """

    def __call__(self, x: Ident) -> Aexpr:
        return Var(x)

    def __str__(self):
        return "{}"


@dataclass
class NonEmptySymStore(SymStore):
    var: Ident
    val: Aexpr
    s: SymStore = Id()

    def __call__(self, x: Ident) -> Aexpr:
        return self.val if x == self.var else self.s(x)

    def __str__(self):
        return f"{self.s}{{{self.var} -> {self.val}}}"


# (** A symbolic state is a path constraint expressed as a [bexpr],
#     a symbolic store and a program to execute
# *)
# Definition sym_state := (bexpr * sym_store * IMP)%type.
SymState = Tuple[Bexpr, SymStore, Imp]


def sym_update(s: SymStore, x: Ident, e: Aexpr) -> SymStore:
    """
    (** Update a symbolic store *)
    Definition sym_update (s : sym_store) (x : ident) (e : aexpr) : sym_store :=
      fun y => if string_dec y x then e else s y.
    """
    return NonEmptySymStore(x, e, s)


def sym_aeval(s: SymStore, e: Aexpr) -> Aexpr:
    """
    (** Symbolic evaluation of arithmetic expressions *)
    Fixpoint sym_aeval (s : sym_store) (e : aexpr) : aexpr :=
      match e with
      | Var x => s x
      | Cst c => e
      | Add e1 e2 => Add (sym_aeval s e1) (sym_aeval s e2)
      | Sub e1 e2 => Sub (sym_aeval s e1) (sym_aeval s e2)
      end.
    """

    match e:
        case Var(x):
            return s(x)
        case Cst(_):
            return e
        case Add(e1, e2):
            return Add(sym_aeval(s, e1), sym_aeval(s, e2))
        case Sub(e1, e2):
            return Sub(sym_aeval(s, e1), sym_aeval(s, e2))


def sym_beval(s: SymStore, e: Bexpr) -> Bexpr:
    """
    (** Symbolic evaluation of boolean expressions *)
    Fixpoint sym_beval (s : sym_store) (e : bexpr) : bexpr :=
      match e with
      | Bcst b      => e
      | Ble e1 e2   => Ble (sym_aeval s e1) (sym_aeval s e2)
      | Beq e1 e2   => Beq (sym_aeval s e1) (sym_aeval s e2)
      | Band e1 e2  => Band (sym_beval s e1) (sym_beval s e2)
      | Bnot e      => Bnot (sym_beval s e)
      end.
    """
    match e:
        case Bcst(_):
            return e
        case Ble(e1, e2):
            return Ble(sym_aeval(s, e1), sym_aeval(s, e2))
        case Beq(e1, e2):
            return Beq(sym_aeval(s, e1), sym_aeval(s, e2))
        case Band(e1, e2):
            return Band(sym_beval(s, e1), sym_beval(s, e2))
        case Bnot(e):
            return Bnot(sym_beval(s, e))
