from abc import abstractmethod
from dataclasses import dataclass

##############
### Syntax ###
##############
import z3

"""
Definition ident := string.
"""
Ident = str

Z = int

"""
Inductive aexpr : Type :=
  | Var : ident -> aexpr
  | Cst : Z -> aexpr
  | Add : aexpr -> aexpr -> aexpr
  | Sub : aexpr -> aexpr -> aexpr.
"""


@dataclass(frozen=True)
class Aexpr:
    @abstractmethod
    def to_smt(self) -> z3.ArithRef:
        raise NotImplementedError()


@dataclass(frozen=True)
class Var(Aexpr):
    ident: Ident

    def __str__(self):
        return self.ident

    def to_smt(self) -> z3.ArithRef:
        return z3.Int(self.ident)


@dataclass(frozen=True)
class Cst(Aexpr):
    num: Z

    def __str__(self):
        return str(self.num)

    def to_smt(self) -> z3.ArithRef:
        return z3.IntVal(self.num)


@dataclass(frozen=True)
class Add(Aexpr):
    left: Aexpr
    right: Aexpr

    def __str__(self):
        return f"({self.left} + {self.right})"

    def to_smt(self) -> z3.ArithRef:
        return self.left.to_smt() + self.right.to_smt()


@dataclass(frozen=True)
class Sub(Aexpr):
    left: Aexpr
    right: Aexpr

    def __str__(self):
        return f"({self.left} - {self.right})"

    def to_smt(self) -> z3.ArithRef:
        return self.left.to_smt() - self.right.to_smt()


"""
Inductive bexpr : Type :=
  | Bcst  : bool -> bexpr
  | Ble   : aexpr -> aexpr -> bexpr
  | Beq   : aexpr -> aexpr -> bexpr
  | Bnot  : bexpr -> bexpr
  | Band  : bexpr -> bexpr -> bexpr.
"""


@dataclass(frozen=True)
class Bexpr:
    @abstractmethod
    def to_smt(self) -> z3.BoolRef:
        raise NotImplementedError()


@dataclass(frozen=True)
class Bcst(Bexpr):
    b: bool

    def __str__(self):
        return str(self.b).lower()

    def to_smt(self) -> z3.BoolRef:
        return z3.BoolVal(self.b)


@dataclass(frozen=True)
class Ble(Bexpr):
    left: Aexpr
    right: Aexpr

    def __str__(self):
        return f"{self.left} <= {self.right}"

    def to_smt(self) -> z3.BoolRef:
        return self.left.to_smt() <= self.right.to_smt()


@dataclass(frozen=True)
class Beq(Bexpr):
    left: Aexpr
    right: Aexpr

    def __str__(self):
        return f"{self.left} == {self.right}"

    def to_smt(self) -> z3.BoolRef:
        return self.left.to_smt() == self.right.to_smt()


@dataclass(frozen=True)
class Bnot(Bexpr):
    expr: Bexpr

    def __str__(self):
        return f"not ({self.expr})"

    def to_smt(self) -> z3.BoolRef:
        return z3.Not(self.expr.to_smt())


@dataclass(frozen=True)
class Band(Bexpr):
    left: Bexpr
    right: Bexpr

    def __str__(self):
        return f"{self.left} and {self.right}"

    def to_smt(self) -> z3.BoolRef:
        return z3.And(self.left.to_smt(), self.right.to_smt())


def Bor(b1: Bexpr, b2: Bexpr) -> Bexpr:
    """
    Definition Bor (b1 b2 : bexpr) := Bnot (Band (Bnot b1) (Bnot b2)).
    """

    return Bnot(Band(Bnot(b1), Bnot(b2)))


"""
Inductive IMP : Type :=
  | Skip  : IMP
  | Ite   : bexpr -> IMP -> IMP -> IMP
  | Seq   : IMP -> IMP -> IMP
  | Aff   : string -> aexpr -> IMP
  | Err   : IMP
  | Loop  : bexpr -> IMP -> IMP.
"""


@dataclass(frozen=True)
class Imp:
    pass


@dataclass(frozen=True)
class Skip(Imp):
    pass

    def __str__(self):
        return "skip"


@dataclass(frozen=True)
class Ite(Imp):
    guard: Bexpr
    then_branch: Imp
    else_branch: Imp

    def __str__(self):
        return f"if {self.guard} then {self.then_branch} else {self.else_branch} fi"


@dataclass(frozen=True)
class Seq(Imp):
    first: Imp
    second: Imp

    def __str__(self):
        return f"{self.first} ; {self.second}"


@dataclass(frozen=True)
class Aff(Imp):
    var: Ident
    expr: Aexpr

    def __str__(self):
        return f"{self.var} = {self.expr}"


@dataclass(frozen=True)
class Err(Imp):
    pass

    def __str__(self):
        return "err"


@dataclass(frozen=True)
class Loop(Imp):
    guard: Bexpr
    body: Imp

    def __str__(self):
        return f"while {self.guard} do {self.body} od"


def Assert(c: Bexpr) -> Imp:
    """
    Definition Assert c := Ite c Skip Err.
    """
    return Ite(c, Skip(), Err())


def is_error(p: Imp) -> bool:
    """
    (** Executable check for erroneous state *)
    Fixpoint is_error (p : IMP) : bool :=
      match p with
      | Err => true
      | Seq p _ => is_error p
      | _ => false
      end.
    """
    match p:
        case Err():
            return True
        case Seq(p, _):
            return is_error(p)
        case _:
            return False
