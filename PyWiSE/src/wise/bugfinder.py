"""
(** A task list is a list of programs to be executed in a given symbolic state. *)
Definition tasks := list (sym_state * IMP).
"""
from dataclasses import dataclass
from typing import List, Tuple, Optional

from toolz import curry

from wise.helpers import is_unsat, simplify_expr, simplify_store
from wise.imp import (
    Imp,
    Seq,
    Bexpr,
    Skip,
    Aff,
    Err,
    Ite,
    Band,
    Bnot,
    Loop,
    is_error,
    Bcst,
)
from wise.streams import Stream, stream_map, scons
from wise.symex import SymState, SymStore, sym_update, sym_aeval, sym_beval, Id

# (** A task list is a list of programs to be executed in a given symbolic state. *)
# Definition tasks := list sym_state.
Tasks = List[SymState]

"""
(** A [status] corresponds to the current state of the bugfinding loop *)
Inductive status :=
  | BugFound (s : sym_state)
  | Pending
  | Finished.
"""


@dataclass(frozen=True)
class Status:
    pass


@dataclass(frozen=True)
class BugFound(Status):
    s: SymState


@dataclass(frozen=True)
class Pending(Status):
    pass


@dataclass(frozen=True)
class Finished(Status):
    pass


@curry
def then_do(q: Imp, task: SymState) -> SymState:
    """
    Definition then_do q '(((path, env), p) : sym_state) :=
      ((path, env), Seq p q).
    """
    path, env, p = task
    return path, env, Seq(p, q)


def exec_task(path: Bexpr, env: SymStore, prog: Imp) -> List[SymState]:
    """
    (** Executing a task according to [sym_step] *)
    Fixpoint exec_task path env prog : list sym_state :=
      match prog with
      | Skip => []
      | Aff x e =>
        [(path, sym_update env x (sym_aeval env e), Skip)]
      | Err => []
      | Ite b p1 p2 =>
        [
          (Band path (sym_beval env b), env, p1);
          (Band path (Bnot (sym_beval env b)), env, p2)
        ]
      | Loop b p =>
        [
          (Band path (sym_beval env b), env, Seq p (Loop b p));
          (Band path (Bnot (sym_beval env b)), env, Skip)
        ]
      | Seq Skip p2 => [(path, env, p2)]
      | Seq p1 p2 =>
        List.map (then_do p2) (exec_task path env p1)
      end.
    """

    match prog:
        case Skip():
            return []
        case Aff(x, e):
            return [(path, sym_update(env, x, sym_aeval(env, e)), Skip())]
        case Err():
            return []
        case Ite(b, p1, p2):
            return [
                (Band(path, sym_beval(env, b)), env, p1),
                (Band(path, Bnot(sym_beval(env, b))), env, p2),
            ]
        case Loop(b, p):
            return [
                (Band(path, sym_beval(env, b)), env, Seq(p, Loop(b, p))),
                (Band(path, Bnot(sym_beval(env, b))), env, Skip()),
            ]
        case Seq(Skip(), p2):
            return [(path, env, p2)]
        case Seq(p1, p2):
            return list(map(then_do(p2), exec_task(path, env, p1)))

    assert False


def run(l: Tasks) -> Stream[Optional[SymState]]:
    """
    (** Bugfinding loop: at every iteration, a task is choosen and then executed.
        If the execution results in an error, a [BugFound] message is
        emitted. If executing the task terminates in a state [s] without error,
        a message [Clear s] is emitted. If executing the task generates a list [l] of subtasks,
        then the loop signals that further computations are pending and add [l] to the worklist.
        Finally, if the task list is empty, the loop emits the token [Finished] continuously.
    *)
    CoFixpoint run (l : tasks) : stream (option sym_state) :=
      match l with
      | [] => scons None (run [])
      | ((path, env), prog)::next =>
        let next_next := exec_task path env prog in
        scons (Some (path, env, prog)) (run (next ++ next_next))
      end.
    """

    match l:
        case []:
            return scons(None, lambda: run([]))
        case [(path, env, prog), *next_]:
            if not is_unsat(path):
                next_next = exec_task(path, env, prog)
                return scons((path, env, prog), lambda: run(next_ + next_next))
            else:
                return run(next_)


def run_depth_first(l: Tasks) -> Stream[Optional[SymState]]:
    """
    A depth-first version of `run` as implemented by early symbolic executors like DART.
    """

    match l:
        case []:
            return scons(None, lambda: run_depth_first([]))
        case [(path, env, prog), *next_]:
            # Note: The only thing changed here is the order of `next_` and `next_next`
            #       in the recursive call to `run_depth_first`. This turns the procedure
            #       into a depth-first search.
            if not is_unsat(path):
                next_next = exec_task(path, env, prog)
                return scons(
                    (path, env, prog), lambda: run_depth_first(next_next + next_)
                )
            else:
                return run_depth_first(next_)


def display(n: Optional[SymState]) -> Status:
    """
    Definition display (st : option sym_state) : status :=
      match st with
      | None => Finished
      | Some (path, env, prog) =>
        if is_error prog then BugFound (path, env, prog)
        else Pending
      end.
    """
    match n:
        case None:
            return Finished()
        case (path, env, prog):
            return BugFound((path, env, prog)) if is_error(prog) else Pending()


def init(p: Imp) -> List[SymState]:
    """
    Definition init (p : IMP) : list sym_state :=
      [((Bcst true, id), p)].
    """
    return [(Bcst(True), Id(), p)]


def find_bugs(p: Imp) -> Stream[Status]:
    """
    Definition find_bugs (p : IMP) : stream status :=
      map display (run (init p)).
    """

    return stream_map(display, run(init(p)))


def find_bugs_depth_first(p: Imp, cond: Optional[Bexpr] = None) -> Stream[Status]:
    """
    A depth-first version of `find_bugs` using `run_depth_first`.
    """

    return stream_map(
        display, run_depth_first(init(p) if cond is None else init_assuming(p, cond))
    )


def init_assuming(p: Imp, cond: Bexpr) -> List[SymState]:
    """
    Definition init_assuming (p : IMP) (cond : bexpr) :=
      [(cond, id, p)].
    """

    return [(cond, Id(), p)]


def find_bugs_assuming(p: Imp, cond: Bexpr) -> Stream[Status]:
    """
    Definition find_bugs_assuming (p : IMP) (cond : bexpr) : stream status :=
      map display (run (init_assuming p cond)).
    """

    return stream_map(display, run(init_assuming(p, cond)))
