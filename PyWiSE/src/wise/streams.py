from typing import Generator, TypeVar, Callable, List

T = TypeVar("T")
S = TypeVar("S")

"""
CoInductive stream (A : Type) : Type :=
  | scons (x : A) (xs : stream A) : stream A.
"""
Stream = Generator[T, None, None]


def scons(x: T, xs: Callable[[], Stream[T]]) -> Stream[T]:
    yield x
    yield from xs()


def peek(n: int, s: Stream[T]) -> List[T]:
    """
    (** Peek the first [n] elements of a stream *)
    Fixpoint peek {A} (n : nat) (s : stream A) : list A :=
      match n, s with
      | 0, _ => []
      | S n, scons x xs => x::peek n xs
      end.
    """
    match n:
        case 0:
            return []
        case _:
            return [next(s)] + peek(n - 1, s)


def stream_map(f: Callable[[S], T], s: Stream[S]) -> Stream[T]:
    """
    (** Apply a function to a stream elementwise *)
    CoFixpoint map {A B} (f : A -> B) (s : stream A) : stream B :=
      match s with
      | scons x xs => scons (f x) (map f xs)
      end.
    """
    for elem in s:
        yield f(elem)
