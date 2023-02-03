From Coq Require Import List.
Import ListNotations.

(** Reduce a list of optional values
    to a single optional values.
*)
Fixpoint reduce {A} (f : A -> A -> A) (l : list (option A)) : option A :=
  match l with
  | [] => None
  | None::_ => None
  | [Some x] => Some x
  | Some x::xs =>
    option_map (fun y => f x y) (reduce f xs)
  end.

(** Apply [f] element-wise but fail if any of the applications of [f] returns [None] *)
Fixpoint map_opt {A B} (f : A -> option B) (l : list A) : option (list B) :=
  match l with
  | [] => None
  | x::xs =>
    match f x with
    | None => None
    | Some fx => option_map (fun xs => fx::xs) (map_opt f xs)
    end
  end.

(** Check that a list of optional values does not contain [None] *)
Fixpoint all_some {A} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | None::_ => None
  | Some x::xs => option_map (fun xs => x::xs) (all_some xs)
  end.

(** Find the first [Some] element of a list of optional values *)
Fixpoint first {A} (l : list (option A)) : option A :=
  match l with
  | [] => None
  | Some x::xs => Some x
  | None::xs => first xs
  end.