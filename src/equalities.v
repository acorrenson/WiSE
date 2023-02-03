(** * Types With Equalities *)

Class Eq (A : Type) := EQ {
  eq_op : A -> A -> Prop;
}.

Infix "≡" := eq_op (at level 80).

Definition bijection (A B : Type) `{Eq A} `{Eq B} (f : A -> B) (g : B -> A) :=
  (forall a, g (f a) ≡ a) /\ (forall b, f (g b) ≡ b).

Definition isomorph (A B : Type) `{Eq A} `{Eq B} :=
  exists f g, bijection A B f g.

Infix "≃" := isomorph (at level 80).