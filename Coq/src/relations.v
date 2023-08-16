From Coq Require Import Classes.RelationClasses.

Section Sequences.

Variable A : Type.
Variable R : A -> A -> Prop.

Inductive star : A -> A -> Prop :=
  | star_refl x :
    star x x
  | star_step x y z :
    R x y -> star y z -> star x z.

Lemma star_one :
  forall x y, R x y -> star x y.
Proof.
  intros * H.
  eapply (star_step _ _ _ H); auto.
  apply star_refl.
Qed.

Global Instance star_reflexive :
  Reflexive star.
Proof.
  intros x. apply star_refl.
Qed.

Global Instance star_trans :
  Transitive star.
Proof.
  intros x y z H1 H2.
  induction H1 in z, H2 |-*; auto.
  apply (star_step _ _ _ H).
  apply (IHstar _ H2).
Qed.

Inductive starr: A -> A -> Prop :=
  | starr_refl x :
    starr x x
  | starr_step x y z :
    starr x y -> R y z -> starr x z.

Global Instance starr_trans :
  Transitive starr.
Proof.
  intros x y z H1 H2.
  induction H2; auto.
  specialize (IHstarr H1).
  econstructor; eauto.
Qed.

Global Instance starr_reflexive :
  Reflexive starr.
Proof.
  intros x. econstructor.
Qed.

Theorem starr_star:
  forall x y, star x y <-> starr x y.
Proof.
  intros. split; intros.
  - induction H as [|? ? ? H1 H2 IH].
    + apply starr_refl.
    + etransitivity; eauto.
      now repeat econstructor.
  - induction H as [|? ? ? H1 H2 IH].
    + reflexivity.
    + etransitivity; eauto.
      now repeat econstructor.
Qed.

End Sequences.

Section Simulation.

Definition simulation {A B}
  (RA : A -> A -> Prop)
  (RB : B -> B -> Prop)
  (sim : A -> B -> Prop) : Prop :=
  forall a1 a2, RA a1 a2 -> forall b1, sim a1 b1 -> exists b2, RB b1 b2 /\ sim a2 b2.

Theorem star_simulation {A B} (RA : A -> A -> Prop) (RB : B -> B -> Prop):
  forall sim, simulation RA RB sim -> simulation (star _ RA) (star _ RB) sim.
Proof.
  intros * H.
  refine (star_ind _ _ _ _ _).
  - intros a1 b1 H1. now exists b1.
  - intros a1 a2 a3 Ha1 Ha2 IH b1 Hsim1.
    specialize (H _ _ Ha1 _ Hsim1) as (b2 & Hb1 & Hsim2).
    specialize (IH b2 Hsim2) as (b3 & Hb2 & Hsim3).
    exists b3; split; auto.
    etransitivity; eauto.
    now apply star_one.
Qed.

End Simulation.

Arguments star {_}.
Arguments star_step {_} {_}.
Arguments star_refl {_} {_}.
Arguments star_one {_} {_}.
Arguments star_reflexive {_} {_}.
Arguments star_trans {_} {_}.
