From WiSE Require Import imp.
From Coq Require Import ZArith String Bool Lia.

(** * A Naive Constraint Solver/simplifier *)

(** Smart constructor to build an [Add] term *)
Definition mk_add (a1 : aexpr) (a2 : aexpr) : aexpr :=
  match a1, a2 with
  | Cst c1, Cst c2 => Cst (c1 + c2)%Z
  | _, Sub a2_1 a2_2 =>
    if aeq a1 a2_2 then a2_1
    else Add a1 a2
  | _, _ => Add a1 a2
  end.

  (** Smart constructor to build a [Sub] term *)
Definition mk_sub (a1 : aexpr) (a2 : aexpr) : aexpr :=
  match a1, a2 with
  | Cst c1, Cst c2 => Cst (c1 - c2)%Z
  | _, Add a2_1 a2_2 =>
    if aeq a1 a2_1 then Sub (Cst 0) a2_2
    else if aeq a1 a2_2 then Sub (Cst 0) a2_1
    else Sub a1 a2
  | _, _ => Sub a1 a2
  end.

(** Basic, non-exhaustive simplification of arithmetic expressions *)
Fixpoint asimp (a: aexpr) : aexpr :=
  match a with
  | Cst _   => a
  | Var _   => a
  | Add a b => mk_add (asimp a) (asimp b)
  | Sub a b => mk_sub (asimp a) (asimp b)
  end.

Lemma mk_add_correct:
  forall env a1 a2, aeval env (Add a1 a2) = aeval env (mk_add a1 a2).
Proof.
  intros. Opaque aeq.
  destruct a1, a2; simpl; auto.
  all:
    destruct aeq eqn:Heq; auto;
    apply aeq_spec in Heq as <-; simpl; lia.
Qed.

Lemma mk_sub_correct:
  forall env a1 a2, aeval env (Sub a1 a2) = aeval env (mk_sub a1 a2).
Proof.
  intros. Opaque aeq.
  destruct a1, a2; simpl; auto.
  all:
    destruct (aeq _ a2_1) eqn:Heq1; [
      apply aeq_spec in Heq1 as <-; simpl; lia |
    ];
    destruct (aeq _ a2_2) eqn:Heq2; [
      apply aeq_spec in Heq2 as <-; simpl; lia |
    ]; reflexivity.
Qed.

Theorem asimp_correct:
  forall env a, aeval env a = aeval env (asimp a).
Proof.
  induction a; simpl; auto.
  + rewrite IHa1, IHa2.
    now rewrite <- mk_add_correct.
  + rewrite IHa1, IHa2.
    now rewrite <- mk_sub_correct.
Qed.

Definition mk_and (b1 b2 : bexpr) : bexpr :=
  match b1, b2 with
  | Bcst false, _ | _, Bcst false => Bcst false   (* Null Law *)
  | Bcst true, _ => b2                            (* Identity Law *)
  | _, Bcst true => b1                            (* Identity Law *)
  | lhs, Bnot rhs =>
    if beq lhs rhs 
    then Bcst false                               (* Inverse Law *)
    else Band lhs (Bnot rhs)
  | Bnot lhs, rhs =>
    if beq lhs rhs 
    then Bcst false                               (* Inverse Law *)
    else Band (Bnot lhs) rhs
  | _, _ =>
    if beq b1 b2
    then b1                                       (* Idempotent Law *)
    else Band b1 b2
  end.

Definition mk_not (b : bexpr) : bexpr :=
  match b with
  | Bnot lhs => lhs
  | Bcst true => Bcst false
  | Bcst false => Bcst true
  | lhs => Bnot lhs
  end.

(** Simplification of boolean formulas *)
Fixpoint bsimp (b : bexpr) : bexpr :=
  match b with
  | Bcst _ => b
  | Band lhs rhs => mk_and (bsimp lhs) (bsimp rhs)
  | Bnot lhs => mk_not (bsimp lhs)
  | Ble x y =>
    match asimp x, asimp y with
    | Cst x, Cst y => Bcst (x <=? y)%Z
    | x, y => Ble x y
    end
  | Beq x y =>
    match asimp x, asimp y with
    | Cst x, Cst y => Bcst (x =? y)%Z
    | x, y => if aeq x y then Bcst true else Beq x y
    end
  end.

Lemma mk_and_correct:
  forall env b1 b2,
    beval env (Band b1 b2) = beval env (mk_and b1 b2).
Proof.
  intros. Opaque beq.
  destruct b1, b2; simpl; auto.
  all: try now destruct b.
  all: try now destruct b, b0.
  all: try now destruct b; rewrite Bool.andb_comm.
  - destruct beq eqn:Heq1; auto.
    apply beq_spec in Heq1 as [=->->].
    now rewrite Bool.andb_diag.
  - destruct beq eqn:Heq1; auto.
    apply beq_spec in Heq1 as <-.
    apply Bool.andb_negb_r.
  - destruct beq eqn:Heq1; auto.
    apply beq_spec in Heq1 as [=->->].
    now rewrite Bool.andb_diag.
  - destruct beq eqn:Heq1; auto.
    apply beq_spec in Heq1 as <-.
    apply Bool.andb_negb_r.
  - destruct beq eqn:Heq1; auto.
    apply beq_spec in Heq1 as ->.
    apply Bool.andb_negb_l.
  - destruct beq eqn:Heq1; auto.
    apply beq_spec in Heq1 as ->.
    apply Bool.andb_negb_l.
  - destruct beq eqn:Heq1; auto.
    apply beq_spec in Heq1 as <-; simpl.
    rewrite Bool.negb_involutive.
    apply Bool.andb_negb_l.
  - destruct beq eqn:Heq1; auto.
    apply beq_spec in Heq1 as ->; simpl.
    apply Bool.andb_negb_l.
  - destruct beq eqn:Heq1; auto.
    apply beq_spec in Heq1 as <-; simpl.
    apply Bool.andb_negb_r.
  - destruct beq eqn:Heq1; auto.
    apply beq_spec in Heq1 as [=->->].
    now rewrite Bool.andb_diag.
Qed.

Lemma mk_not_correct:
  forall env b,
    beval env (Bnot b) = beval env (mk_not b).
Proof.
  intros env []; simpl; auto.
  - now destruct b.
  - now rewrite Bool.negb_involutive.
Qed.

(** Correctness of [bsimp] *)
Lemma bsimp_correct:
  forall env b,
    beval env (bsimp b) = beval env b.
Proof.
  Opaque asimp aeq beq.
  induction b; simpl; auto.
  - destruct (asimp a) eqn:Heq1, (asimp a0) eqn:Heq2.
    all: now rewrite (asimp_correct _ a), (asimp_correct _ a0), Heq1, Heq2.
  - destruct (asimp a) eqn:Heq1, (asimp a0) eqn:Heq2.
    all: try now rewrite (asimp_correct _ a), (asimp_correct _ a0), Heq1, Heq2.
    destruct aeq eqn:Heq.
    apply aeq_spec in Heq as [=->].
    rewrite (asimp_correct _ a), (asimp_correct _ a0), Heq1, Heq2.
    simpl. now rewrite Z.eqb_refl.
    now rewrite (asimp_correct _ a), (asimp_correct _ a0), Heq1, Heq2.
    destruct aeq eqn:Heq.
    apply aeq_spec in Heq as [=->->].
    rewrite (asimp_correct _ a), (asimp_correct _ a0), Heq1, Heq2.
    simpl. now rewrite Z.eqb_refl.
    now rewrite (asimp_correct _ a), (asimp_correct _ a0), Heq1, Heq2.
    destruct aeq eqn:Heq.
    apply aeq_spec in Heq as [=->->].
    rewrite (asimp_correct _ a), (asimp_correct _ a0), Heq1, Heq2.
    simpl. now rewrite Z.eqb_refl.
    now rewrite (asimp_correct _ a), (asimp_correct _ a0), Heq1, Heq2.
  - rewrite <- mk_not_correct; simpl.
    now rewrite IHb.
  - rewrite <- mk_and_correct; simpl.
    now rewrite IHb1, IHb2.
Qed.

Inductive sat : Type :=
  | SAT
  | UNSAT
  | MAYBE.

(** An extremely naive sover *)
Definition solver (b : bexpr) : sat :=
  match bsimp b with
  | Bcst true => SAT
  | Bcst false => UNSAT
  | _ => MAYBE
  end.

(** [solver] is correct (but absolutely not complete) *)
Lemma solver_correct:
  forall b,
    (solver b = UNSAT -> forall env, beval env b = false) /\
    (solver b = SAT ->   exists env, beval env b = true).
Proof.
  intros. split.
  - intros H env. unfold solver in H.
    destruct (bsimp b) eqn:Heq; try easy.
    destruct b0; try easy.
    now rewrite <- bsimp_correct, Heq.
  - intros H. unfold solver in H.
    destruct (bsimp b) eqn:Heq; try easy.
    destruct b0; try easy.
    exists (fun _ => 0%Z).
    now rewrite <- bsimp_correct, Heq.
Qed.

Definition is_sat (b : bexpr) : bool :=
  match solver b with
  | SAT => true
  | _ => false
  end.