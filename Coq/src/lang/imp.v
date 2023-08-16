From Coq Require Import ZArith String Bool Program.Equality.
From WiSE Require Import relations.

(** * IMP, A toy imperative programming language *)

(** ** Syntax *)

Definition ident := string.

(** Expressions *)
Inductive aexpr : Type :=
  | Var : ident -> aexpr
  | Cst : Z -> aexpr
  | Add : aexpr -> aexpr -> aexpr
  | Sub : aexpr -> aexpr -> aexpr.

Fixpoint aeq (a1: aexpr) (a2: aexpr) : bool :=
  match a1, a2 with
  | Var id1, Var id2 => String.eqb id1 id2
  | Cst c1, Cst c2 => Z.eqb c1 c2
  | Add a1 a2, Add a3 a4 | Sub a1 a2, Sub a3 a4 
      => andb (aeq a1 a3) (aeq a2 a4)
  | _, _ => false
  end.

Lemma aeq_spec:
  forall a b, aeq a b = true <-> a = b.
Proof.
  induction a; intro b; split; intro H; destruct b; try easy; simpl in *.
  - destruct (String.eqb_spec i i0).
    + rewrite <- e; easy.
    + destruct (diff_false_true); easy.
  - injection H.
    intro eq.
    rewrite <- eq.
    destruct (String.eqb_spec i i); auto.
  - destruct (Z.eqb_eq z z0).
    destruct (H0 H); easy.
  - injection H; intros; rewrite <- H0; destruct (Z.eqb_eq z z); auto.
  - destruct (andb_true_iff (aeq a1 b1) (aeq a2 b2)) as [H_to_prop _].
    destruct (H_to_prop H) as [H_a1_beq_b1 H_a2_beq_b2].
    destruct (IHa1 b1) as [H_a1_beq_b1_to_prop _].
    destruct (H_a1_beq_b1_to_prop H_a1_beq_b1).
    destruct (IHa2 b2) as [H_a2_beq_b2_to_prop _].
    destruct (H_a2_beq_b2_to_prop H_a2_beq_b2).
    reflexivity.
  - destruct (andb_true_iff (aeq a1 b1) (aeq a2 b2)) as [_ H_goal_to_prop].
    injection H; intros; subst.
    destruct (IHa1 b1) as [_ H_b1_eq_b1_to_prop].
    destruct (IHa2 b2) as [_ H_b2_eq_b2_to_prop].
    auto.
  - destruct (andb_true_iff (aeq a1 b1) (aeq a2 b2)) as [H_to_prop _].
    destruct (H_to_prop H) as [H_a1_beq_b1 H_a2_beq_b2].
    destruct (IHa1 b1) as [H_a1_beq_b1_to_prop _].
    destruct (H_a1_beq_b1_to_prop H_a1_beq_b1).
    destruct (IHa2 b2) as [H_a2_beq_b2_to_prop _].
    destruct (H_a2_beq_b2_to_prop H_a2_beq_b2).
    reflexivity.
  - destruct (andb_true_iff (aeq a1 b1) (aeq a2 b2)) as [_ H_goal_to_prop].
    injection H; intros; subst.
    destruct (IHa1 b1) as [_ H_b1_eq_b1_to_prop].
    destruct (IHa2 b2) as [_ H_b2_eq_b2_to_prop].
    auto.
Qed.

Inductive bexpr : Type :=
  | Bcst  : bool -> bexpr
  | Ble   : aexpr -> aexpr -> bexpr
  | Beq   : aexpr -> aexpr -> bexpr
  | Bnot  : bexpr -> bexpr
  | Band  : bexpr -> bexpr -> bexpr.

Definition Bor (b1 b2 : bexpr) := Bnot (Band (Bnot b1) (Bnot b2)).

Fixpoint beq (b1: bexpr) (b2: bexpr) : bool :=
  match b1, b2 with
  | Bcst b1, Bcst b2 => eqb b1 b2
  | Ble a1 a2, Ble a3 a4 | Beq a1 a2, Beq a3 a4 
      => andb (aeq a1 a3) (aeq a2 a4)
  | Bnot b1, Bnot b2 => beq b1 b2
  | Band b1 b2, Band b3 b4 => andb (beq b1 b3) (beq b2 b4)
  | _, _ => false
  end.

Lemma beq_spec:
  forall a b, beq a b = true <-> a = b.
Proof.
  induction a; intro b0; split; intro H;
  destruct b0; auto;
  try (simpl in H; destruct (diff_false_true); easy).
  - simpl in *;
    destruct (eqb_spec b b0); inversion H; subst; auto.
  - injection H; intro H_b_eq_b0; subst.
    unfold beq.
    destruct (eqb_spec b0 b0); easy.
  - unfold beq in H.
    destruct (andb_true_iff (aeq a a1) (aeq a0 a2)) as [H0 _].
    destruct (H0 H) as [H1 H2].
    destruct (aeq_spec a a1) as [H3 _].
    destruct (aeq_spec a0 a2) as [H4 _].
    destruct (H3 H1).
    destruct (H4 H2).
    easy.
  - unfold beq.
    apply (andb_true_iff (aeq a a1) (aeq a0 a2)).
    inversion H; subst.
    split; apply aeq_spec; reflexivity.
  - unfold beq in H.
    destruct (andb_true_iff (aeq a a1) (aeq a0 a2)) as [H0 _].
    destruct (H0 H) as [H1 H2].
    destruct (aeq_spec a a1) as [H3 _].
    destruct (aeq_spec a0 a2) as [H4 _].
    destruct (H3 H1).
    destruct (H4 H2).
    easy.
  - unfold beq.
    apply (andb_true_iff (aeq a a1) (aeq a0 a2)).
    inversion H; subst.
    split; apply aeq_spec; reflexivity.
  - destruct (IHa b0) as [H_beq_a_b0_to_prop _].
    simpl in *.
    destruct (H_beq_a_b0_to_prop H).
    reflexivity.
  - injection H; intros H_a_eq_b0; subst.
    simpl.
    destruct (IHa b0) as [_ H0].
    auto.
  - simpl in *.
    destruct (andb_true_iff (beq a1 b0_1) (beq a2 b0_2)) as [H0 _].
    destruct (H0 H) as [H1 H2].
    destruct (IHa1 b0_1) as [H3 _].
    destruct (IHa2 b0_2) as [H4 _].
    destruct (H3 H1).
    destruct (H4 H2).
    reflexivity.
  - injection H; intros H1 H2; subst.
    simpl in *.
    destruct (IHa1 b0_1) as [_ H0].
    destruct (IHa2 b0_2) as [_ H1].
    destruct (andb_true_iff (beq b0_1 b0_1) (beq b0_2 b0_2)) as [_ H2].
    auto.
Qed.

(** Commands *)
Inductive IMP : Type :=
  | Skip  : IMP
  | Ite   : bexpr -> IMP -> IMP -> IMP
  | Seq   : IMP -> IMP -> IMP
  | Aff   : string -> aexpr -> IMP
  | Err   : IMP
  | Loop  : bexpr -> IMP -> IMP
  .

Definition Assert c := Ite c Skip Err.

(** ** Semantics *)

Definition store := ident -> Z.

(** *** Denotational semantics for expressions *)

(** Semantic of Arithmetic expressions *)
Fixpoint aeval (s : store) (e : aexpr) : Z :=
  match e with
  | Var x => s x
  | Cst c => c
  | Add e1 e2 => aeval s e1 + aeval s e2
  | Sub e1 e2 => aeval s e1 - aeval s e2
  end.

Fixpoint asubst (e : aexpr) (x : ident) (e' : aexpr) :=
  match e with
  | Var y => if (y =? x)%string then e' else e
  | Cst _ => e
  | Add e1 e2 => Add (asubst e1 x e') (asubst e2 x e')
  | Sub e1 e2 => Sub (asubst e1 x e') (asubst e2 x e')
  end.

Definition ainst (e : aexpr) (x : ident) (vx : Z) :=
  asubst e x (Cst vx).

Fixpoint beval (s : store) (e : bexpr) : bool :=
  match e with
  | Bcst b      => b
  | Ble e1 e2   => (aeval s e1 <=? aeval s e2)%Z
  | Beq e1 e2   => (aeval s e1 =? aeval s e2)%Z
  | Band e1 e2  => beval s e1 && beval s e2
  | Bnot e      => negb (beval s e)
  end.

Fixpoint bsubst (e : bexpr) (x : ident) (e' : aexpr) :=
  match e with
  | Bcst _      => e
  | Beq e1 e2   => Beq (asubst e1 x e') (asubst e2 x e')
  | Ble e1 e2   => Ble (asubst e1 x e') (asubst e2 x e')
  | Band e1 e2  => Band (bsubst e1 x e') (bsubst e2 x e')
  | Bnot e      => Bnot (bsubst e x e')
  end.

Definition binst (e : bexpr) (x : ident) (vx : Z) :=
  bsubst e x (Cst vx).

(** *** Operational semantics of IMP *)

(** Updating a store *)
Definition update (s : store) (x : ident) (v : Z) : store :=
  fun y => if (y =? x)%string then v else s y.

(** Subtitution lemma (for arithmetic expressions) *)
Lemma aeval_asubst :
  forall s e x e',
    aeval s (asubst e x e') = aeval (update s x (aeval s e')) e.
Proof.
  induction e; intros; simpl in *; auto.
  - unfold update.
    destruct (String.eqb_spec i x); auto.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe1, IHe2.
Qed.

(** Subtitution lemma (for boolean expressions) *)
Lemma beval_bsubst :
  forall s c x e,
    beval s (bsubst c x e) = beval (update s x (aeval s e)) c.
Proof.
  intros. induction c; simpl in *; auto.
  all: try now do 2 rewrite <- aeval_asubst.
  now rewrite IHc.
  now rewrite IHc1, IHc2.
Qed.

Lemma aeval_inst:
  forall s e x vx, aeval (update s x vx) e = aeval s (ainst e x vx).
Proof.
  intros. unfold ainst.
  now rewrite aeval_asubst.
Qed.

Lemma beval_inst:
  forall s c x vx, beval (update s x vx) c = beval s (binst c x vx).
Proof.
  intros. induction c; simpl; auto.
  all: try now do 2 rewrite aeval_inst.
  now rewrite IHc.
  now rewrite IHc1, IHc2.
Qed.

(** Big step semantics *)
Inductive exec : store -> IMP -> store -> Prop :=
  | exec_Skip s :
    exec s Skip s
  | exec_Aff s x e ve :
    aeval s e = ve ->
    exec s (Aff x e) (update s x ve)
  | exec_Seq s s' s'' c1 c2 :
    exec s c1 s' ->
    exec s' c2 s'' ->
    exec s (Seq c1 c2) s''
  | exec_Ite_true s s' e c1 c2 :
    beval s e = true ->
    exec s c1 s' ->
    exec s (Ite e c1 c2) s'
  | exec_Ite_false s s' e c1 c2 :
    beval s e = false ->
    exec s c2 s' ->
    exec s (Ite e c1 c2) s'
  | exec_loop_true s s' s'' e c :
    beval s e = true ->
    exec s c s' ->
    exec s' (Loop e c) s'' ->
    exec s (Loop e c) s''
  | exec_loop_false s e c :
    beval s e = false ->
    exec s (Loop e c) s.

(** Small step semantics *)
Inductive step : (store * IMP) -> (store * IMP) -> Prop :=
  | step_Aff s x e ve :
    aeval s e = ve -> step (s, Aff x e) (update s x ve, Skip)
  | step_Seq s1 s2 c1 c2 c3 :
    step (s1, c1) (s2, c2) -> step (s1, Seq c1 c3) (s2, Seq c2 c3)
  | step_Seq_Skip s c :
    step (s, Seq Skip c) (s, c)
  | step_Ite_true s e c1 c2 :
    beval s e = true -> step (s, Ite e c1 c2) (s, c1)
  | step_Ite_false s e c1 c2 :
    beval s e = false -> step (s, Ite e c1 c2) (s, c2)
  | step_Loop_true s e c :
    beval s e = true -> step (s, Loop e c) (s, Seq c (Loop e c))
  | step_Loop_false s e c :
    beval s e = false -> step (s, Loop e c) (s, Skip).

Lemma aeval_stable:
  forall env1 env2 e,
    (forall x, env1 x = env2 x) ->
    aeval env1 e = aeval env2 e.
Proof.
  intros.
  induction e; simpl; auto.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe1, IHe2.
Qed.

(** Sequences of steps *)
Definition steps := star step.

(** Taking several steps to the left of a sequence *)
Lemma steps_seq :
  forall s1 s2 c1 c2 c3,
    steps (s1, c1) (s2, c2) -> steps (s1, Seq c1 c3) (s2, Seq c2 c3).
Proof.
  intros * H. dependent induction H.
  * reflexivity.
  * destruct y as [s1' c1'].
    eapply star_step. apply step_Seq, H.
    now apply IHstar.
Qed.

(**
  If a program [p] starting in state [s] terminates in 
  state [s'] then [p] can take a sequence of steps
  from [s] to [s']
*)
Theorem exec_steps :
  forall p s s', exec s p s' -> steps (s, p) (s', Skip).
Proof.
  induction 1.
  - reflexivity.
  - eapply star_step.
    + apply (step_Aff _ _ _ _ H).
    + reflexivity.
  - etransitivity. apply steps_seq, IHexec1.
    eapply star_step. apply step_Seq_Skip.
    apply IHexec2.
  - eapply star_step. eapply (step_Ite_true _ _ _ _ H).
    apply IHexec.
  - eapply star_step. eapply (step_Ite_false _ _ _ _ H).
    apply IHexec.
  - eapply star_step. eapply (step_Loop_true _ _ _ H).
    etransitivity. eapply (steps_seq _ _ _ _ _ IHexec1).
    eapply star_step. eapply step_Seq_Skip. apply IHexec2.
  - eapply star_step. eapply (step_Loop_false _ _ _ H).
    reflexivity.
Qed.

Theorem step_exec_exec :
  forall c1 c2 s1 s2 s3,
    step (s1, c1) (s2, c2) ->
    exec s2 c2 s3 ->
    exec s1 c1 s3.
Proof.
  intros * H1. generalize s3. clear s3.
  dependent induction H1; intros.
  - inversion_clear H.
    now apply exec_Aff.
  - inversion_clear H.
    eapply exec_Seq; eauto.
  - eapply exec_Seq; eauto using exec.
  - eapply exec_Ite_true; eauto.
  - eapply exec_Ite_false; eauto.
  - inversion_clear H0.
    eapply exec_loop_true; eauto.
  - inversion H0; subst.
    eapply exec_loop_false; eauto.
Qed.

(**
  If a program [p] can take a sequence of steps
  from [s] to [s'] then [p] terminates in
  state [s'] when executed in [s]
*)
Theorem steps_exec :
  forall p s s', steps (s, p) (s', Skip) -> exec s p s'.
Proof.
  intros. dependent induction H.
  - apply exec_Skip.
  - destruct y as [s1 p1].
    eapply step_exec_exec; eauto.
Qed.

(** ** Progression and Erroneous States  *)

(** A configuration is said to [progress] if it is a [Skip] statement or
    if it can take a [step]
*)
Definition progress '((s, p) : (store * IMP)) : Prop :=
  p = Skip \/ exists s' p', step (s, p) (s', p').

(** An error state is a state that can't progress *)
Definition error_state (st : (store * IMP)) : Prop :=
  ~progress st.

(** [Skip] can progress *)
Theorem progress_Skip:
  forall env, progress (env, Skip).
Proof.
  now left.
Qed.

(** [Ite] can progress *)
Theorem progress_Ite:
  forall env b p1 p2, progress (env, Ite b p1 p2).
Proof.
  intros *. right.
  destruct (beval env b) eqn:Hsat.
  * exists env, p1. now econstructor.
  * exists env, p2. now econstructor.
Qed.

(** [Aff] can progress *)
Theorem progress_Aff:
  forall env x e, progress (env, Aff x e).
Proof.
  intros *. right.
  repeat econstructor.
Qed.

(** [Aff] can progress *)
Theorem progress_Seq:
  forall env p1 p2, progress (env, p1) -> progress (env, Seq p1 p2).
Proof.
  intros * [-> | (s' & p' & H)].
  - right. exists env, p2. econstructor.
  - right. exists s', (Seq p' p2). now econstructor.
Qed.

(** [Loop] can progress *)
Theorem progress_Loop:
  forall env b p, progress (env, Loop b p).
Proof.
  intros *. right.
  destruct (beval env b) eqn:Hsat.
  - exists env. now repeat econstructor.
  - exists env, Skip. now repeat econstructor.
Qed.

(** If a sequence [Seq p1 p2] can't progress, then [p1] can't progress *)
Theorem error_state_seq:
  forall s p1 p2, error_state (s, Seq p1 p2) -> error_state (s, p1).
Proof.
  intros * H Hcontr.
  apply H, progress_Seq, Hcontr.
Qed.

(** Syntactic characterization of error states *)
Inductive error : IMP -> Prop :=
  | error_Err : error Err
  | error_Seq p1 p2 : error p1 -> error (Seq p1 p2).

Theorem error_state_error :
  forall s p, error_state (s, p) <-> error p.
Proof.
  intros. split.
  - intros Hcontr.
    induction p; try easy.
    + now specialize (Hcontr (progress_Skip s)).
    + now specialize (Hcontr (progress_Ite s _ _ _)).
    + apply error_state_seq in Hcontr.
      specialize (IHp1 Hcontr). now econstructor.
    + now specialize (Hcontr (progress_Aff s _ _)).
    + econstructor.
    + now specialize (Hcontr (progress_Loop s _ _)).
  - induction 1.
    + intros [H | (s' & p' & H)]; try easy.
    + intros [H' | (s' & p' & H')]; try easy.
      inversion H'; subst.
      assert (Hprog : progress (s, p1)) by (right; repeat econstructor; eauto).
      apply (IHerror Hprog).
      inversion H.
Qed.

(** Executable check for erroneous state *)
Fixpoint is_error (p : IMP) : bool :=
  match p with
  | Err => true
  | Seq p _ => is_error p
  | _ => false
  end.

Theorem is_error_correct:
  forall p, is_error p = true <-> error p.
Proof.
  induction p; try easy.
  - split.
    + intros H%IHp1. now econstructor.
    + intros. inversion H; subst.
      simpl. now apply IHp1.
  - repeat econstructor.
Qed.

Definition is_skip (p : IMP) : bool :=
  match p with
  | Skip => true
  | _ => false
  end.

Definition bug (s s' : store * IMP) : Prop :=
  let '(_, prog) := s' in
  steps s s' /\ error prog.

Definition Stuck (σ : store * IMP) : Prop :=
  ~progress σ.

Definition Reach '(p : IMP) '(σ : store * IMP) : Prop :=
  exists V0, steps (V0, p) σ.

Definition HasBug (p : IMP) : Prop :=
  exists σ, Reach p σ /\ Stuck σ.

Definition IsBug (p : IMP) (σ : store * IMP) : Prop :=
  Reach p σ /\ Stuck σ.

Definition BadInput (p : IMP) (V0 : store) : Prop :=
  exists σ, steps (V0, p) σ /\ Stuck σ.


Lemma is_error_Stuck:
  forall V p, is_error p = true <-> Stuck (V, p).
Proof.
  intros.
  rewrite is_error_correct.
  now rewrite error_state_error.
Qed.