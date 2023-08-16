From Coq Require Import ZArith String Program.Equality Logic.FunctionalExtensionality.
From WiSE Require Import lang.imp relations.

(** * Simple Symbolic Execution for [IMP] *)

(** ** Symbolic Evaluation *)

(** Symbolic stores are simply substitutions (of variable with expressions) *)
Definition sym_store :=
  ident -> aexpr.

Definition id : sym_store := fun x => Var x.

(** Update a symbolic store *)
Definition sym_update (s : sym_store) (x : ident) (e : aexpr) : sym_store :=
  fun y => if (y =? x)%string then e else s y.

(** Compose a store and a symbolic store *)
Definition comp (env : store) (s : sym_store) : store :=
  fun x => aeval env (s x).

Infix "∘" := (comp) (at level 70, no associativity).

Lemma comp_id :
  forall env, comp env id = env.
Proof.
  intros.
  now apply functional_extensionality.
Qed.

(** Symbolic evaluation of arithmetic expressions *)
Fixpoint sym_aeval (s : sym_store) (e : aexpr) : aexpr :=
  match e with
  | Var x => s x
  | Cst c => e
  | Add e1 e2 => Add (sym_aeval s e1) (sym_aeval s e2)
  | Sub e1 e2 => Sub (sym_aeval s e1) (sym_aeval s e2)
  end.

(** Symbolic evaluation of boolean expressions *)
Fixpoint sym_beval (s : sym_store) (e : bexpr) : bexpr :=
  match e with
  | Bcst b      => e
  | Ble e1 e2   => Ble (sym_aeval s e1) (sym_aeval s e2)
  | Beq e1 e2   => Beq (sym_aeval s e1) (sym_aeval s e2)
  | Band e1 e2  => Band (sym_beval s e1) (sym_beval s e2)
  | Bnot e      => Bnot (sym_beval s e)
  end.

(** Substitution lemma (arithmetic) *)
Lemma aeval_comp:
  forall env senv e,
    aeval (env ∘ senv) e = aeval env (sym_aeval senv e).
Proof.
  induction e; simpl; auto.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe1, IHe2.
Qed.

(** Substitution lemma (boolean) *)
Lemma beval_comp:
  forall env senv e,
    beval (env ∘ senv) e = beval env (sym_beval senv e).
Proof.
  induction e; simpl; auto.
  - now do 2 rewrite aeval_comp.
  - now do 2 rewrite aeval_comp.
  - now rewrite IHe.
  - now rewrite IHe1, IHe2.
Qed.

(** Composing with an updated symbolic store is the same
    as composing with the initial symbolic store and then
    do a (regular) update
*)
Lemma comp_update:
  forall env senv e x,
    env ∘ (sym_update senv x (sym_aeval senv e)) =
    update (env ∘ senv) x (aeval (env ∘ senv) e).
Proof.
  intros.
  apply functional_extensionality. intros y.
  unfold comp, sym_update, update.
  destruct String.eqb; subst; auto.
  fold (comp env senv).
  now rewrite aeval_comp.
Qed.

(** ** Symbolic Semantics *)

(** A symbolic state is a path constraint expressed as a [bexpr],
    a symbolic store and a program to execute
*)
Definition sym_state := (bexpr * sym_store * IMP)%type.

(** A small step symbolic semantics for IMP *)
Inductive sym_step : sym_state -> sym_state -> Prop :=
  | sym_step_Aff s π x e ve :
    sym_aeval s e = ve -> sym_step (π, s, Aff x e) (π, sym_update s x ve, Skip)
  | sym_step_Seq π1 π2 s1 s2 c1 c2 c3 :
    sym_step (π1, s1, c1) (π2, s2, c2) -> sym_step (π1, s1, Seq c1 c3) (π2, s2, Seq c2 c3)
  | sym_step_Seq_Skip s c :
    sym_step (s, Seq Skip c) (s, c)
  | sym_step_Ite_true π s e c1 c2 :
    sym_step (π, s, Ite e c1 c2) (Band π (sym_beval s e), s, c1)
  | sym_step_Ite_false π s e c1 c2 :
    sym_step (π, s, Ite e c1 c2) (Band π (Bnot (sym_beval s e)), s, c2)
  | sym_step_Loop_true π s e c :
    sym_step (π, s, Loop e c) (Band π (sym_beval s e), s, Seq c (Loop e c))
  | sym_step_Loop_false π s e c :
    sym_step (π, s, Loop e c) (Band π (Bnot (sym_beval s e)), s, Skip).

(** Reflexive Transitive Closure of [sym_step] *)
Definition sym_steps := star sym_step.

(** [sym_step] is sound with respect to [step] *)
Lemma sym_step_step:
  forall env senv1 senv2 π1 π2 c1 c2,
    sym_step (π1, senv1, c1) (π2, senv2, c2) ->
    beval env π2 = true ->
    step (env ∘ senv1, c1) (env ∘ senv2, c2).
Proof.
  intros.
  dependent induction H; subst.
  - rewrite comp_update.
    now econstructor.
  - econstructor.
    simpl in H0.
    now eapply IHsym_step.
  - econstructor.
  - simpl in H0.
    apply Bool.andb_true_iff in H0 as [H1 H2].
    econstructor.
    now rewrite beval_comp.
  - simpl in H0.
    apply Bool.andb_true_iff in H0 as [H1 H2].
    econstructor.
    rewrite beval_comp.
    now apply Bool.negb_true_iff in H2.
  - simpl in H0.
    apply Bool.andb_true_iff in H0 as [H1 H2].
    econstructor.
    now rewrite beval_comp.
  - simpl in H0.
    apply Bool.andb_true_iff in H0 as [H1 H2].
    econstructor.
    rewrite beval_comp.
    now apply Bool.negb_true_iff in H2.
Qed.

(** Monotonicity of path constraints over 1 step *)
Lemma sym_step_path:
  forall env π1 senv1 c1 π2 senv2 c2,
    sym_step (π1, senv1, c1) (π2, senv2, c2) ->
    beval env π2 = true ->
    beval env π1 = true.
Proof.
  intros * H1 H2.
  dependent induction H1; auto; simpl in *.
  - eapply IHsym_step; eauto.
  - now apply Bool.andb_true_iff in H2 as [H2 _].
  - now apply Bool.andb_true_iff in H2 as [H2 _].
  - now apply Bool.andb_true_iff in H2 as [H2 _].
  - now apply Bool.andb_true_iff in H2 as [H2 _].
Qed.

(** Monotonicity of path constraints over 0 or more steps *)
Lemma sym_steps_path:
  forall env X Y,
    sym_steps X Y ->
    forall π1 senv1 c1 π2 senv2 c2,
      X = (π1, senv1, c1) ->
      Y = (π2, senv2, c2) ->
      beval env π2 = true ->
      beval env π1 = true.
Proof.
  intros env.
  refine (star_ind _ _ _ _ _).
  - now intros * -> [=->->->] H.
  - intros [[π1 senv1] c1] [[π2 senv2] c2] [[π3 senv3] c3].
    intros H1 H2 H3 * [=<-<-<-] [=<-<-<-] H.
    eapply sym_step_path; eauto.
Qed.

(** [sym_steps] is sound with respect to [steps].
    This lemma is an (equivalent) reformulation of [sym_steps_steps]
    that makes the pattern of [star']'s induction principle explicit.
*)
Lemma sym_steps_steps_aux:
  forall env X Y,
    sym_steps X Y ->
    forall senv1 senv2 π1 π2 c1 c2,
      X = (π1, senv1, c1) ->
      Y = (π2, senv2, c2) ->
      beval env π2 = true ->
      steps (env ∘ senv1, c1) (env ∘ senv2, c2).
Proof.
  intros env.
  refine (star_ind _ _ _ _ _).
  - intros * -> [=->->->] _.
    reflexivity.
  - intros [[π1 senv1] c1] [[π2 senv2] c2] [[π3 senv3] c3].
    intros * H1 H2 IH * [=<-<-<-] [=<-<-<-] H3.
    econstructor.
    eapply sym_step_step; eauto.
    eapply sym_steps_path; eauto.
    eapply IH; auto.
Qed.

(** [sym_steps] is sound with respect to [steps] *)
Lemma sym_steps_steps:
  forall env senv1 senv2 π1 π2 c1 c2,
    sym_steps (π1, senv1, c1) (π2, senv2, c2) ->
    beval env π2 = true ->
    steps (comp env senv1, c1) (comp env senv2, c2).
Proof.
  intros * H1 H2.
  eapply sym_steps_steps_aux; eauto.
Qed.

(** [sym_step] is a sound semantics to simulate initial execution paths *)
Lemma symex_sound:
  forall π env senv p1 p2,
    sym_steps (Bcst true, id, p1) (π, senv, p2) ->
    beval env π = true ->
    steps (env, p1) (comp env senv, p2).
Proof.
  intros * H1 H2.
  pose proof sym_steps_steps env _ _ _ _ _ _ H1 H2.
  now rewrite comp_id in H.
Qed.

(**
  A symbolic state [⟨π, senv, p⟩] is said to simulate a concrete state
  [⟨env, p'⟩] wrt to initial store [env0] iff [env0] satisfies
  the path constraint [π], and [p = p'], and the concrete
  store [env] is obtained by composing the initial store [env0] and the
  symbolic store [senv].
*)
Definition sim (env0 : store) '((env, p') : store * IMP) '((π, senv, p) : sym_state) :=
  beval env0 π = true /\ env = comp env0 senv /\ p = p'.

Notation "e @ s1 ≃ s2" := (sim e s1 s2) (at level 80).

(** We can build a simulation diagram over [step] and [sym_step]:
    For every step [step p p'] such that [sim p q], there exists [q'] such
    that [sym_step q q'] and [sim q q'].
*)
Lemma step_simulation_diagram:
  forall env0,
    simulation step sym_step (sim env0).
Proof.
  intros env0.
  refine (step_ind _ _ _ _ _ _ _ _).
  - intros env x e ve <- [[π1 senv1] p1] (Hπ & -> & ->).
    repeat econstructor; auto.
    now rewrite comp_update.
  - intros env1 env2 p1 p2 p3 Hstep IH [[π1 senv1] p1'] (Hπ & -> & ->).
    assert (Hsim : sim env0 (comp env0 senv1, p1) (π1, senv1, p1)) by easy.
    specialize (IH _ Hsim) as ([[π2 senv2] p2'] & H1 & (Hπ2 & -> & ->)).
    repeat esplit.
    + econstructor; apply H1.
    + red; auto.
  - intros env p [[π1 senv1] p1] (Hπ1 & -> & ->).
    repeat esplit.
    + apply sym_step_Seq_Skip.
    + red; auto.
  - intros env e p1 p2 He [[π1 senv1] p1'] (Hπ1 & -> & ->).
    repeat esplit.
    + apply sym_step_Ite_true.
    + red; simpl. now rewrite <- beval_comp, He, Hπ1.
  - intros env e p1 p2 He [[π1 senv1] p1'] (Hπ1 & -> & ->).
    repeat esplit.
    + apply sym_step_Ite_false.
    + red; simpl. now rewrite <- beval_comp, He, Hπ1.
  - intros env e p He [[π1 senv1] p1] (Hπ1 & -> & ->).
    repeat esplit.
    + apply sym_step_Loop_true.
    + red; simpl. now rewrite <- beval_comp, He, Hπ1.
  - intros env e p He [[π1 senv1] p1] (Hπ1 & -> & ->).
    repeat esplit.
    + apply sym_step_Loop_false.
    + red; simpl. now rewrite <- beval_comp, He, Hπ1.
Qed.

Lemma sim_init:
  forall env p, env @ (env, p) ≃ (Bcst true, id, p).
Proof.
  easy.
Qed.

(** The simulation diagram [step_simulation_diagram] can
    be iterated and therefore extended
    to a diagram over [steps] and [sym_steps]
*)
Theorem steps_simulation_diagram:
  forall env0,
    simulation steps sym_steps (sim env0).
Proof.
  intros.
  apply star_simulation, step_simulation_diagram.
Qed.

Theorem symex_complete:
  forall env p s,
    steps (env, p) s ->
    exists s',
      sym_steps (Bcst true, id, p) s' /\
      env @ s ≃ s'.
Proof.
  intros * H.
  now eapply steps_simulation_diagram; eauto.
Qed.

Definition potential_bug (s s' : sym_state) : Prop :=
  let '(path, env, prog) := s' in
  sym_steps s s' /\ error prog.

Definition relatively_sound_bug_finding:
  forall prog0 path senv prog,
    potential_bug (Bcst true, id, prog0) (path, senv, prog) ->
    forall env0,
      beval env0 path = true ->
      imp.bug (env0, prog0) (env0 ∘ senv, prog).
Proof.
  intros * [H1 H2]. split; auto.
  eapply symex_sound; eauto.
Qed.

Definition complete_bug_finding:
  forall env0 prog0 env1 prog1,
    imp.bug (env0, prog0) (env1, prog1) ->
    exists π senv prog,
      potential_bug (Bcst true, id, prog0) (π, senv, prog) /\
      sim env0 (env1, prog1) (π, senv, prog).
Proof.
  intros * [([[π senv] prog1] & [H1 [H2 [H3 H4]]])%symex_complete H5]; subst.
  exists π, senv, prog2.
  repeat split; auto.
Qed.

Definition Reach '(p : IMP) '(σ : store * IMP) : Prop :=
  exists V0, exists σ', sym_steps (Bcst true, id, p) σ' /\ V0 @ σ ≃ σ'.

Definition HasBug (p : IMP) : Prop :=
  exists σ, Reach p σ /\ Stuck σ.

Definition IsBug (p : IMP) (σ : store * IMP) : Prop :=
  Reach p σ /\ Stuck σ.

Definition BadInput (p : IMP) (V0 : store) : Prop :=
  exists σ, exists σ', sym_steps (Bcst true, id, p) σ' /\ V0 @ σ ≃ σ' /\ Stuck σ.

Theorem Reach_sound:
  forall p σ, Reach p σ -> imp.Reach p σ.
Proof.
  intros p0 [V p].
  intros (V0 & [[φ S] p'] & [Hsteps [Heq1 [-> ->]]]).
  exists V0.
  rewrite <- (comp_id V0) at 1.
  eapply sym_steps_steps; eauto.
Qed.

Theorem Reach_complete:
  forall p σ, imp.Reach p σ -> Reach p σ.
Proof.
  intros p0 [V p].
  intros (V0 & Hsteps%symex_complete). red.
  exists V0. apply Hsteps.
Qed.

Theorem HasBug_correct:
  forall p, HasBug p <-> imp.HasBug p.
Proof.
  intros p. split.
  - intros [σ [Hreach%Reach_sound Hstuck]].
    now exists σ.
  - intros [σ [Hreach%Reach_complete Hstuck]].
    now exists σ.
Qed.

Theorem IsBug_correct:
  forall p σ, IsBug p σ <-> imp.IsBug p σ.
Proof.
  intros p σ. split.
  - now intros [Hreach%Reach_sound Hstuck].
  - now intros [Hreach%Reach_complete Hstuck].
Qed.

Theorem BadInput_correct:
  forall p V0, BadInput p V0 <-> imp.BadInput p V0.
Proof.
  intros p0 V0. split.
  - eintros ([V p] & [[φ S] p'] & [Hsteps [[Heq1 [-> ->]] Hstuck]]).
    exists (V0 ∘ S, p). split; auto.
    eapply symex_sound; eauto.
  - eintros (σ & (σ' & Hsteps & Hequiv)%symex_complete & Hstuck).
    now exists σ, σ'.
Qed.

(** What it means to be a concrete state denoted by
    a symbolic state *)
Definition Concrete '(σ : sym_state) :=
  fun σ' => exists V0, V0 @ σ' ≃ σ.