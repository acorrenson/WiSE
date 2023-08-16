From Coq Require Import ZArith String Program.Equality Logic.FunctionalExtensionality.
From WiSE Require Import lang.imp relations symex.

(** * A more Precise Symbolic Execution for [IMP] *)

Definition unsat (b : bexpr) : Prop :=
  forall env, beval env b = false.

Definition sat (b : bexpr) : Prop :=
  exists env, beval env b = true.

(** A small step symbolic semantics for IMP *)
Inductive precise_sym_step : sym_state -> sym_state -> Prop :=
  | sym_step_Aff s π x e ve :
    sym_aeval s e = ve -> precise_sym_step (π, s, Aff x e) (π, sym_update s x ve, Skip)
  | sym_step_Seq π1 π2 s1 s2 c1 c2 c3 :
    precise_sym_step (π1, s1, c1) (π2, s2, c2) -> precise_sym_step (π1, s1, Seq c1 c3) (π2, s2, Seq c2 c3)
  | sym_step_Seq_Skip s c :
    precise_sym_step (s, Seq Skip c) (s, c)
  | sym_step_Ite_true π s e c1 c2 :
    sat (Band π (sym_beval s e)) ->
    precise_sym_step (π, s, Ite e c1 c2) (Band π (sym_beval s e), s, c1)
  | sym_step_Ite_false π s e c1 c2 :
    sat (Band π (Bnot (sym_beval s e))) ->
    precise_sym_step (π, s, Ite e c1 c2) (Band π (Bnot (sym_beval s e)), s, c2)
  | sym_step_Loop_true π s e c :
    sat (Band π (sym_beval s e)) ->
    precise_sym_step (π, s, Loop e c) (Band π (sym_beval s e), s, Seq c (Loop e c))
  | sym_step_Loop_false π s e c :
    sat (Band π (Bnot (sym_beval s e))) ->
    precise_sym_step (π, s, Loop e c) (Band π (Bnot (sym_beval s e)), s, Skip).

(** Reflexive Transitive Closure of [precise_sym_step] *)
Definition precise_sym_steps := star precise_sym_step.

(** [precise_sym_step] is sound with respect to [step] *)
Lemma precise_sym_step_step:
  forall env senv1 senv2 π1 π2 c1 c2,
    precise_sym_step (π1, senv1, c1) (π2, senv2, c2) ->
    beval env π2 = true ->
    step (env ∘ senv1, c1) (env ∘ senv2, c2).
Proof.
  intros.
  dependent induction H; subst.
  - rewrite comp_update.
    now econstructor.
  - econstructor.
    simpl in H0.
    now eapply IHprecise_sym_step.
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
Lemma precise_sym_step_path:
  forall env π1 senv1 c1 π2 senv2 c2,
    precise_sym_step (π1, senv1, c1) (π2, senv2, c2) ->
    beval env π2 = true ->
    beval env π1 = true.
Proof.
  intros * H1 H2.
  dependent induction H1; auto; simpl in *.
  - eapply IHprecise_sym_step; eauto.
  - now apply Bool.andb_true_iff in H2 as [H2 _].
  - now apply Bool.andb_true_iff in H2 as [H2 _].
  - now apply Bool.andb_true_iff in H2 as [H2 _].
  - now apply Bool.andb_true_iff in H2 as [H2 _].
Qed.

(** Monotonicity of path constraints over 0 or more steps *)
Lemma precise_sym_steps_path:
  forall env X Y,
    precise_sym_steps X Y ->
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
    eapply precise_sym_step_path; eauto.
Qed.

(** [sym_steps] is sound with respect to [steps].
    This lemma is an (equivalent) reformulation of [sym_steps_steps]
    that makes the pattern of [star']'s induction principle explicit.
*)
Lemma precise_sym_steps_steps_aux:
  forall env X Y,
    precise_sym_steps X Y ->
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
    eapply precise_sym_step_step; eauto.
    eapply precise_sym_steps_path; eauto.
    eapply IH; auto.
Qed.

(** [sym_steps] is sound with respect to [steps] *)
Lemma precise_sym_steps_steps:
  forall env senv1 senv2 π1 π2 c1 c2,
    precise_sym_steps (π1, senv1, c1) (π2, senv2, c2) ->
    beval env π2 = true ->
    steps (comp env senv1, c1) (comp env senv2, c2).
Proof.
  intros * H1 H2.
  eapply precise_sym_steps_steps_aux; eauto.
Qed.

Lemma precise_sym_step_precise:
  forall π1 senv1 p1 π2 senv2 p2,
    sat π1 -> precise_sym_step (π1, senv1, p1) (π2, senv2, p2) -> sat π2.
Proof.
  intros * H1 H2.
  dependent induction H2; auto.
  eapply IHprecise_sym_step; eauto.
Qed.

Lemma precise_sym_steps_precise:
  forall π1 senv1 p1 π2 senv2 p2,
    sat π1 -> precise_sym_steps (π1, senv1, p1) (π2, senv2, p2) -> sat π2.
Proof.
  intros * H1 H2.
  dependent induction H2; auto.
  destruct y as [[π3 senv3] p3].
  pose proof (H3 := precise_sym_step_precise _ _ _ _ _ _ H1 H).
  eapply IHstar.
  + apply H3.
  + reflexivity.
  + reflexivity.
Qed.

(** [precise_sym_step] is a sound semantics to simulate initial execution paths *)
Lemma precise_symex_sound:
  forall π env senv p1 p2,
    precise_sym_steps (Bcst true, id, p1) (π, senv, p2) ->
    beval env π = true ->
    steps (env, p1) (comp env senv, p2).
Proof.
  intros * H1 H2.
  pose proof precise_sym_steps_steps env _ _ _ _ _ _ H1 H2.
  now rewrite comp_id in H.
Qed.

(** [precise_symex_step] is a precise semantics to simulate initial execution paths *)
Lemma precise_symex_precise:
  forall p0 π senv p,
    precise_sym_steps (Bcst true, id, p0) (π, senv, p) -> sat π.
Proof.
  intros * H.
  eapply precise_sym_steps_precise; eauto.
  now exists (fun _ => 0%Z).
Qed.

Lemma true_sat:
  sat (Bcst true).
Proof.
  now exists (fun _ => 0%Z).
Qed.

Lemma step_simulation_diagram:
  forall env0,
    simulation step precise_sym_step (sim env0).
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
      exists env0. simpl.
      now rewrite Hπ1, <- beval_comp, He.
    + red; simpl. now rewrite <- beval_comp, He, Hπ1.
  - intros env e p1 p2 He [[π1 senv1] p1'] (Hπ1 & -> & ->).
    repeat esplit.
    + apply sym_step_Ite_false.
      exists env0. simpl.
      now rewrite Hπ1, <- beval_comp, He.
    + red; simpl. now rewrite <- beval_comp, He, Hπ1.
  - intros env e p He [[π1 senv1] p1] (Hπ1 & -> & ->).
    repeat esplit.
    + apply sym_step_Loop_true.
      exists env0. simpl.
      now rewrite Hπ1, <- beval_comp, He.
    + red; simpl. now rewrite <- beval_comp, He, Hπ1.
  - intros env e p He [[π1 senv1] p1] (Hπ1 & -> & ->).
    repeat esplit.
    + apply sym_step_Loop_false.
      exists env0. simpl.
      now rewrite Hπ1, <- beval_comp, He.
    + red; simpl. now rewrite <- beval_comp, He, Hπ1.
Qed.

Lemma sim_init:
  forall env p, sim env (env, p) (Bcst true, id, p).
Proof.
  easy.
Qed.

(** The simulation diagram [step_simulation_diagram] can
    be iterated and therefore extended
    to a diagram over [steps] and [sym_steps]
*)
Theorem steps_simulation_diagram:
  forall env0,
    simulation steps precise_sym_steps (sim env0).
Proof.
  intros.
  apply star_simulation, step_simulation_diagram.
Qed.

(** [sym_steps] is complete with respect to [steps]. *)
Theorem precise_symex_complete:
  forall env p s,
    steps (env, p) s ->
    exists s',
      precise_sym_steps (Bcst true, id, p) s' /\ env @ s ≃ s'.
Proof.
  intros * H.
  apply (steps_simulation_diagram env _ _ H (Bcst true, id, p) (sim_init env p)).
Qed.

Definition bug (s s' : sym_state) : Prop :=
  let '(path, env, prog) := s' in
  precise_sym_steps s s' /\ error prog.

Definition sound_bug_finding:
  forall prog0 path senv prog,
    bug (Bcst true, id, prog0) (path, senv, prog) ->
    exists env0,
      imp.bug (env0, prog0) (env0 ∘ senv, prog).
Proof.
  intros * [H1 H2].
  pose proof (precise_sym_steps_precise _ _ _ _ _ _ true_sat H1) as [env0 Hsat].
  exists env0. split; auto.
  eapply precise_symex_sound; eauto.
Qed.

Definition complete_bug_finding:
  forall env0 prog0 env1 prog1,
    imp.bug (env0, prog0) (env1, prog1) ->
    exists π senv prog,
      bug (Bcst true, id, prog0) (π, senv, prog) /\
      env0 @ (env1, prog1) ≃ (π, senv, prog).
Proof.
  intros * [[[[π senv] prog] [H1 [H2 [-> ->]]]]%precise_symex_complete H3].
  exists π, senv, prog1.
  repeat esplit; eauto.
Qed.