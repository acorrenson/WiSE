From Coq Require Import ZArith String Program.Equality.
From WiSE Require Import relations.

(** * IMPREC, An extension of IMP with procedures and recursion *)

(** ** Syntax *)

Definition ident := string.

Inductive variable :=
  | Local (x : ident)
  | Global (x : ident).

(** Expressions *)
Inductive aexpr : Type :=
  | Var : variable -> aexpr
  | Cst : Z -> aexpr
  | Add : aexpr -> aexpr -> aexpr
  | Sub : aexpr -> aexpr -> aexpr.

Inductive bexpr : Type :=
  | Bcst  : bool -> bexpr
  | Ble   : aexpr -> aexpr -> bexpr
  | Beq   : aexpr -> aexpr -> bexpr
  | Bnot  : bexpr -> bexpr 
  | Band  : bexpr -> bexpr -> bexpr.

Definition Bor (b1 b2 : bexpr) := Band (Bnot b1) (Bnot b2).

(** Commands *)
Inductive stmt : Type :=
  | Skip  : stmt
  | Ite   : bexpr -> stmt -> stmt -> stmt
  | Seq   : stmt -> stmt -> stmt
  | Aff   : string -> aexpr -> stmt
  | Err   : stmt
  | Loop  : bexpr -> stmt -> stmt
  .

Definition Assert c := Ite c Skip Err.

Fixpoint alocals (e : aexpr) (x : ident) : Prop :=
  match e with
  | Var (Local y) => y = x
  | Var (Global _) | Cst _ => False
  | Add e1 e2 | Sub e1 e2 => alocals e1 x \/ alocals e2 x
  end.

Fixpoint blocals (b : bexpr) (x : ident) : Prop :=
  match b with
  | Bcst _ => False
  | Bnot b => blocals b x
  | Ble e1 e2 | Beq e1 e2 => alocals e1 x \/ alocals e2 x
  | Band b1 b2 =>  blocals b1 x \/ blocals b2 x
  end.

Fixpoint locals (s : stmt) (x : ident) : Prop :=
  match s with
  | Skip => False
  | Ite b s1 s2 => blocals b x \/ locals s1 x \/ locals s2 x
  | Seq s1 s2 =>  locals s1 x \/ locals s2 x
  | Aff y e => x = y \/ alocals e x
  | Err => False
  | Loop b s => blocals b x \/ locals s x
  end.

Record declaration := {
  params : list ident;
  body : stmt;
  Hlocals : forall x, locals body x -> List.In x params
}.

Record IMPREC := {
  decls : list declaration;
  main  : stmt;
}.

(** NOTE :
    Option 1 : assume programs are well formed
      - No undefined local variables
      - No references to undefined procedures
    Option 2 : Semantics fail if undefined variable....

    Opinion :
    - option1 is an approach that works well for static languages
    - option2 models more dynamic languages (python, js)
*)

(** ** Semantics *)

Definition global_store := ident -> Z.
Definition local_store := ident -> Z.

(** *** Denotational semantics for expressions *)

(** Semantics of Arithmetic expressions *)
Fixpoint aeval (gs : global_store) (ls : local_store) (e : aexpr) : Z :=
  match e with
  | Var (Global x) => gs x
  | Var (Local x) => ls x
  | Cst c => c
  | Add e1 e2 => aeval gs ls e1 + aeval gs ls e2
  | Sub e1 e2 => aeval gs ls e1 - aeval gs ls e2
  end.

(* Fixpoint asubst (e : aexpr) (x : ident) (e' : aexpr) :=
  match e with
  | Var y => if (string_dec y x) then e' else e
  | Cst _ => e
  | Add e1 e2 => Add (asubst e1 x e') (asubst e2 x e')
  | Sub e1 e2 => Sub (asubst e1 x e') (asubst e2 x e')
  end.

Definition ainst (e : aexpr) (x : ident) (vx : Z) :=
  asubst e x (Cst vx).

Fixpoint beval (s : store) (e : bexpr) : bool :=
  match e with
  | Bcst b      => b
  | Ble e1 e2   => (aeval s e1 <? aeval s e2)%Z
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
  fun y => if string_dec y x then v else s y.

(** Subtitution lemma (for arithmetic expressions) *)
Lemma aeval_asubst :
  forall s e x e',
    aeval s (asubst e x e') = aeval (update s x (aeval s e')) e.
Proof.
  induction e; intros; simpl in *; auto.
  - unfold update.
    destruct (string_dec i x) eqn:E; auto.
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
Qed. *)