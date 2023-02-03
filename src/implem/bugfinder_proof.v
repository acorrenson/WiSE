From Coq Require Import List Lia String ZArith Program.Equality.
From WiSE Require Import streams lang.imp symbolic.symex implem.bugfinder.
Import ListNotations.
Import LTL.

(** * Correctness proof of the bugfinder *)

(** ** Soundness and Completness of [expand] w.r.t [sym_step] *)

Lemma map_in:
  forall A B (f : A -> B) (l : list A) b,
    In b (List.map f l) -> exists a, In a l /\ b = f a.
Proof.
  intros. induction l; try easy.
  destruct H as [<- | H].
  - repeat econstructor.
  - specialize (IHl H) as (a' & Ha' & ->).
    exists a'. split; auto. now right.
Qed.

(** [expand] is a sound implementation of [sym_step] *)
Theorem expand_sound:
  forall path env prog t,
    In t (expand path env prog) -> sym_step ((path, env), prog) t.
Proof.
  intros path env prog [[path' env'] prog'] Hin.
  induction prog in path', env', prog', Hin |-*; subst; try easy.
  - destruct Hin as [[=<-<-<-] | [ [=<-<-<-] | [] ]]; constructor.
  - destruct prog1; try easy.
    + destruct Hin as [[=<-<-<-] | []]. now econstructor.
    + pose proof (map_in _ _ _ _ _ Hin) as ([[path2 env2] prog3] & [H1 [=->->->]]).
      specialize (IHprog1 _ _ _ H1).
      now constructor.
    + pose proof (map_in _ _ _ _ _ Hin) as ([[path2 env2] prog3] & [H1 [=->->->]]).
      specialize (IHprog1 _ _ _ H1).
      now constructor.
    + pose proof (map_in _ _ _ _ _ Hin) as ([[path2 env2] prog3] & [H1 [=->->->]]).
      specialize (IHprog1 _ _ _ H1).
      now constructor.
    + pose proof (map_in _ _ _ _ _ Hin) as ([[path2 env2] prog3] & [H1 [=->->->]]).
      specialize (IHprog1 _ _ _ H1).
      now constructor.
  - destruct Hin as [[=<-<-<-] | []]. now constructor.
  - destruct Hin as [[=<-<-<-] | [[=<-<-<-]| []]]; now constructor.
Qed.

(** [expand] is a complete implementation of [sym_step] *)
Theorem expand_complete:
  forall path env prog t,
    sym_step ((path, env), prog) t ->
    In t (expand path env prog).
Proof.
  intros * Ht.
  dependent induction Ht; intros; simpl.
  - now econstructor.
  - change (π2, s2, Seq c2 c3) with (then_do c3 (π2, s2, c2)).
    destruct c1; try easy.
    all: eapply in_map, IHHt; eauto.
  - now left.
  - now left.
  - now (right; left).
  - now left.
  - now (right; left).
Qed.

(** [expand] spawns 0, 1 or 2 tasks *)
Theorem expand_inv:
  forall path env prog,
    (expand path env prog = []) \/
    (exists s, expand path env prog = [s]) \/
    (exists s1 s2, expand path env prog = [s1; s2]).
Proof.
  intros. induction prog.
  - now left.
  - now right; right; repeat econstructor.
  - destruct IHprog1 as [IH | [(s & Hs) | (s1 & s2 & Hs)]].
    + destruct prog1; simpl in *; try easy.
      now right; left; repeat econstructor. rewrite IH.
      now left.
      now left.
    + destruct prog1; simpl in *; try easy.
      right. repeat econstructor. now rewrite Hs.
      right. repeat econstructor.
    + destruct prog1; simpl in *; try easy.
      now right; right; repeat econstructor.
      now right; right; repeat econstructor; rewrite Hs.
      right; right; repeat econstructor; rewrite Hs.
  - now right; left; repeat econstructor.
  - now left.
  - now right; right; repeat econstructor.
Qed.

(** ** Eager model of [run] *)
(** The [run] function that executes the main loop of the bugfinder
    generates a lazy stream. Lazy streams are defined co-inductively
    which make them somwhat hard to reason about. To ease the proofs, we
    provide an eager implementation [run_n] of [run] that simulates the behavior of
    [run] for [n] steps of computation. We then relate the 2 functions by a theorem [run_run_n].
*)

(** [run_eq] can be used to destruct applications of the cofixpoint [run] *)
Theorem run_eq:
  forall l path env prog,
    run ((path, env, prog)::l) = scons (Some (path, env, prog)) (run (l ++ expand path env prog)).
Proof.
  intros. now rewrite <- force_id at 1.
Qed.

(** the [run []] is a fixpoint for [shift] i.e.
    once the task list is empty, [run] loops indefinitely
    in a state where the task list remains empty
*)
Lemma run_nil:
  forall n, shift n (run []) = run [].
Proof.
  now induction n.
Qed.

(** Relation between [run] and its eager model [run_n].
    [run_n n l] computes the task list after [n] iterations [run l]
*)
Lemma run_run_n:
  forall n l, shift n (run l) = run (run_n n l).
Proof.
  intros. induction n in l |-*; try easy.
  destruct l as [| [[path env] prog] l] .
  - apply run_nil.
  - rewrite run_eq. simpl. now rewrite IHn.
Qed.

Lemma run_n_nil:
  forall n, run_n n [] = [].
Proof.
  now induction n.
Qed.

(** After [List.length l1] iterations, the task list of [run (l1 ++ l2)]
    starts with [l2]
*)
Theorem run_n_length:
  forall l1 l2,
    exists l3,
      run_n (List.length l1) (l1 ++ l2) = l2 ++ l3.
Proof.
  intros. induction l1 as [|[[path env] prog] l1 IH] in l2 |-*.
  - simpl. exists []. now rewrite app_nil_r.
  - simpl. rewrite <- List.app_assoc.
    specialize (IH (l2 ++ expand path env prog)) as [l3 Hl3].
    rewrite Hl3. rewrite <- List.app_assoc. now eexists.
Qed.

(** After [1 + List.length l1] iterations, the task list of [run (t::l1 ++ l2)]
    starts with [l2] followed with the task spawed by executing [t]
*)
Theorem run_n_S_length:
  forall l1 l2 path env prog,
    exists l3,
      run_n (S (List.length l1)) ((path, env, prog)::l1 ++ l2) = l2 ++ (expand path env prog) ++ l3.
Proof.
  intros. induction l1 as [|[[path1 env1] prog1] l1 IH] in l2, path, env, prog |-*.
  - simpl. exists []. now rewrite app_nil_r.
  - simpl. do 2 rewrite <- List.app_assoc. simpl in IH.
    specialize (IH (l2 ++ expand path env prog) path1 env1 prog1).
    simpl in IH. edestruct IH as [l3 Hl3]. eexists.
    repeat rewrite <- List.app_assoc in Hl3. apply Hl3.
Qed.

(** ** LTL Specification Predicates

    In the remainder of this file, we will use a shallow embedding of the [LTL]
    logic to write specifications over lazy streams.
    We start by defining some usefull [LTL] predicates.
*)

(** The current state in the stream is [sym_steps] reachable from a state in [l] *)
Definition reachable_from (tasks : list sym_state) : LTL.t :=
  now (fun s =>
    match s with
    | None => True
    | Some s => exists s0, In s0 tasks /\ sym_steps s0 s
    end
  ).

(** The current state in the stream is [s] *)
Definition here (s : sym_state) : LTL.t :=
  now (fun st =>
    match st with
    | Some s' => s' = s
    | None => False
    end
  ).
Notation "! x" := (here x).

Definition bug_found s : LTL.t :=
  now (fun (st : status) => 
    match st with
    | BugFound s' => s' = s
    | _ => False
    end
  ).
Notation "!! x" := (bug_found x).

Definition potential_bug p : LTL.t :=
  now (fun (st : status) =>
    match st with
    | BugFound s' => potential_bug (Bcst true, id, p) s'
    | _ => True
    end
  ).

Definition none : LTL.t :=
  now (fun (st : option sym_state) =>
    match st with
    | None => True
    | _ => False
    end
  ).

Definition done : LTL.t :=
  now (fun (st : status) =>
    match st with
    | Finished => True
    | _ => False
    end
  ).

(** ** Soundess of [run] *)

(** [run] is sound with respect to [sym_exec]:
    all states generate by the stream [run l],
    are reachable from [l]
*)
Theorem run_sound:
  forall l,
    run l ⊨ □ reachable_from l.
Proof.
  intros l n. rewrite run_run_n.
  induction n in l |-*.
  - simpl in *. destruct l as [| [[path env] prog]]; try easy.
    repeat econstructor.
  - destruct l as [| [[path env] prog] l]; try easy.
    specialize (IHn (l ++ expand path env prog)).
    simpl. destruct run_n as [| [[path1 env1] prog1]] eqn:Heq; try easy.
    destruct IHn as [[[path2 env2] prog2] [[H | H]%in_app_iff Hsteps]].
    + eexists. split; eauto. now right.
    + pose proof (expand_sound _ _ _ _ H).
      eexists. split. now left.
      econstructor; eauto.
Qed.

(** ** Completeness of [run] *)

(** [run] is complete for [sym_step]:
    if [s] is the next value generated by [run l], then
    all the direct sucessors of [s] are eventually generated
*)
Theorem run_step_complete:
  forall l s s',
    sym_step s s' ->
    run l ⊨ (!s → ◊!s').
Proof.
  intros * Hstep H.
  destruct l as [| [[path env] prog]]; try easy.
  cbn in H. subst.
  apply expand_complete in Hstep.
  destruct (expand_inv path env prog) as [Htask | [[s Htask] | (s1 & s2 & Htask)]].
  - now rewrite Htask in Hstep.
  - rewrite run_eq, Htask in *. inversion Hstep; subst; try easy.
    exists (S (List.length l)). simpl.
    rewrite run_run_n.
    pose proof (run_n_length l [s']) as [l3 Hl3].
    replace (run_n (Datatypes.length l) (l ++ [s'])) with ([s'] ++ l3) at 1.
    now destruct s' as [[a b] c].
  - rewrite run_eq, Htask in *. destruct Hstep as [-> | [ -> | []]].
    + exists (S (List.length l)). simpl.
      rewrite run_run_n.
      pose proof (run_n_length l [s'; s2]) as [l3 Hl3].
      replace (run_n (Datatypes.length l) (l ++ [s'; s2])) with ([s'; s2] ++ l3) at 1.
      simpl. now destruct s' as [[a b] c].
    + exists (S (S (List.length l))). rewrite shift_eq.
      rewrite run_run_n.
      replace (l ++ [s1; s']) with ((l ++ [s1]) ++ [s']) at 1 by now rewrite <- List.app_assoc.
      pose proof (run_n_length (l ++ [s1]) [s']) as [l3 Hl3].
      replace (Datatypes.length (l ++ [s1])) with (S (Datatypes.length l)) in Hl3.
      replace (run_n (S (Datatypes.length l)) ((l ++ [s1]) ++ [s'])) with ([s'] ++ l3) at 1.
      now destruct s' as [[a b] c].
      rewrite List.app_length. simpl. lia.
Qed.

(** [run [s]] immediately generates [s] *)
Theorem run_here:
  forall s,
    run [s] ⊨ here s.
Proof.
  now intros [[path env] prog].
Qed.

(** [run] is complete for [sym_steps]:
    At any point in time, if [s] is generated by [run l], then
    all the [sym_steps] sucessors of [s] are eventually generated
*)
Theorem run_steps_complete:
  forall s s',
    sym_steps s s' ->
    forall l,
      run l ⊨ □ (!s → ◊!s').
Proof.
  intros s s' H.
  dependent induction H.
  - intros l n Hn. now exists 0.
  - intros l n Hn. rewrite run_run_n in *.
    pose proof (run_step_complete (run_n n l) _ _ H Hn) as [m Hm]. simpl in Hm.
    specialize (IHstar _ _ Hm) as [k Hk].
    rewrite shift_shift, run_run_n in Hk.
    eexists (k + m). now rewrite run_run_n.
Qed.

(** [run] is a complete wau to compute the [sym_steps] sucessors
    of any state [s]:
    starting with the task [[s]], [run [s]] eventually generates
    all [sym_steps] sucessors of [s]
*)
Theorem run_complete:
  forall s s',
    sym_steps s s' -> run [s] ⊨ ◊!s'.
Proof.
  intros.
  now pose proof (run_steps_complete _ _ H [s] 0 (run_here s)).
Qed.

Theorem run_finished_nil:
  forall l,
    none (run l) -> l = [].
Proof.
  now intros [|[[path env] prog]].
Qed.

Theorem run_finished:
  forall l,
    run l ⊨ □ (none → □ none).
Proof.
  intros l n Hn m.
  rewrite run_run_n in Hn.
  apply run_finished_nil in Hn.
  rewrite run_run_n, Hn.
  now rewrite run_nil.
Qed.

(** [fin_bugs] is sound:
    For any program [p], [find_bugs p]
    emits warnings ONLY if it found a bug in [p]
*)
Theorem find_bugs_sound:
  forall p,
    find_bugs p ⊨ □ (potential_bug p).
Proof.
  intros. unfold find_bugs.
  pose proof (run_sound (init p)).
  intros n. specialize (H n).
  unfold potential_bug, reachable_from, now in *.
  rewrite get_shift in *. simpl get in *.
  rewrite get_map in *. destruct display eqn:Heq1; try easy.
  destruct get as [[[path env] prog]|] eqn:Heq2; simpl in Heq1; try easy.
  destruct (is_error prog) eqn:Heq3.
  apply is_error_correct in Heq3. injection Heq1 as <-.
  now destruct H as [[[path0 env0] prog0] [[[=->->->]|] H2]].
  now destruct is_skip.
Qed.

(** [fin_bugs] is complete:
    For any program [p], if it has a bug,
    [find_bugs p] will eventually find it
*)
Theorem find_bugs_complete:
  forall p s',
    symex.potential_bug (Bcst true, id, p) s' ->
    find_bugs p ⊨ ◊ (bug_found s').
Proof.
  intros p [[path env] prog] [H1 H2].
  pose proof (run_complete _ _ H1) as [n Hn].
  exists n. unfold find_bugs, bug_found, here, now in *.
  rewrite get_shift in *. simpl in *.
  rewrite get_map. unfold init.
  destruct get eqn:Heq1; subst; try easy.
  unfold display.
  destruct is_error eqn:Heq2; try easy.
  destruct prog; try easy.
  apply is_error_correct in H2.
  now rewrite H2 in Heq2.
Qed.

(** A symbolic state denotes a valid bug in
    [p] if all states in its concretization are bugs
*)
Definition ValidBug p σ' :=
  forall σ, Concrete σ' σ -> imp.IsBug p σ.

(** A status message is valid wrt prog [p] 
    if it is a [BugFound] message reporting a [ValidBug]
    or any other kind of status message
*)
Definition ValidStatus p :=
  now (fun st =>
    match st with
    | BugFound σ' => ValidBug p σ'
    | _ => True
    end
  ).

Definition Symbolic σ :=
  now (fun st =>
    match st with
    | BugFound σ' => Concrete σ' σ
    | _ => False
    end
  ).

Theorem relative_completeness:
  forall p σ,
    imp.IsBug p σ -> find_bugs p ⊨ ◊ Symbolic σ.
Proof.
  intros * [(V0 & σ' & [Hsteps Hequiv])%Reach_complete H].
  pose proof (run_complete _ _ Hsteps) as [n Hn].
  exists n.
  unfold find_bugs, Symbolic, bug_found, here, now in *.
  rewrite get_shift in *. simpl in *.
  rewrite get_map. unfold init, display.
  destruct get as [[[π senv] p']|]; auto.
  rewrite <- Hn in Hequiv. destruct σ as [V ?].
  destruct (is_error p') eqn:Herr.
  - now exists V0.
  - destruct Hequiv as [_ [-> ->]].
    apply is_error_Stuck in H.
    now rewrite H in Herr.
Qed.

Theorem relative_soundness:
  forall p,
    find_bugs p ⊨ □ ValidStatus p.
Proof.
  intros.
  (* cleary a reformulation of find_bugs_sound *)
Admitted.

(** ** Main Correctness Theorem !!!! *)

(** THE MAIN RESULT:
    [find_bugs p] is correct !
    This statement means 2 things:
    (1) For any bug in the program [p], the bug is eventually going
        to be discovered
    (2) If a 'bugy path' is discovered, then any concrete
        instance of this path is a bug
*)
(* Theorem find_bugs_correct:
  forall env0 prog0 env1 prog1,
    imp.bug (env0, prog0) (env1, prog1) <->
    exists path2 env2 prog2,
      simpath (env0, prog0) (env1, prog1) (path2, env2, prog2) /\
      (◊ (bug_found (path2, env2, prog2))) (find_bugs prog0).
Proof.
  intros. split.
  + intros (path2 & env2 & prog2 & [Hbug Hpath])%bug_bug.
    do 3 eexists. split; eauto.
    now apply find_bugs_sym_complete.
  + intros (path2 & env2 & prog2 & [Hpath [n Hbug]]).
    pose proof (H1 := find_bugs_sym_sound prog0 n).
    pose proof (H2 := bug_found_bug_here _ _ Hbug).
    specialize (H1 H2).
    unfold bug_from, bug_found, now, here in *.
    rewrite get_shift in *.
    destruct get eqn:Heq; subst; try easy.
    destruct Hpath as [H [-> ->]].
    apply bug_bug.
    do 3 eexists. split; eauto.
    now repeat econstructor.
Qed. *)

(** "termination" of the bugfinding loop:
    If at any point in time [find_bugs p] emits
    a [Finished] token, then the exploration of [p]
    terminated. We encode this property by
    asserting that after the first [Finished] token,
    the only message that the loop will ever send is [Finished]
    (i.e. it cannot find new bugs afterward)
*)
Theorem sound_termination:
  forall p,
    find_bugs p ⊨ □ (done → □ done).
Proof.
  intros p. unfold find_bugs.
  pose proof (run_finished (init p)).
  intros n Hn m.
  assert (Hnone : none (shift n (run (init p)))).
  { unfold none, done, now in Hn |-*. rewrite get_shift in *.
    simpl in *. rewrite get_map in Hn.
    destruct get as [[[path env] prog]|] eqn:Heq1; try easy.
    simpl in Hn. destruct is_error eqn:Heq2; try easy.
  }
  specialize (H n Hnone m). clear Hn Hnone.
  rewrite shift_shift in *.
  unfold done, none, now in *.
  rewrite get_shift in *. simpl in *.
  rewrite get_map. now destruct get eqn:Heq.
Qed.