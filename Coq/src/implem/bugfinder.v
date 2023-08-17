From Coq Require Import List Lia String ZArith.
From WiSE Require Import streams imp symbolic.symex.
Import ListNotations.

(** * Implementation of a naive bug finder for [IMP] *)

(** A task list is a list of programs to be executed in a given symbolic state. *)
Definition tasks := list sym_state.

(** A [status] corresponds to the current state of the bugfinding loop *)
Inductive status :=
  | BugFound (s : sym_state)
  | Pending
  | Finished.

Definition then_do q '(((path, env), p) : sym_state) :=
  ((path, env), Seq p q).

(** Executing a task according to [sym_step] *)
Fixpoint expand path env prog : list sym_state :=
  match prog with
  | Skip => []
  | Aff x e =>
    [(path, sym_update env x (sym_aeval env e), Skip)]
  | Err => []
  | Ite b p1 p2 =>
    [
      (Band path (sym_beval env b), env, p1);
      (Band path (Bnot (sym_beval env b)), env, p2)
    ]
  | Loop b p =>
    [
      (Band path (sym_beval env b), env, Seq p (Loop b p));
      (Band path (Bnot (sym_beval env b)), env, Skip)
    ]
  | Seq Skip p2 => [(path, env, p2)]
  | Seq p1 p2 =>
    List.map (then_do p2) (expand path env p1)
  end.

(** Bugfinding loop: at every iteration, a task is choosen and then executed.
    If the execution results in an error, a [BugFound] message is
    emitted. If executing the task terminates in a state [s] without error,
    a message [Clear s] is emitted. If executing the task generates a list [l] of subtasks,
    then the loop signals that further computations are pending and add [l] to the worklist.
    Finally, if the task list is empty, the loop emits the token [Finished] continuously.
*)
CoFixpoint run (l : tasks) : stream (option sym_state) :=
  match l with
  | [] => scons None (run [])
  | ((path, env), prog)::next =>
    let next_next := expand path env prog in
    scons (Some (path, env, prog)) (run (next ++ next_next))
  end.

(** [run_n] predicts the tasks list after n iteration *)
Fixpoint run_n (n : nat) (tasks : list sym_state) : list sym_state :=
  match n, tasks with
  | 0, _ => tasks
  | S n, [] => []
  | S n, (path, env, prog)::next =>
    let next_next := expand path env prog in
    run_n n (next ++ next_next)
  end.

Definition display (st : option sym_state) : status :=
  match st with
  | None => Finished
  | Some (path, env, prog) =>
    if is_error prog then BugFound (path, env, prog)
    else Pending
    (* else if is_skip prog then Clear (path, env, prog)
    else Pending (path, env, prog) *)
  end.

Definition init (p : IMP) : list sym_state :=
  [((Bcst true, id), p)].

Definition find_bugs (p : IMP) : stream status :=
  map display (run (init p)).

Definition init_assuming (p : IMP) (cond : bexpr) :=
  [(cond, id, p)].

Definition find_bugs_assuming (p : IMP) (cond : bexpr) : stream status :=
  map display (run (init_assuming p cond)).

(** Examples *)
Section Examples.

Section Simple.
Example my_prog :=
  Ite 
    (Beq (Var "x"%string) (Cst 0%Z))
    Err
    Skip.
Compute (peek 10 (find_bugs my_prog)).
Example a := (Var "a"%string).
Example b := (Var "b"%string).
Example olda := (Var "olda"%string).
Example oldb := (Var "oldb"%string).
Example trivial_assertion :=
  Seq
    (Aff "a"%string b)
    (Assert (Bnot (Beq a b))).
Compute (peek 10 (find_bugs trivial_assertion)).
End Simple.

Section Gcd.

(*
function gcd(a, b)
    while a ≠ b 
        if a <= b
            b := b − a
        else
            a := a − b
    return a
*)

Example gcd :=
  Loop
    (Bnot (Beq a b))
      (Ite
        (Ble a b)
        (Aff "b"%string (Sub b a))
        (Aff "a"%string (Sub a b))).

Example init_store (x : ident) : Z :=
  match x with
  | "a"%string => 9
  | "b"%string => 6
  | _ => 0
  end.

(* gcd(9, 6) --> (3, 3) *)
Example execute_gcd:
  exec 
    init_store 
    gcd 
    (update (update init_store "a"%string 3%Z) "b"%string 3%Z).
Proof.
  unfold gcd.
  
  (* First Iteration *)
  apply exec_loop_true with 
    (update init_store "a"%string 3%Z); 
  auto.
  1: (* correctness of provided store *)
  apply exec_Ite_false; auto.
  apply exec_Aff.
  auto.
  
  (* Second Iteration *)
  apply exec_loop_true with 
    (update (update init_store "a"%string 3%Z) "b"%string 3%Z); auto.

  1: (* correctness of provided store *)
  apply exec_Ite_true; auto.
  apply exec_Aff.
  auto.

  (* Termination *)
  apply exec_loop_false.
  auto.
Qed.
  
Example a0 := (Var "a0"%string).
Example b0 := (Var "b0"%string).

(* Now, a correct version of `gcd` with assertions. *)

(*
function gcd(a, b)
    while a ≠ b 
        if a <= b
            b := b − a
        else
            a := a − b
        
        assert a + b + 1 <= \old(a) + \old(b)
    return a
*)

Example gcd_assertions :=
  Loop
    (Bnot (Beq a b))
    (Seq
      (Aff "a0"%string a)
      (Seq
        (Aff "b0"%string b)
        (Seq
          (Ite
             (Ble a b)
             (Aff "b"%string (Sub b a))
             (Aff "a"%string (Sub a b)))
          (Assert (Ble (Add (Add a b) (Cst 1%Z)) (Add a0 b0)))))).
Compute (peek 15 (find_bugs gcd_assertions)).


Example init_store' (x : ident) : Z :=
  match x with
  | "a"%string => 4
  | "b"%string => 2
  | _ => 0
  end.

(* gcd(4, 2) --> (2, 2) *)
Example execute_gcd_noerr:
  exec 
    init_store' 
    gcd_assertions 
    (update 
      (update 
        (update init_store' "a0"%string 4)
        "b0"%string 2)
      "a"%string 2).
  unfold gcd_assertions.
  
  (* First Iteration *)
  apply exec_loop_true with 
    (update 
      (update 
        (update init_store' "a0"%string 4)
        "b0"%string 2)
      "a"%string 2); 
  auto.

  1: (* correctness of provided store *)
  (* `a0 = a` *)
  apply exec_Seq with (update init_store' "a0"%string 4%Z);
  try constructor; auto.

  (* `b0 = b` *)
  apply exec_Seq with 
    (update (update init_store' "a0"%string 4%Z) "b0"%string 2%Z);
  try constructor; auto.
 
  (* if... ; ... *)
  apply exec_Seq with 
    (update
      (update 
        (update init_store' "a0"%string 4%Z) 
        "b0"%string 2%Z)
      "a"%string 2%Z).

  1: (* if ... *)
  apply exec_Ite_false; auto.
  apply exec_Aff.
  auto.

  (* assert ... *)
  unfold Assert.
  apply exec_Ite_true; auto.
  apply exec_Skip.

  (* Termination *)
  apply exec_loop_false.
  auto.
Qed.

(* Now, a *buggy* version of `gcd` with assertions. *)

(*
function gcd_buggy(a, b)
    while a ≠ b 
        if a <= b
            b := b − a
        else
            a := a + b  // Should be `a - b`
        
        assert a + b + 1 <= \old(a) + \old(b)
    return a
*)

Example gcd_buggy :=
  Loop
    (Bnot (Beq a b))
    (Seq
      (Aff "a0"%string a)
      (Seq
        (Aff "b0"%string b)
        (Seq
          (Ite
             (Ble a b)
             (Aff "b"%string (Sub b a))
             (Aff "a"%string (Add a b)))
          (Assert (Ble (Add (Add a b) (Cst 1%Z)) (Add a0 b0)))))).

(* gcd_buggy(4, 2) --> Err *)
Example execute_gcd_err:
  forall s, ~ exec init_store' gcd_buggy s.
  intros s.
  unfold not; intros.
  inversion H; try (inversion H4; fail).

  inversion H4; clear H4 H2; subst; simpl in *.
  inversion H12; clear H12; subst; simpl in *.
  inversion H5; clear H5; subst; simpl in *.
  inversion H4; clear H4; subst; simpl in *.
  
  - (* then case *)
    inversion H3; clear H3; subst; simpl in *.
    inversion H10; clear H10; subst; simpl in *.
    inversion H9.
  - (* else case *)
    inversion H11; clear H11; subst; simpl in *.
    inversion H3; clear H3; subst; simpl in *.
    inversion H10; clear H10; subst; simpl in *.
    inversion H8; clear H8; subst; simpl in *; inversion H5.
    inversion H7.
Qed.
Notation "'Bug' π" := (BugFound (π, _, _)) (at level 80).
Eval compute in (peek 20 (find_bugs gcd_buggy)).
End Gcd.

End Examples.