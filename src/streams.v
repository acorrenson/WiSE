From Coq Require Import List Lia.
From WiSE Require Import equalities.
Import ListNotations.

(** * A library to manipulate infinite streams *)

CoInductive stream (A : Type) : Type :=
  | scons (x : A) (xs : stream A) : stream A.
Arguments scons { _ }.

Definition force {A} (s : stream A) : stream A :=
  match s with
  | scons x xs => scons x xs
  end.

Lemma force_id:
  forall A (s : stream A), force s = s.
Proof.
  intros. now destruct s.
Qed.

Ltac force :=
  rewrite <- force_id; simpl force.

(** Get the nth element of a stream *)
Fixpoint get {A} (n : nat) (s : stream A) : A :=
  match n, s with 
  | 0, scons x _ => x
  | S n, scons _ xs => get n xs
  end.

Fixpoint shift {A} (n : nat) (s : stream A) : stream A :=
  match n, s with
  | 0, _ => s
  | S n, scons _ xs => shift n xs
  end.

Lemma get_shift:
  forall A (s : stream A) n m, get n (shift m s) = get (n + m) s.
Proof.
  intros *.
  induction m in s |-*.
  - now replace (n + 0) with n by lia.
  - simpl. destruct s. rewrite IHm.
    now replace (n + S m) with (S (n + m)) by lia.
Qed.

Lemma shift_eq:
  forall A n (x : A) xs, shift (S n) (scons x xs) = shift n xs.
Proof.
  auto.
Qed.

(** Peek the first [n] elements of a stream *)
Fixpoint peek {A} (n : nat) (s : stream A) : list A :=
  match n, s with 
  | 0, _ => []
  | S n, scons x xs => x::peek n xs
  end.

(** Apply a function to a stream elementwise *)
CoFixpoint map {A B} (f : A -> B) (s : stream A) : stream B :=
  match s with 
  | scons x xs => scons (f x) (map f xs)
  end.

Lemma map_eq:
  forall A B (f : A -> B) x xs, map f (scons x xs) = scons (f x) (map f xs).
Proof.
  intros. now rewrite <- force_id at 1.
Qed.

(** Filter out some element of a stream *)
CoFixpoint filter {A} (f : A -> bool) (s : stream A) : stream (option A) :=
  match s with
  | scons x xs =>
    if f x then scons None (filter f xs)
    else scons (Some x) (filter f xs)
  end.

(** Correctness of [filter] *)
Lemma get_filter :
  forall A (f : A -> bool) (s : stream A) n,
    if f (get n s) then
      get n (filter f s) = None
    else
      get n (filter f s) = Some (get n s).
Proof.
  intros A f s n.
  induction n in s |-*.
  - simpl. now destruct s, (f x).
  - destruct s; simpl.
    destruct (f (get n s)) eqn:Heq.
    + specialize (IHn s). rewrite Heq in IHn.
      now destruct (f x).
    + specialize (IHn s). rewrite Heq in IHn.
      now destruct (f x).
Qed.

Lemma get_map :
  forall n A B (f : A -> B) (s : stream A),
      get n (map f s) = f (get n s).
Proof.
  induction n.
  - now destruct s.
  - destruct s. simpl in *. now rewrite IHn.
Qed.

(** ** Predicates Over Streams *)

Module LTL.
  Lemma shift_shift:
    forall A m n (str : stream A), shift n (shift m str) = shift (n + m) str.
  Proof.
    induction m; auto.
    - intros. now replace (n + 0) with n by lia.
    - intros n str. replace (n + S m) with (S (n + m)) by lia.
      destruct str. rewrite shift_eq.
      now rewrite IHm.
  Qed.
  Definition t {A} : Type := (stream A -> Prop).
  Definition now {A} (P : A -> Prop) : t :=
    fun (s : stream A) => P (get 0 s).
  Definition globally {A} (P : t) : t :=
    fun (s : stream A) => forall n, P (shift n s).
  Definition eventually {A} (P : t) : t :=
    fun (s : stream A) => exists n, P (shift n s).
  Definition imp {A} (P Q : t) : t :=
    fun (s : stream A) => P s -> Q s.
  Definition or {A} (P Q : t) : t :=
    fun (s : stream A) => P s \/ Q s.
  Definition and {A} (P Q : t) : t :=
    fun (s : stream A) => P s /\ Q s.
  Definition not {A} (P : t) : t :=
    fun (s : stream A) => ~P s.
  Definition next {A} (P : t) : t :=
    fun (s : stream A) => P (shift 1 s).
  
  Notation "□ P" := (globally P) (at level 80).
  Notation "◊ P" := (eventually P) (at level 80).
  Notation "◯ P" := (next P) (at level 80).
  Notation "P → Q" := (imp P Q) (at level 80).
  Notation "¬ Q" := (not Q) (at level 80).
  Notation "P ∨ Q" := (or P Q) (at level 80).
  Notation "P ∧ Q" := (and P Q) (at level 80).
  Notation "! P" := (now P) (at level 80).
  Notation "!! p" := (! (fun x => x = p)) (at level 80).
  Check (_ → (□ ◯ _)).

  Theorem globally_map:
    forall A B (f : A -> B) (P : B -> Prop) str,
      (□ (now (fun x => P (f x)))) str ->
      (□ (now P)) (map f str).
  Proof.
    intros * H n.
    specialize (H n).
    unfold now in *. rewrite get_shift in *.
    simpl in *.
    now rewrite get_map.
  Qed.

  Definition model {A} (s : stream A) (f : @t A) : Prop :=
    f s.
  Notation "α ⊨ φ" := (model α φ) (at level 80).
End LTL.

(** The current value satisfies [P] *)
Definition now {A} (s : stream A) (P : A -> Prop) : Prop :=
  P (get 0 s).

  
(** Globally, [P] holds for all values of the stream *)
Definition globally {A} (s : stream A) (P : A -> Prop) : Prop :=
  forall n, P (get n s).

(** Eventually, a [P] value will be enumerated *)
Definition eventually {A} (s : stream A) (P : A -> Prop) : Prop :=  
  exists n, P (get n s).

(** [P] holds untill [Q] holds *)
Definition untill {A} (s : stream A) (P Q : A -> Prop) :=
  exists n, Q (get n s) /\ forall m, 0 <= m <= n -> P (get n s).

(** ** Examples *)

(** Type of enumerators over a type [A] *)
Definition enum A : Type := nat -> A.

(** Extensional equality of streams *)
Definition stream_equ {A} (s1 s2 : stream A) :=
  forall n, get n s1 = get n s2.

(** Extensional equality of enumerators *)
Definition enum_equ {A} (f1 f2 : enum A) :=
  forall n, f1 n = f2 n.

(** Instances of [Eq] *)
Instance stream_Eq {A} : @Eq (stream A) := EQ _ stream_equ.
Instance fun_Eq {A} : @Eq (enum A) := EQ _ enum_equ.

(** Converting enumerators into streams *)
CoFixpoint func_to_stream {A} (n : nat) (f : nat -> A) : stream A :=
  scons (f n) (func_to_stream (S n) f).

(** Applying [func_to_stream] gives an equivalent [stream] *)
Lemma func_to_stream_correct {A} :
  forall n (f : nat -> A) m,
    get m (func_to_stream n f) = f (n + m).
Proof.
  intros.
  induction m in n |-*.
  - now replace (n + 0) with n by lia.
  - simpl get. rewrite IHm.
    now replace (n + S m) with (S n + m) by lia.
Qed.

(** [stream A] and [enum A] are isomorphic *)
Theorem stream_func_iso {A}:
  stream A ≃ (enum A).
Proof.
  exists (fun x n => get n x), (func_to_stream 0).
  split.
  - intros x n.
    now rewrite func_to_stream_correct.
  - intros f n.
    now rewrite func_to_stream_correct.
Qed.