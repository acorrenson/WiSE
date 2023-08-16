From Coq Require Import List ZArith String Program Lia.
From WiSE Require Import imp utils.
Import ListNotations.

(** Operator names *)
Inductive op :=
  | ADD
  | SUB.

(** Compressed expressions in the E-graph *)
Inductive eexpr :=
  | Eop (op : op) (args : list positive)
  | Ecst (c : Z)
  | Evar (v : string).

(** Nodes of the E-graph *)
Inductive enode : Type :=
  | Enode (key : positive) (exp : eexpr).

(** An E-graph is a list of e-nodes*)
Definition egraph' := list enode.

Fixpoint list_eq (l1 l2 : list positive) :=
  match l1, l2 with
  | [], [] => true
  | x::xs, y::ys =>
    if (x =? y)%positive then
      list_eq xs ys
    else false
  | _, _ => false
  end.

Definition eeq (e1 e2 : eexpr) :=
  match e1, e2 with
  | Eop ADD args1, Eop ADD args2 =>
    list_eq args1 args2
  | Eop SUB args1, Eop SUB args2 =>
    list_eq args1 args2
  | Ecst c1, Ecst c2 => (c1 =? c2)%Z
  | Evar v1, Evar v2 => (v1 =? v2)%string
  | _, _ => false
  end.

Lemma eeq_eq:
  forall e1 e2, eeq e1 e2 = true <-> e1 = e2.
Proof.
Admitted.

Lemma eeq_refl:
  forall e, eeq e e = true.
Proof.
  intros.
  now apply eeq_eq.
Qed.

Lemma eeq_neq:
  forall e1 e2, eeq e1 e2 = false <-> e1 <> e2.
Proof.
Admitted.

(** Find a the *)
Fixpoint egraph_find_ptr (g : egraph') (ptr : positive) :=
  match g with
  | [] => None
  | (Enode lbl _ as nd)::g =>
    if (lbl =? ptr)%positive then Some nd else egraph_find_ptr g ptr
  end.

Definition label (nd : enode) :=
  match nd with
  | Enode lbl  _ => lbl
  end.

Fixpoint egraph_find (g : egraph') (exp : eexpr) : option (positive * enode) :=
  match g with
  | [] => None
  | (Enode lbl exp' as nd)::g =>
    if eeq exp' exp then
      Some (lbl, nd)
    else
      egraph_find g exp
  end.

Fixpoint egraph_get (g : egraph') (id : positive) : option enode :=
  match g with
  | [] => None
  | (Enode lbl _ as nd)::g =>
    if (lbl =? id)%positive then
      Some nd
    else
      egraph_get g id
  end.

Fixpoint repr (g : egraph') (id : positive) : option aexpr :=
  match g with
  | [] => None
  | (Enode lbl exp)::g =>
    if (lbl =? id)%positive then
      match exp with
      | Ecst c => Some (Cst c)
      | Evar v => Some (Var v)
      | Eop ADD args =>
        reduce Add (map (repr g) args)
      | Eop SUB args =>
        reduce Sub (map (repr g) args)
      end
    else
      repr g id
  end.

Definition repr_node (g : egraph') '(Enode _ exp : enode) : option aexpr :=
  match exp with
  | Ecst c => Some (Cst c)
  | Evar v => Some (Var v)
  | Eop ADD args =>
    reduce Add (map (repr g) args)
  | Eop SUB args =>
    reduce Sub (map (repr g) args)
  end.

Lemma get_repr:
  forall g id e,
    repr g id = Some e ->
    exists exp g',
      egraph_find g exp = Some (id, Enode id exp) /\
      repr_node g (Enode id exp) = Some e.
Proof.
  induction g; intros; try easy.
  destruct a as [key exp]. simpl in H.
  destruct (key =? id)%positive eqn:Heq1.
  - apply Pos.eqb_eq in Heq1 as ->.
    exists exp. split.
    + simpl. now rewrite eeq_refl.
    + Opaque repr. simpl.

Record egraph : Type := {
  counter : positive;
  data    :> egraph';
}.

Definition wf_eexpr (g : egraph) (e : eexpr) : Prop :=
  match e with
  | Ecst _ => True
  | Evar _ => True
  | Eop _ args =>
    args <> [] /\
    Forall (fun id => repr g id <> None) args
  end.

Inductive wf_egraph : egraph -> Prop :=
  | wf_egraph_nil :
    wf_egraph (Build_egraph 1 [])
  | wf_egraph_cons c l e:
    wf_egraph (Build_egraph c l) ->
    wf_eexpr (Build_egraph c l) e ->
    (forall key exp, In (Enode key exp) l -> exp <> e) ->
    wf_egraph (Build_egraph (1 + c) (Enode c e::l)).

Lemma reduce_map_not_none:
  forall A B (l : list A) (f : A -> option B) g,
    l <> [] ->
    Forall (fun x => f x <> None) l ->
    reduce g (map f l) <> None.
Proof.
  intros * H1 H2.
  induction H2; try easy.
  - destruct l. simpl.
    now destruct (f x).
    simpl. destruct (f x); try easy.
    destruct (reduce g _) eqn:Heq.
    simpl in *.
    now rewrite Heq.
    exfalso. now apply IHForall.
Qed.

Opaque Pos.add.

Lemma wf_egraph_repr:
  forall g i,
    wf_egraph g ->
    (i <? counter g)%positive = true ->
    repr g i <> None.
Proof.
  intros * H1 H2 Hcontr.
  dependent induction H1. cbn in *.
  - apply Pos.ltb_lt in H2.
    lia.
  - cbn in *.
    destruct (c =? i)%positive eqn:Heq.
    apply Pos.eqb_eq in Heq as ->.
    destruct e as [[|] args | | ]; try easy.
    + destruct H as [H_1 H_2].
      enough (reduce Add (map (repr l) args) <> None); auto.
      now apply reduce_map_not_none.
    + destruct H as [H_1 H_2].
      enough (reduce Sub (map (repr l) args) <> None); auto.
      now apply reduce_map_not_none.
    + apply Pos.eqb_neq in Heq.
      apply Pos.ltb_lt in H2.
      assert (Hlt : (i <? c = true)%positive).
      apply Pos.ltb_lt. lia.
      now apply IHwf_egraph.
Qed.

Definition register (g : egraph) (e : eexpr) : egraph * positive :=
  match egraph_find g e with
  | Some (i, _) => (g, i)
  | None =>
    let lbl' := (1 + counter g)%positive in
    let lbl := counter g in
    (Build_egraph lbl' (Enode lbl e::data g), lbl)
  end.



Lemma In_find:
  forall g key exp,
    In (Enode key exp) g ->
    egraph_find g exp <> None.
Proof.
  intros.
  induction g; try easy.
  + inversion H; subst.
    simpl. now rewrite eeq_refl.
    simpl. destruct a.
    destruct eeq eqn:Heq; try easy.
    now apply IHg.
Qed.

Lemma register_wf:
  forall g,
    wf_egraph g ->
    forall g' i e,
      wf_eexpr g e ->
      register g e = (g', i) ->
      wf_egraph g'.
Proof.
  intros [c g] * H1.
  Opaque Pos.add.
  induction H1; intros * H2 H3.
  - injection H3 as <- <-.
    econstructor; auto.
    econstructor.
  - unfold register in H3.
    destruct egraph_find as [[id nd]|]eqn:Hfind.
  + injection H3 as <- <-.
    now econstructor.
  + injection H3 as <- <-. simpl in *.
    destruct eeq eqn:Heq; try easy.
    apply eeq_neq in Heq.
    repeat econstructor; auto.
    intros. inversion H3.
    * now injection H4 as -> ->.
    * intros <-. apply In_find in H4.
      now rewrite Hfind in H4.
Qed.

Lemma init_wf:
  wf_egraph (Build_egraph 1 []).
Proof.
  econstructor.
Qed.

Example test :=
  let eg := Build_egraph 1 [] in
  let '(eg, i1) := register eg (Ecst 10%Z) in
  let '(eg, i2) := register eg (Ecst 11%Z) in
  let '(eg, i3) := register eg (Eop ADD [i1; i2]) in
  let '(eg, i4) := register eg (Eop SUB [i3; i3]) in
  let '(eg, i5) := register eg (Eop SUB [i3; i3]) in
  (eg, repr eg i5).
Compute test.

Fixpoint register_aexpr (g : egraph) (e : aexpr) : egraph * positive :=
  match e with
  | Cst c => register g (Ecst c)
  | Var v => register g (Evar v)
  | Add e1 e2 =>
    let '(g, i1) := register_aexpr g e1 in
    let '(g, i2) := register_aexpr g e2 in
    register g (Eop ADD [i1; i2])
  | Sub e1 e2 =>
    let '(g, i1) := register_aexpr g e1 in
    let '(g, i2) := register_aexpr g e2 in
    register g (Eop SUB [i1; i2])
  end.

Theorem repr_find:
  forall g id,
    repr g id <> None ->
    exists exp, In (Enode id exp) g.
Proof.
  intros.
  induction g; try easy.
  - destruct a as [lbl exp]. simpl in H.
    destruct (lbl =? id)%positive eqn:Heq.
  + apply Pos.eqb_eq in Heq as ->.
    exists exp. now left.
  + specialize (IHg H) as (exp' & H').
    exists exp'. now right.
Qed.

Theorem wf_egraph_id_lt_counter:
  forall g,
    wf_egraph g ->
    Forall (fun '(Enode lbl _) => (lbl < counter g)%positive) (data g).
Proof.
  intros.
  dependent induction H.
  + econstructor.
  + econstructor; simpl in *. lia.
    apply Forall_forall. intros [key exp] Hx.
    rewrite Forall_forall in IHwf_egraph.
    specialize (IHwf_egraph (Enode key exp) Hx).
    simpl in *. lia.
Qed.

Theorem egraph_find_in:
  forall g e id nd,
    egraph_find g e = Some (id, nd) ->
    In (Enode id e) g.
Proof.
  intros.
  induction g; try easy.
  simpl in *. destruct a as [key exp].
  destruct (eeq exp e) eqn:Heq.
  - apply eeq_eq in Heq as <-.
    injection H as -> ->. now left.
  - right. auto.
Qed.

Theorem egraph_get_in:
  forall g e id id',
    egraph_get g id = Some (Enode id' e) ->
    id = id' /\ In (Enode id e) g.
Proof.
  intros.
  induction g; try easy.
  simpl in *. destruct a as [key exp].
  destruct (key =? id)%positive eqn:Heq.
  - apply Pos.eqb_eq in Heq as <-.
    injection H as -> ->. auto.
  - specialize (IHg H) as [H1 H2]. auto.
Qed.

Theorem egraph_find_correct:
  forall g e id nd,
    egraph_find g e = Some (id, nd) ->
    nd = Enode id e.
Proof.
  induction g; intros; try easy.
  simpl in *. destruct a as [key exp].
  destruct eeq eqn:Heq.
  - apply eeq_eq in Heq as <-.
    now injection H as -> ->.
  - now apply IHg in H.
Qed.

Theorem egraph_get_find:
  forall g id key exp,
    wf_egraph g ->
    egraph_get g id = Some (Enode key exp) ->
    id = key /\ egraph_find g exp = Some (id, Enode key exp).
Proof.
  intros [c g].
  induction g in c |-*; intros * Hwf Hget; try easy.
  split.
  - destruct a as [key' exp']. simpl in *.
    destruct (key' =? id)%positive eqn:Heq.
    apply Pos.eqb_eq in Heq as ->.
    now injection Hget as ->.
    inversion Hwf; subst.
    eapply IHg; eauto.
  - destruct a as [key' exp']. simpl in *.
    destruct (key' =? id)%positive eqn:Heq.
    apply Pos.eqb_eq in Heq as ->.
    injection Hget as -> ->.
    now rewrite eeq_refl.
    apply Pos.eqb_neq in Heq.
    destruct eeq eqn:Heq'.
    apply eeq_eq in Heq' as ->.
    inversion Hwf; subst.
    apply egraph_get_in in Hget as [->].
    now apply H5 in H.
    inversion Hwf; subst.
    eapply IHg; eauto.
Qed.

Inductive MonoKey : egraph' -> Prop :=
  | mono_nil  : MonoKey []
  | mono_cons l key exp :
    MonoKey l ->
    (forall key' exp', In (Enode key' exp') l -> (key > key')%positive) ->
    MonoKey (Enode key exp::l).

Inductive NoDupKey : egraph' -> Prop :=
  | no_dup_nil  : NoDupKey []
  | no_dup_cons l key exp :
    NoDupKey l ->
    (forall key' exp', In (Enode key' exp') l -> key' <> key) ->
    NoDupKey (Enode key exp::l).

Theorem mono_no_dup:
  forall g, MonoKey g -> NoDupKey g.
Proof.
  induction 1.
  + econstructor.
  + econstructor; auto.
    intros * Hin ->.
    apply H0 in Hin. lia.
Qed.

Theorem wf_egraph_no_dup_key:
  forall g,
    wf_egraph g ->
    MonoKey g.
Proof.
  intros [c g] Hwf.
  induction g in c, Hwf |-*.
  - repeat econstructor.
  - inversion Hwf; subst.
    specialize (IHg _ H2).
    inversion IHg; simpl in *; subst.
  + now econstructor.
  + repeat econstructor; auto.
    intros. inversion H2; subst.
    inversion H1.
    injection H5 as -> ->. lia.
    specialize (H0 _ _ H5). lia.
Qed.

Theorem egraph_find_get:
  forall g key1 exp1 key2 exp2,
    wf_egraph g ->
    egraph_find g exp1 = Some (key1, Enode key2 exp2) ->
    key1 = key2 /\ exp1 = exp2 /\ egraph_get g key1 = Some (Enode key1 exp1).
Proof.
  intros [c g].
  induction g in c |-*; intros * Hwf Hget; try easy.
  repeat split.
  - destruct a as [key' exp']. simpl in *.
    destruct eeq eqn:Heq.
    apply eeq_eq in Heq as ->.
    now injection Hget as ->.
    inversion Hwf; subst.
    eapply IHg; eauto.
  - destruct a as [key' exp']. simpl in *.
    destruct eeq eqn:Heq.
    apply eeq_eq in Heq as ->.
    now injection Hget as ->.
    apply egraph_find_correct in Hget.
    now injection Hget as ->.
  - destruct a as [key' exp']. simpl in *.
    destruct (key' =? key1)%positive eqn:Heq.
    apply Pos.eqb_eq in Heq as ->.
    destruct eeq eqn:Heq.
    apply eeq_eq in Heq as ->.
    now injection Hget as ->.
    apply wf_egraph_no_dup_key in Hwf.
    inversion Hwf; subst.
    apply egraph_find_in in Hget.
    specialize (H3 _ _ Hget). lia.
    destruct eeq eqn:Heq'.
    injection Hget as -> ->.
    now rewrite Pos.eqb_neq in Heq.
    inversion Hwf; subst.
    eapply IHg; eauto.
Qed.

Theorem register_mono':
  forall e g g' i,
    wf_egraph g ->
    register g e = (g', i) ->
    (i < counter g')%positive.
Proof.
  intros * H1 H2.
  unfold register in H2.
  destruct egraph_find as [[id nd]|] eqn:Heq.
  - injection H2 as <- <-.
    apply egraph_find_in in Heq.
    pose proof (wf_egraph_id_lt_counter _ H1).
    rewrite Forall_forall in H.
    apply (H _ Heq).
  - injection H2 as <- <-. simpl.
    lia.
Qed.

Theorem register_mono:
  forall e g g' i,
    register g e = (g', i) ->
    (counter g <= counter g')%positive.
Proof.
  intros * H.
  induction e; intros.
  - unfold register in H.
    destruct egraph_find as [[id nd]|].
    injection H as <- <-. lia.
    injection H as <- <-. simpl. lia.
  - unfold register in H.
    destruct egraph_find as [[id nd]|].
    injection H as <- <-. lia.
    injection H as <- <-. simpl. lia.
  - unfold register in H.
    destruct egraph_find as [[id nd]|].
    injection H as <- <-. lia.
    injection H as <- <-. simpl. lia.
Qed.

Theorem register_aexpr_mono':
  forall e g g' i,
    register_aexpr g e = (g', i) ->
    (counter g <= counter g')%positive.
Proof.
  induction e; intros.
  - simpl in H. unfold register in H.
    destruct egraph_find as [[id nd]|] eqn:Heq.
    injection H as -> ->. lia.
    injection H as <- <-. simpl. lia.
  - simpl in H. unfold register in H.
    destruct egraph_find as [[id nd]|] eqn:Heq.
    injection H as -> ->. lia.
    injection H as <- <-. simpl. lia.
  - simpl in H.
    destruct (register_aexpr g e1) as [g1 i1] eqn:Heq1.
    destruct (register_aexpr g1 e2) as [g2 i2] eqn:Heq2.
    specialize (IHe1 g g1 i1 Heq1).
    specialize (IHe2 g1 g2 i2 Heq2).
    apply register_mono in H.
    lia.
  - simpl in H.
    destruct (register_aexpr g e1) as [g1 i1] eqn:Heq1.
    destruct (register_aexpr g1 e2) as [g2 i2] eqn:Heq2.
    specialize (IHe1 g g1 i1 Heq1).
    specialize (IHe2 g1 g2 i2 Heq2).
    apply register_mono in H.
    lia.
Qed.

Theorem register_aexpr_wf:
  forall e g g' i,
    wf_egraph g ->
    register_aexpr g e = (g', i) ->
    wf_egraph g' /\ (i < counter g')%positive.
Proof.
  induction e; intros [c g] * H1 H2.
  - split.
  + eapply register_wf; eauto. econstructor.
  + simpl in H2. eapply register_mono'; eauto.
  - split.
  + eapply register_wf; eauto. econstructor.
  + simpl in H2. eapply register_mono'; eauto.
  - simpl in H2.
    destruct (register_aexpr _ e1) as [g1 i1] eqn:Heq1.
    destruct (register_aexpr _ e2) as [g2 i2] eqn:Heq2.
    pose proof (IHe1 _ _ _ H1 Heq1) as [Hwf1_1 Hwf1_2].
    pose proof (IHe2 _ _ _ Hwf1_1 Heq2) as [Hwf2_1 Hwf2_2].
    split.
    eapply register_wf; eauto.
    econstructor; try easy.
    repeat econstructor; try easy.
    apply wf_egraph_repr; auto.
    apply Pos.ltb_lt.
    eapply Pos.lt_le_trans; eauto.
    eapply register_aexpr_mono'; eauto.
    apply wf_egraph_repr; auto.
    apply Pos.ltb_lt.
    eapply Pos.lt_le_trans; eauto.
    reflexivity.
    eapply register_mono'; eauto.
  - simpl in H2.
    destruct (register_aexpr _ e1) as [g1 i1] eqn:Heq1.
    destruct (register_aexpr _ e2) as [g2 i2] eqn:Heq2.
    pose proof (IHe1 _ _ _ H1 Heq1) as [Hwf1_1 Hwf1_2].
    pose proof (IHe2 _ _ _ Hwf1_1 Heq2) as [Hwf2_1 Hwf2_2].
    split.
    eapply register_wf; eauto.
    econstructor; try easy.
    repeat econstructor; try easy.
    apply wf_egraph_repr; auto.
    apply Pos.ltb_lt.
    eapply Pos.lt_le_trans; eauto.
    eapply register_aexpr_mono'; eauto.
    apply wf_egraph_repr; auto.
    apply Pos.ltb_lt.
    eapply Pos.lt_le_trans; eauto.
    reflexivity.
    eapply register_mono'; eauto.
Qed.

Theorem register_correct_1:
  forall e g,
    wf_egraph g ->
    let '(g', i) := register g e in
    egraph_get g' i = Some (Enode i e).
Proof.
  intros.
  unfold register.
  destruct egraph_find as [[id nd]|]eqn:Heq.
  + rewrite (egraph_find_correct _ _ _ _ Heq) in Heq.
    eapply egraph_find_get; eauto.
  + simpl. now rewrite Pos.eqb_refl.
Qed.

Theorem egraph_repr_evar:
  forall g v,
    wf_egraph g ->
    let '(g', i) := register_aexpr g (Var v) in
    repr g' i = Some (Var v).
Proof.
  intros [c g] * Hwf.
  unfold register_aexpr, register.
  destruct egraph_find as [[id nd]|]eqn:Hfind.
  - simpl in *.
   induction g in c, id, nd, Hfind, Hwf |-*; try easy.
    destruct a as [key' exp']. simpl in Hfind.
    destruct eeq eqn:Heq.
    + apply eeq_eq in Heq as ->.
      injection Hfind as ->. simpl.
      now rewrite Pos.eqb_refl.
    + apply eeq_neq in Heq.
      destruct nd as [key exp].
      rewrite (egraph_find_correct _ _ _ _ Hfind) in Hfind.

    
    destruct (key' =? id)%positive eqn:Heq'.
      apply Pos.eqb_eq in Heq' as ->.
      destruct exp'.
    

Theorem egraph_correct:
  forall e g,
    wf_egraph g ->
    let '(g', i) := register_aexpr g e in
    repr g' i = Some e.
Proof.
  induction e; intros.
  - simpl. unfold register.
    destruct egraph_find as [[id nd]|]eqn:Heq.
  + destruct g as [c g]. simpl in *.
    rewrite (egraph_find_correct _ _ _ _ Heq) in Heq.
    induction g as [|[key exp] g IH]; try easy.
    simpl in *.
    destruct eeq in Heq.
    injection Heq as _ -> ->.
    now rewrite Pos.eqb_refl.
    destruct (key =? id)%positive eqn:Heq2.
    apply Pos.eqb_eq in Heq2 as ->.
    apply wf_egraph_no_dup_key in H.
    inversion H; subst.
    apply egraph_find_in in Heq.
    apply H4 in Heq. lia.
    inversion H; subst.
    apply IH; auto.


    destruct eeq eqn:Heq1.
    apply eeq_eq in Heq1 as ->.
    now rewrite Pos.eqb_refl.
    destruct exp.

  admit. (* by lemma egraph_find <-> repr *)
  + simpl. now rewrite Pos.eqb_refl.
  - simpl. unfold register.
    destruct egraph_find as [[id nd]|]eqn:Heq.
  + admit. (* by lemma egraph_find <-> repr *)
  + simpl. now rewrite Pos.eqb_refl.
  - simpl. do 2 unfold register.
    destruct (register_aexpr g e1) as [g1 i1] eqn:Heq1.
    destruct (register_aexpr g1 e2) as [g2 i2] eqn:Heq2.
    destruct egraph_find as [[id nd]|]eqn:Heq.
  + pose proof (register_wf g H).
    specialize (IHe1 g H).
    rewrite Heq1 in IHe1.
    specialize (IHe2 g1).
    





