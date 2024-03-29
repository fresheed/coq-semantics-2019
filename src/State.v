(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Omega.
Require Export Arith Arith.EqNat.
Require Export Id.

From hahn Require Import HahnBase.

Section S.

  Variable A : Set.

  Definition state := list (id * A). 

  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
    st_binds_hd : forall st id x, ((id, x) :: st) / id => x
  | st_binds_tl : forall st id x id' x', id <> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  Definition update (st : state) (id : id) (a : A) : state := (id, a) :: st.

  Notation "st [ x '<-' y ]" := (update st x y) (at level 0).

  Lemma state_deterministic (st : state) (x : id) (n m : A)
        (SN : st / x => n)
        (SM : st / x => m) :
    n = m.
  Proof.
    induction st; inversion SN; subst.
    all: inversion SM; desf.
    apply IHst; desf.
  Qed.    

  Lemma update_eq (st : state) (x : id) (n : A) :
    st [x <- n] / x => n.
  Proof. unfold update. constructor. Qed.

  Lemma update_neq (st : state) (x2 x1 : id) (n m : A)
        (NEQ : x2 <> x1) : st / x1 => m <-> st [x2 <- n] / x1 => m.
  Proof.
    split; intros HH.
    { unfold update. apply st_binds_tl; auto. }
    unfold update in HH. inv HH.
  Qed.

  Lemma update_shadow (st : state) (x1 x2 : id) (n1 n2 m : A) :
    st[x2 <- n1][x2 <- n2] / x1 => m <-> st[x2 <- n2] / x1 => m.
  Proof.
    split; intros HH.
    { unfold update in HH.
      inv HH.
      { apply update_eq. }
      inv H5. apply update_neq; auto. }
    inv HH.
    { apply update_eq. }
    repeat (apply update_neq; auto).
  Qed.

  Lemma update_same (st : state) (x1 x2 : id) (n1 m : A)
        (SN : st / x1 => n1)
        (SM : st / x2 => m) :
    st [x1 <- n1] / x2 => m.
  Proof.
    destruct (id_eq_dec x1 x2) as [|NEQ]; subst.
    2: by apply update_neq.
    assert (m = n1); subst.
    2: by apply update_eq.
    eapply state_deterministic; eauto.
  Qed.

  Lemma update_permute (st : state) (x1 x2 x3 : id) (n1 n2 m : A)
        (NEQ : x2 <> x1)
        (SM : st [x2 <- n1][x1 <- n2] / x3 => m) :
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof.
    destruct (id_eq_dec x1 x3) as [|NN]; subst.
    { apply update_neq; auto.
      inv SM. apply update_eq. }
    destruct (id_eq_dec x2 x3) as [|AA]; subst.
    { inv SM. inv H5. apply update_eq. }
    repeat (apply update_neq; auto).
    inv SM. inv H5.
  Qed.  

End S.
