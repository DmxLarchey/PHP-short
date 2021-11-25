(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREER SOFTWARE LICENSE AGREEMENT         *)
(**************************************************************)

Require Import Arith List Permutation Utf8.

Import ListNotations.

Set Implicit Arguments.

Local Infix "~ₚ" := (@Permutation _) (at level 70, no associativity).

Local Hint Constructors Permutation : core.
Local Hint Resolve Permutation_sym Permutation_middle Permutation_app : core.

Local Notation "⌊ l ⌋" := (length l) (at level 0, format "⌊ l ⌋").
Local Infix "∈" := In (at level 70, no associativity).
Local Infix "⊆" := incl (at level 70, no associativity).

Notation "'lhd' l" := (∃ x m, l ~ₚ x::x::m) (at level 1).

Local Reserved Notation "x ↑ n" (at level 1, left associativity, format "x ↑ n").

Section php_short.

  Variable (X : Type).

  Implicit Types (x : X) (l : list X).

  Hint Resolve incl_nil_l incl_cons
               in_eq in_cons incl_tl
               incl_refl incl_tran : core.

  (** Repeat facts*)

  Fixpoint repeat (x:X) n :=
    match n with
      | 0 => nil
      | S n => x::x↑n
    end
  where "x ↑ n" := (repeat x n).

  Fact incl_sg_repeat l x : l ⊆ [x] → { n | l = x↑n }.
  Proof. 
    intros H; exists ⌊l⌋; revert H.
    induction l as [ | y l IHl ]; simpl; auto. 
    intros H; apply incl_cons_inv in H as [ [ <- | [] ] ]; f_equal; auto.
  Qed.

  (** Membership vs permutation *)

  Fact In_perm x l : x ∈ l → ∃m, l ~ₚ x::m.
  Proof. intro H; apply in_split in H as (? & ? & ->); eauto. Qed.

  Lemma incl_app_perm m l r : m ⊆ l++r → ∃ mₗ mᵣ, m ~ₚ mₗ++mᵣ ∧ mₗ ⊆ l ∧ mᵣ ⊆ r.
  Proof.
    induction m as [ | x m IHm ].
    + exists [], []; auto.
    + intros H; apply incl_cons_inv in H as (H1 & H2).
      apply IHm in H2 as (a & b & ? & ? & ?).
      apply in_app_or in H1 as [H1 | H1];
        destruct In_perm with (1 := H1).
      * exists (x::a), b; repeat split; simpl; auto.
      * exists a, (x::b); repeat split; eauto.
  Qed.

  Corollary incl_cons_perm m x l : m ⊆ x::l → ∃ n m', m ~ₚ x↑n++m' ∧ m' ⊆ l.
  Proof. 
    intros H. 
    apply incl_app_perm with (l := [_]) in H
      as (? & ? & ? & H & ?). 
    apply incl_sg_repeat in H as (? & ->); eauto.
  Qed.

  Theorem php_short l m : l ⊆ m → ⌊m⌋ < ⌊l⌋ → lhd l.
  Proof.
    revert l; induction m as [ | x m IHm ]; intros l H1 H2.
    + exfalso; revert H2; apply incl_l_nil in H1 as ->.
      apply lt_irrefl.
    + apply incl_cons_perm in H1 
        as ([ | [ | n ] ] & l' & H1 & H3); 
        simpl in *; eauto.
      * destruct (IHm _ H3) as (y & m' & ?).
        - apply Permutation_length in H1 as <-.
          apply le_lt_trans with (2 := H2), le_n_Sn.
        - exists y, m'; eauto.
      * destruct (IHm _ H3) as (y & m' & ?).
        - revert H2; apply Permutation_length in H1 as ->; simpl.
          apply lt_S_n.
        - exists y, (x::m').
          apply perm_trans with (1 := H1); eauto.
  Qed.

  Fact lhd_split l : lhd l → ∃ x a b c, l = a++x::b++x::c.
  Proof.
    intros (x & m & Hm).
    apply Permutation_sym in Hm.
    destruct (in_split x l) as (a & k & ->).
    1: apply Permutation_in with (1 := Hm); auto.
    rewrite <- Permutation_middle in Hm.
    apply Permutation_cons_inv in Hm.
    destruct (in_app_or a k x) as [ Hx | Hx ].
    + apply Permutation_in with (1 := Hm); auto.
    + apply in_split in Hx as (? & ? & ->).
      eexists _, _, _, _; simpl; rewrite app_ass; simpl; eauto.
    + apply in_split in Hx as (? & ? & ->).
      eexists _, _, _, _; eauto.
  Qed.

  Hint Resolve php_short lhd_split : core.

  Theorem php l m : l ⊆ m → ⌊m⌋ < ⌊l⌋ → ∃ x a b c, l = a++x::b++x::c.
  Proof. eauto. Qed.

End php_short.