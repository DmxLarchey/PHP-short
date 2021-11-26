(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
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

Section php_short.

  Variable (X : Type).

  Implicit Types (x : X) (l : list X).

  Hint Resolve incl_nil_l incl_cons
               in_eq in_cons incl_tl
               incl_refl incl_tran : core.

  Reserved Notation "x ↑ n" (at level 1, left associativity, format "x ↑ n").

  Fixpoint repeat x n :=
    match n with
      | 0   => []
      | S n => x::x↑n
    end
  where "x ↑ n" := (repeat x n).

  (* If l ⊆ x::m then, up to permutation, l splits
     in two parts, one consisting in a repetition of x,
     and the other contained in m. Notice that w/o
     a decider equality, we cannot ensure that l'
     does not contain x *)

  Lemma incl_cons_perm l x m : l ⊆ x::m → ∃ n l', l ~ₚ x↑n++l' ∧ l' ⊆ m.
  Proof.
    induction l as [ | y l IHl ].
    + exists 0, []; auto.
    + intros H. 
      apply incl_cons_inv in H as (Hy & H).
      destruct (IHl H) as (n & l' & H1 & H2).
      destruct Hy as [ <- | Hy ].
      * exists (S n), l'; split; simpl; auto.
      * exists n, (y::l'); split; auto.
        rewrite <- Permutation_middle; auto.
  Qed.

  (* In the recursive case l ⊆ x::m, 
     we get either 
        - l ~ₚ l'    and l' ⊆ m (apply IH to l')
        - l ~ₚ x::l' and l' ⊆ m (apply IH to l')
        - l ~ₚ x::x::... and finished
   *)
 
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

  (* The below proof is trivial but tedious due
     to several possibilities in the respective positions 
     of the duplicated x *)

  Fact lhd_split l : lhd l → ∃ x a b c, l = a++x::b++x::c.
  Proof.
    intros (x & m & Hm).
    apply Permutation_sym in Hm.
    destruct (in_split x l) as (a & k & ->).
    1: apply Permutation_in with (1 := Hm); auto.
    rewrite <- Permutation_middle in Hm.
    apply Permutation_cons_inv in Hm.
    destruct (in_app_or a k x) as [ Hx | Hx ].
    1: apply Permutation_in with (1 := Hm); auto.
    + apply in_split in Hx as (? & ? & ->).
      eexists _, _, _, _; simpl; rewrite app_ass; simpl; eauto.
    + apply in_split in Hx as (? & ? & ->).
      eexists _, _, _, _; eauto.
  Qed.

  Hint Resolve php_short lhd_split : core.

  Theorem php l m : l ⊆ m → ⌊m⌋ < ⌊l⌋ → ∃ x a b c, l = a++x::b++x::c.
  Proof. eauto. Qed.

End php_short.

Check php.