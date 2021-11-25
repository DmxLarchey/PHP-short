(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREER SOFTWARE LICENSE AGREEMENT         *)
(**************************************************************)

Require Import List Arith Wellfounded.
Import ListNotations.

Set Implicit Arguments.

Section measure_rect.

  Variable (X : Type) (m : X -> nat) (P : X -> Type).

  Hypothesis F : forall x, (forall y, m y < m x -> P y) -> P x.

  Definition measure_rect x : P x.
  Proof.
    cut (Acc (fun x y => m x < m y) x); [ revert x | ].
    + refine (
        fix loop x Dx := @F x (fun y Dy => loop y _)
      ).
      apply (Acc_inv Dx), Dy.
    + apply wf_inverse_image with (f := m), lt_wf.
  Qed.

End measure_rect.

Tactic Notation "induction" "on" hyp(x) "as" ident(IH) "with" "measure" uconstr(f) :=
  pattern x; revert x; apply measure_rect with (m := fun x => f); intros x IH.

Section less_than_wf.

  Variable (X : Type) (R : X -> X -> Prop) (Rwf : well_founded R).

  Notation "⌊ l ⌋" := (length l) (at level 0, format "⌊ l ⌋").

  Reserved Notation "l '<lex' m" (at level 70).  (* for lexicographic product *)
  Reserved Notation "l '<<' m" (at level 70).    (* for less than *)

  Inductive lex : list X -> list X -> Prop :=
    | lex_skip x l m : l <lex m -> x::l <lex x::m
    | lex_cons x y l m : ⌊l⌋ = ⌊m⌋ -> R x y -> x::l <lex y::m
  where "l <lex m" := (lex l m).

  Fact lex_length l m : l <lex m -> ⌊l⌋ = ⌊m⌋.
  Proof. induction 1; simpl; auto. Qed.

  Fact lex_cons_inv l m : 
          l <lex m 
       -> match m with
            | [] => False
            | y::m =>
            match l with
              | [] => False
              | x::l => x = y /\ l <lex m 
                     \/ R x y /\ ⌊l⌋ = ⌊m⌋
            end
          end.
  Proof. inversion 1; auto. Qed.

  (* Proof of Acc lex m by nested induction on:
       - induction the length of m (IHm)
       - if m = [] then finished (no l exists st l <lex [])
       - if m = x::m' then  
         * we know Acc lex m' (by IHm)
         * induction on x using Rfw
         * induction on (Acc lex m')
  *) 

  Theorem lex_wf : well_founded lex.
  Proof.
    intros m; induction on m as IHm with measure ⌊m⌋.
    destruct m as [ | y m ].
    + constructor; intros l Hl; apply lex_cons_inv in Hl; easy.
    + revert m IHm.
      induction y as [ y IHy' ] using (well_founded_induction Rwf).
      intros m IHm.
      assert (Acc lex m) as Hm.
      1: apply IHm; simpl; auto.
      assert (forall x l, R x y -> ⌊l⌋ = ⌊m⌋ -> Acc lex (x::l)) as IHy.
      1: { intros x l Hx Hl; apply IHy'; auto.
           intros; apply IHm.
           simpl in *; rewrite <- Hl; auto. }
      clear IHy' IHm.
      revert Hm IHy.
      induction 1 as [ m Hm IHm ]; intros IHy.
      constructor; intros l Hl; apply lex_cons_inv in Hl.
      destruct l as [ | x l ]; try tauto.
      destruct Hl as [ (-> & Hl) | (Hx & Hl) ].
      * apply IHm; auto.
        apply lex_length in Hl as ->; auto.
      * apply IHy; auto.
  Qed.

  Inductive less_than : list X -> list X -> Prop :=
    | less_than_lt l m : ⌊l⌋ < ⌊m⌋ -> l << m
    | less_than_eq l m : l <lex m -> l << m
  where "l << m" := (less_than l m).

  Hint Constructors less_than : core.

  Fact less_than_inv l m : l << m <-> ⌊l⌋ < ⌊m⌋ \/ l <lex m.
  Proof. 
    split. 
    + inversion 1; auto. 
    + intros []; eauto. 
  Qed.

  Theorem less_than_wf : well_founded less_than.
  Proof.
    intros m.
    induction on m as IHl with measure (length m).
    induction m as [ m IHm ] using (well_founded_induction lex_wf).
    constructor; intros l Hl. 
    apply less_than_inv in Hl as [ Hl | Hl ].
    + apply IHl; auto.
    + apply IHm; auto.
      apply lex_length in Hl as ->; eauto.
  Qed.

  Section less_than_rect.

    Variable (P : list X -> Type)
             (HP : forall m, (forall l, ⌊l⌋ < ⌊m⌋ -> P l)
                          -> (forall l, l <lex m  -> P l)
                          -> P m).

    Corollary less_than_rect m : P m.
    Proof.
      induction m using (well_founded_induction_type less_than_wf).
      apply HP; eauto.
    Qed.
  
  End less_than_rect.

End less_than_wf.