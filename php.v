(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREER SOFTWARE LICENSE AGREEMENT         *)
(**************************************************************)

Require Import Arith Lia List Permutation Utf8.

Import ListNotations.

Set Implicit Arguments.

Local Infix "~ₚ" := (@Permutation _) (at level 70, no associativity).

Local Hint Constructors Permutation : core.
Local Hint Resolve Permutation_sym Permutation_middle Permutation_app : core.

Local Notation "⌊ l ⌋" := (length l) (at level 0, format "⌊ l ⌋").
Local Infix "∈" := In (at level 70, no associativity).
Local Infix "⊆" := incl (at level 70, no associativity).

Notation "'lhd' l" := (∃ x m, l ~ₚ x::x::m) (at level 1).

Section app_perm_inv.

  Variable (X : Type).

  Implicit Type (l : list X).

  Fact app_inv l1 l2 m1 m2 : 
         l1++l2 = m1++m2 
      -> { k : _ & (l1++k = m1 /\ l2 = k++m2) + (l1 = m1++k /\ k++l2 = m2) }%type.
  Proof.
    revert l1 m1; induction l1 as [ | x l1 IH ]; intros m1.
    + exists m1; left; auto.
    + destruct m1 as [ | y m1 ].
      * exists (x::l1); right; auto.
      * simpl; intros H; injection H; clear H; intros H ->.
        apply IH in H as (k & [ (<- & ->) | (-> & <-) ]); exists k; auto.
  Qed.

  Fact app_inj l1 l2 m1 m2 :
         l1++l2 = m1++m2 
      -> ⌊l1⌋ = ⌊m1⌋
      -> l1 = m1 /\ l2 = m2.
  Proof.
    intros H.
    apply app_inv in H as ([|k] & [ (H1 & H2) | (H1 & H2) ]).
    1-2: rewrite <- app_nil_end in *; simpl in *; auto.
    all: intros; apply f_equal with (f := @length _) in H1;
         rewrite app_length in H1; simpl in H1; lia.
  Qed.

  Fact cons_inj x l y m : x::l = y::m -> x = y /\ l = m.
  Proof. inversion 1; auto. Qed.

  Fact perm_cons_inv x l m :
           l ~ₚ x::m
        -> exists a b, l = a++x::b.
  Proof.
    intros H; apply in_split.
    apply Permutation_in with (1 := Permutation_sym H).
    simpl; auto.
  Qed.

  Fact perm_cons2_inv x y l m :
           l ~ₚ x::y::m
        -> ∃ a b c, l = a++x::b++y::c ∨ l = a++y::b++x::c.
  Proof.
    intros H.
    destruct perm_cons_inv with (1 := H)
      as (u & v & ->).
    apply perm_trans with (1 := Permutation_middle _ _ _),
          Permutation_cons_inv in H.
    apply perm_cons_inv in H as (a & b & H).
    apply app_inv in H as (k & [ (<- & ->) | (-> & ?) ]).
    + exists u, k, b; auto.
    + destruct k as [ | ? k ]; simpl in H.
      * subst v; rewrite <- app_nil_end.
        exists a, [], b; simpl; auto.
      * inversion H; subst; simpl.
        exists a, k, v; right; rewrite app_ass; auto.
  Qed.

  Fact lhd_split l : lhd l → ∃ x a b c, l = a++x::b++x::c.
  Proof.
    intros (x & m & Hm).
    apply perm_cons2_inv in Hm
      as (? & ? & ? & []); eauto.
  Qed.

End app_perm_inv.

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

  Fact lhd_map_split Y (f : X -> Y) l : lhd (map f l) → ∃ a x b y c, l = a++x::b++y::c /\ f x = f y.
  Proof.
    intros H.
    apply lhd_split in H as (u & a & b & c & H).
    apply map_eq_app in H as (a' & d & -> & Ha & H).
    apply map_eq_cons in H as (x & e & -> & Hx & H).
    apply map_eq_app in H as (b' & d & -> & Hb & H).
    apply map_eq_cons in H as (y & c' & -> & Hy & Hc).
    exists a', x, b', y, c'; subst; auto.
  Qed.

  Hint Resolve php_short lhd_split : core.

  Theorem php l m : l ⊆ m → ⌊m⌋ < ⌊l⌋ → ∃ x a b c, l = a++x::b++x::c.
  Proof. eauto. Qed.

End php_short.

Section iter.

  Variables (X : Type) (f : X -> X).

  Fixpoint iter n x :=
    match n with
      | 0 => x
      | S n => iter n (f x)
    end.

  Fact iter_plus n m x : iter (n+m) x = iter m (iter n x).
  Proof. revert x; induction n; simpl; f_equal; auto. Qed.

  Fact iter_S n x : iter (S n) x = f (iter n x).
  Proof.
    replace (S n) with (n+1) by lia.
    rewrite iter_plus; auto.
  Qed.

End iter.

Fixpoint list_an a n :=
  match n with
    | 0 => []
    | S n => a::(list_an (S a) n)
  end.

Fact list_an_plus a n m : list_an a (n+m) = list_an a n ++ list_an (n+a) m.
Proof.
  revert a; induction n as [ | n IHn ]; intros a; simpl; f_equal; try lia.
  rewrite IHn; do 2 f_equal; lia.
Qed.

Fact list_an_length a n : ⌊list_an a n⌋ = n.
Proof. revert a; induction n; simpl; auto. Qed.

Fact list_an_app_inv a n l m : 
         list_an a n = l++m 
      -> n = ⌊l⌋+⌊m⌋ 
      /\ l = list_an a ⌊l⌋ 
      /\ m = list_an (⌊l⌋+a) ⌊m⌋.
Proof.
  intros H.
  generalize H; intros E.
  apply f_equal with (f := @length _) in E.
  rewrite list_an_length, app_length in E; subst; split; auto.
  rewrite list_an_plus in H.
  apply app_inj in H as (-> & ->); auto.
  rewrite list_an_length; auto.
Qed.

Definition injective X Y (f : X -> Y) := forall x₁ x₂, f x₁ = f x₂ -> x₁ = x₂.

Definition inverse X Y (f : X -> Y) g := (forall x, g (f x) = x) /\ forall y, f (g y) = y.

Section finite_inj_inverse.

  Variable (X : Type) (f : X -> X) (Hf : injective f) 
           (l : list X) (Hl : forall x, x ∈ l).

  Fact iter_inj n x y : iter f n x = iter f n y -> x = y.
  Proof. revert x y; induction n; simpl; auto. Qed.

  Local Fact cyclic x : exists n, 0 < n <= ⌊l⌋ /\ iter f n x = x.
  Proof.
    assert (lhd (map (fun n => iter f n x) (list_an 0 (S ⌊l⌋)))) as H.
    1:{ apply php_short with (m := l).
        + intros ? _; auto.
        + rewrite map_length, list_an_length; auto. }
    apply lhd_map_split in H as (a & u & b & v & c & H1 & H2).
    apply list_an_app_inv in H1 as (E & H3 & H4).
    rewrite plus_comm in H4; simpl in H4.
    apply cons_inj in H4 as (-> & H4).
    symmetry in H4.
    apply list_an_app_inv in H4 as (F & H4 & H5).
    rewrite plus_comm in H5; simpl in H5.
    apply cons_inj in H5 as (-> & H5).
    replace (S (⌊a⌋ + ⌊b⌋)) with ((S ⌊b⌋)+⌊a⌋) in H2 by lia.
    rewrite iter_plus in H2.
    apply iter_inj in H2.
    exists (S ⌊b⌋); split; auto.
    simpl in E; rewrite app_length in E; simpl in E; lia.
  Qed.
 
  Fact fact_divides n p : 0 < p <= n -> exists k, p*k = fact n.
  Proof.
    revert p; induction n as [ | n IHn ]; intros p Hp.
    + lia.
    + destruct (eq_nat_dec p (S n)) as [ -> | H ].
      * exists (fact n); auto.
      * destruct (IHn p) as (k & Hk).
        - lia.
        - exists (k*S n).
          unfold fact; fold fact; rewrite <- Hk.
          ring.
  Qed.

  Fact iter_divides p k x : iter f p x = x -> iter f (p*k) x = x.
  Proof.
    intros H.
    rewrite mult_comm.
    induction k as [ | k IHk ]; simpl; auto.
    rewrite iter_plus, H; auto.
  Qed.

  Hint Resolve iter_divides : core.

  Local Theorem finite_inj_id x : iter f (fact ⌊l⌋) x = x.
  Proof.
    destruct (cyclic x) as (n & H1 & H2).
    apply fact_divides in H1 as (k & <-); auto.
  Qed.

  Theorem finite_inj_iter_inverse : { n | inverse f (iter f n) }.
  Proof.
    generalize (fact_le 0 ⌊l⌋ (le_0_n _)); simpl; intros H.
    exists (fact ⌊l⌋ - 1); split; intros x.
    + rewrite <- (finite_inj_id x) at 2.
      replace (fact ⌊l⌋) with (S (fact ⌊l⌋ - 1)) at 2 by lia; auto.
    + rewrite <- iter_S.
      replace (S (fact ⌊l⌋ - 1)) with (fact ⌊l⌋) by lia.
      apply finite_inj_id.
  Qed.

  Theorem finite_inj_inverse : { g | inverse f g }.
  Proof.
    destruct finite_inj_iter_inverse as (n & Hn); eauto.
  Qed.

End finite_inj_inverse.

Section Cantor_Bernstein_finite.

  Variable (X Y : Type) (f : X -> Y) (g : Y -> X) 
           (Hf : injective f) (Hg : injective g)
           (HX : exists l : list X, forall x, x ∈ l).

  Theorem Cantor_Bernstein_finite : 
             (exists fi, inverse f fi) 
          /\ (exists gi, inverse g gi).
  Proof.
    destruct HX as (l & Hl).
    destruct finite_inj_inverse with (f := fun x => g (f x)) 
             (l := l) as (h & H1 & H2); auto; [ | split ].
    + intros ? ? ?; auto.
    + exists (fun x => h (g x)); split; auto.
    + exists (fun y => f (h y)); split; auto.
  Qed.

End Cantor_Bernstein_finite.

Check Cantor_Bernstein_finite.
