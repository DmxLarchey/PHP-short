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

Local Reserved Notation "x ↑ n" (at level 1, left associativity, format "x ↑ n").

Section app_perm_inv.

  Variable (X : Type).

  Implicit Type (l : list X).

  Fact app_inv l1 l2 m1 m2 : 
         l1++l2 = m1++m2 
       → { k : _ & (l1++k = m1 ∧ l2 = k++m2) + (l1 = m1++k ∧ k++l2 = m2) }%type.
  Proof.
    induction l1 as [ | x l1 IH ] in m1 |- *.
    + exists m1; left; auto.
    + destruct m1 as [ | y m1 ].
      * exists (x::l1); right; auto.
      * simpl; intros H; injection H; clear H. 
        intros (k & [ (<- & ->) | (-> & <-) ])%IH ->; exists k; auto.
  Qed.

  Fact app_inj l1 l2 m1 m2 :
         l1++l2 = m1++m2 → ⌊l1⌋ = ⌊m1⌋ → l1 = m1 ∧ l2 = m2.
  Proof.
    intros H.
    apply app_inv in H as ([|k] & [ (H1 & H2) | (H1 & H2) ]).
    1-2: rewrite <- app_nil_end in *; simpl in *; auto.
    all: intros; apply f_equal with (f := @length _) in H1;
         rewrite app_length in H1; simpl in H1; lia.
  Qed.

  Fact cons_inj x l y m : x::l = y::m → x = y ∧ l = m.
  Proof. inversion 1; auto. Qed.

  Fact perm_cons_inv x l m : l ~ₚ x::m → ∃ a b, l = a++x::b.
  Proof. intros H%Permutation_sym; apply in_split, Permutation_in with (1 := H), in_eq. Qed.

  Fact perm_cons2_inv x y l m : l ~ₚ x::y::m → ∃ a b c, l = a++x::b++y::c ∨ l = a++y::b++x::c.
  Proof.
    intros H.
    destruct perm_cons_inv with (1 := H)
      as (u & v & ->).
    apply perm_trans with (1 := Permutation_middle _ _ _),
          Permutation_cons_inv, perm_cons_inv in H as (a & b & H).
    apply app_inv in H as (k & [ (<- & ->) | (-> & ?) ]).
    + exists u, k, b; auto.
    + destruct k as [ | ? k ]; simpl in H.
      * subst v; rewrite <- app_nil_end.
        exists a, [], b; simpl; auto.
      * inversion H; subst; simpl.
        exists a, k, v; right; rewrite app_ass; auto.
  Qed.

  Fact lhd_split l : lhd l → ∃ x a b c, l = a++x::b++x::c.
  Proof. intros (? & ? & (? & ? & ? & [])%perm_cons2_inv); eauto. Qed.

End app_perm_inv.

Fact lhd_map_inv X Y (f : X → Y) l : 
        lhd (map f l) → ∃ a x b y c, l = a++x::b++y::c ∧ f x = f y.
Proof.
  intros (u & a & b & c & H)%lhd_split; revert H.
  intros (a' & d & -> & Ha & (x & e & -> & Hx & H)%map_eq_cons)%map_eq_app; revert H.
  intros (b' & d & -> & Hb & (y & c' & -> & Hy & H)%map_eq_cons)%map_eq_app; revert H.
  exists a', x, b', y, c'; subst; auto.
Qed.

Section php_short.

  Variable (X : Type).

  Implicit Types (x : X) (l : list X).

  Hint Resolve incl_nil_l incl_cons
               in_eq in_cons incl_tl
               incl_refl incl_tran : core.

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
    induction m as [ | x m IHm ] in l |- *; intros H1 H2.
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

  Hint Resolve php_short lhd_split : core.

  Theorem php l m : l ⊆ m → ⌊m⌋ < ⌊l⌋ → ∃ x a b c, l = a++x::b++x::c.
  Proof. eauto. Qed.

End php_short.

Section iter.

  Variables (X : Type) (f : X → X).

  Fixpoint iter n x :=
    match n with
      | 0   => x
      | S n => iter n (f x)
    end.

  Fact iter_plus n m x : iter (n+m) x = iter m (iter n x).
  Proof. revert x; induction n; simpl; f_equal; auto. Qed.

  Fact iter_S n x : iter (S n) x = f (iter n x).
  Proof. replace (S n) with (n+1) by lia; now rewrite iter_plus. Qed.

  Fact iter_divides p k x : iter p x = x → iter (p*k) x = x.
  Proof.
    intros H.
    rewrite mult_comm.
    induction k; simpl; auto.
    now rewrite iter_plus, H.
  Qed.

End iter.

Fixpoint list_an a n :=
  match n with
    | 0   => []
    | S n => a::(list_an (S a) n)
  end.

Fact list_an_plus a n m : list_an a (n+m) = list_an a n ++ list_an (n+a) m.
Proof.
  induction n as [ | n IHn ] in a |- *; simpl; f_equal; try lia.
  rewrite IHn; do 2 f_equal; lia.
Qed.

Fact list_an_length a n : ⌊list_an a n⌋ = n.
Proof. induction n in a |- *; simpl; auto. Qed.

Fact list_an_app_inv a n l m : 
         list_an a n = l++m 
       → n = ⌊l⌋+⌊m⌋ 
       ∧ list_an a ⌊l⌋ = l 
       ∧ list_an (⌊l⌋+a) ⌊m⌋ = m.
Proof.
  intros H.
  generalize H; intros E.
  apply f_equal with (f := @length _) in E.
  rewrite list_an_length, app_length in E; subst; split; auto.
  rewrite list_an_plus in H.
  apply app_inj in H as (-> & ->); auto.
  rewrite list_an_length; auto.
Qed.

Fact list_an_cons_inv a n x l :
          list_an a n = x::l
        → match n with 
            | 0   => False 
            | S m => a = x ∧ list_an (S a) m = l
          end.
Proof.
  destruct n as [ | m ]; simpl.
  + easy.
  + intros (<- & ?)%cons_inj; eauto.
Qed.

Fact list_an_complex_inv a n u x v y w :
          list_an a n = u++x::v++y::w
        → u = list_an a ⌊u⌋
        ∧ x = a+⌊u⌋
        ∧ v = list_an (S x) ⌊v⌋
        ∧ y = 1+a+⌊u⌋+⌊v⌋
        ∧ w = list_an (S y) ⌊w⌋
        ∧ n = 2+⌊u⌋+⌊v⌋+⌊w⌋.
Proof.
  intros (G1 & G2 & H1)%list_an_app_inv; simpl in H1, G1; revert H1.
  intros (G3 & (G4 & G5 & H1)%list_an_app_inv)%cons_inj; simpl in H1; revert H1.
  intros (G6 & G7)%cons_inj.
  simpl in *; repeat split; auto; try lia.
  + rewrite <- G5 at 1; subst; auto.
  + rewrite <- G7 at 1; subst; auto.
Qed.

Fact fact_ge n : n ≤ fact n.
Proof.
  induction n as [ | n ].
  + simpl; auto.
  + replace (S n) with ((1+n)*1) at 1 by lia.
    apply mult_le_compat; auto.
    apply lt_O_fact.
Qed.

Fact fact_divides n p : 0 < p <= n → ∃k, p*k = fact n.
Proof.
  induction n as [ | n IHn ] in p |- *; intros Hp.
  + lia.
  + destruct (eq_nat_dec p (S n)) as [ -> | H ].
    * exists (fact n); auto.
    * destruct (IHn p) as (k & Hk).
      - lia.
      - exists (k*S n).
        unfold fact; fold fact; rewrite <- Hk.
        ring.
Qed.

Section bound_cycle.

  Variables (X : Type) (l : list X) (Hl : ∀x, x ∈ l) (f : X → X).

  Infix "↑" := iter.

  Lemma iter_fix_after x : ∃c, 0 < c <= ⌊l⌋ ∧ ∀n, ⌊l⌋ ≤ n → f↑(c+n) x = f↑n x.
  Proof.
    destruct lhd_map_inv with (f := λ n, f↑n x) (l := list_an 0 (S ⌊l⌋))
      as (a & i & b & j & c & (G1 & G2 & G3 & G4 & G5 & G6)%list_an_complex_inv & H2).
    + apply php_short with (m := l).
      * intro; auto.
      * rewrite map_length, list_an_length; auto.
    + exists (j-i); split.
      1: simpl in *; lia.
      intros n Hn.
      replace n with (i+(n-i)) at 2 by (simpl in *; lia).
      replace (j-i+n) with (j+(n-i)) by (simpl in *; lia).
      rewrite !iter_plus; f_equal; auto.
  Qed.

  Theorem bound_cycle : ∀ x n, ⌊l⌋ ≤ n -> f↑(fact ⌊l⌋+n) x = f↑n x.
  Proof.
    intros x n Hn.
    destruct (iter_fix_after x) as (c & H1 & H2).
    specialize (H2 _ Hn).
    destruct (fact_divides H1) as (k & <-).
    rewrite plus_comm, iter_plus.
    apply iter_divides.
    now rewrite plus_comm, iter_plus in H2.
  Qed.

End bound_cycle.

Section Marc_Hermes.

  (** Follow up on https://hermesmarc.github.io/2022/07/22/function-cycling.html 

      Notice that the statement of Puzzle 1 is incorrect because X could be empty
      Notice that the constraint k < c in Puzzle 2 seems a bit artificial *)

  Variable (X : Type) (Xfin : ∃l, ∀x : X, x ∈ l).

  Implicit Type (f : X → X).

  Infix "↑" := iter.

  (** See iter_fix_after above *)
  Fact Puzzle_1 : inhabited X → ∀f, ∃ a c, 0 < c ∧ f↑c a = a.
  Proof.
    intros [ x ] f.
    destruct Xfin as (l & Hl).
    destruct (iter_fix_after l Hl f x) as (c & (H1 & H2) & H3).
    exists (f↑⌊l⌋ x), c; split; auto.
    rewrite <- iter_plus, plus_comm.
    now apply H3.
  Qed.

  (** See bound_cycle above *)
  Fact Puzzle_2 : ∃ k c, k < c ∧ ∀ f x, f↑(c+k) x = f↑k x.
  Proof.
    destruct Xfin as (l & Hl).
    exists ⌊l⌋, (fact ⌊l⌋ + fact ⌊l⌋); split.
    + apply plus_le_compat with (1 := lt_O_fact _) (2 := fact_ge _).
    + intros; rewrite <- plus_assoc, !bound_cycle; auto; lia.
  Qed.

End Marc_Hermes.

Definition injective X Y (f : X → Y) := ∀ x₁ x₂, f x₁ = f x₂ → x₁ = x₂.

Definition inverse X Y (f : X → Y) g := (∀x, g (f x) = x) ∧ ∀y, f (g y) = y.

Section finite_inj_inverse.

  Variable (X : Type) (f : X → X) (Hf : injective f) 
           (l : list X) (Hl : ∀x, x ∈ l).

  Infix "↑" := iter.

  Fact iter_inj n : ∀ x y, f↑n x = f↑n y → x = y.
  Proof. induction n; simpl; auto. Qed.

  Local Theorem finite_inj_id x : f↑(fact ⌊l⌋) x = x.
  Proof.
    apply iter_inj with (n := ⌊l⌋).
    rewrite <- iter_plus.
    apply bound_cycle; auto.
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
  Proof. destruct finite_inj_iter_inverse; eauto. Qed.

End finite_inj_inverse.

Section Cantor_Bernstein_finite.

  Variable (X Y : Type) 
           (f : X → Y) (Hf : injective f)
           (g : Y → X) (Hg : injective g)
           (Xfin : ∃l, ∀x : X, x ∈ l).

  Theorem Cantor_Bernstein_finite : 
             (∃fi, inverse f fi) 
          /\ (∃gi, inverse g gi).
  Proof.
    destruct Xfin as (l & Hl).
    destruct finite_inj_inverse with (f := fun x => g (f x)) 
             (l := l) as (h & H1 & H2); auto; [ | split ].
    + intros ? ? ?; auto.
    + exists (fun x => h (g x)); split; auto.
    + exists (fun y => f (h y)); split; auto.
  Qed.

End Cantor_Bernstein_finite.

Section Kuratowski.

  Variable (X : Type).

  Inductive kuratowski_fin : (X → Prop) → Prop :=
    | kfin_empty P : (∀x, ~ P x) → kuratowski_fin P
    | kfin_cons P y Q : (∀x, P x <-> y = x \/ Q x) → kuratowski_fin Q → kuratowski_fin P.

  Fact kuratowski_fin_listable P : kuratowski_fin P -> ∃l, ∀x, P x <-> x ∈ l.
  Proof.
    induction 1 as [ P HP | P y Q HP HQ (l & Hl) ].
    + exists nil; simpl; firstorder.
    + exists (y::l); intro; rewrite HP, Hl; simpl; firstorder.
  Qed.

  Fact listable_kuratowski_fin P : (∃l, ∀x, P x <-> x ∈ l) → kuratowski_fin P.
  Proof.
    intros (l & Hl); revert P Hl.
    induction l as [ | y l IHl ]; intros P Hl.
    + constructor 1; intro; rewrite Hl; simpl; tauto.
    + constructor 2 with y (fun x => In x l); auto.
      apply IHl; tauto.
  Qed.

End Kuratowski.

Definition kuratowski_finite X := kuratowski_fin (fun _ : X => True).

Fact kuratowski_finite_listable X : kuratowski_finite X <-> ∃l, ∀x : X, x ∈ l.
Proof.
  split.
  + intros H.
    apply kuratowski_fin_listable in H as (l & Hl).
    exists l; intro; apply Hl; auto.
  + intros (l & Hl); apply listable_kuratowski_fin; exists l; split; eauto.
Qed.




  