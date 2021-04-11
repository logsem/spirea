(* In this we define [view] type which is both a unital resource algebra and a
lattice. We use the lattice notation from stdpp. *)

From stdpp Require Import tactics countable numbers gmap.
From iris.heap_lang Require Export locations.
From iris.algebra Require Export gmap numbers.

Notation time := nat (only parsing).

(* A view is a finite map from locations to natural numbers. A view is a monoid
  with the empty map as the unit and point-wise max as the operation. To get
  this monoid structure very easily we use the camera of finite maps and the
  max_nat camera. We will use this definition in, for instance, the memory model
  where the full camera structure is not needed. But, this approach simplifies
  things greatly. *)
Notation view := (gmap loc max_nat).

Canonical Structure viewO := leibnizO view.

Notation viewUR := (gmapUR loc max_natUR).

Implicit Types (V W : view) (ℓ : loc).

Instance join_view : Join view :=
  λ a b, a ⋅ b.

Instance subseteq_view : SqSubsetEq view := λ v w, v ≼ w.

Lemma view_join V W : (V ⊔ W) = (V ⋅ W).
Proof. done. Qed.

Lemma subseteq_view_incl V W : (V ⊑ W) = (V ≼ W).
Proof. done. Qed.

Global Instance subseteq_view_assoc : Assoc (=) (join_view).
Proof. apply _. Qed.

Global Instance join_mono : Proper ((⊑@{view}) ==> (⊑) ==> (⊑)) (⊔).
Proof. solve_proper. Qed.

Infix "!!0" := (λ m i, default 0 (max_nat_car <$> (m !! i))) (at level 80).

Lemma view_empty_least V : ∅ ⊑ V. 
Proof.
  rewrite subseteq_view_incl.
  replace ∅ with ε by done.
  apply: ucmra_unit_least.
Qed.

Lemma view_lt_lt V W ℓ : V ⊑ W → (V !!0 ℓ) ≤ (W !!0 ℓ).
Proof.
  rewrite subseteq_view_incl lookup_included.
  intros le.
  pose proof (le ℓ) as le.
  move: le.
  destruct (V !! ℓ) as [[t]|] eqn:eq, (W !! ℓ) as [[t'']|] eqn:eq'; simpl; try lia.
  - rewrite eq. rewrite eq'.
    rewrite Some_included_total.
    rewrite max_nat_included.
    done.
  - rewrite eq. rewrite eq'.
    rewrite option_included.
    intros [?|[? [? (_ & ? & _)]]]; done.
Qed.

Global Instance view_core_id (v : view) : CoreId v.
Proof. apply _. Qed.

Lemma option_max_nat_included (on on' om : option max_nat) : on ≼ om → on' ≼ om → on ⋅ on' ≼ om.
Proof.
  destruct on, on', om; auto.
  - rewrite !Some_included_total.
    destruct m, m0, m1.
    rewrite max_nat_op !max_nat_included. simpl. lia.
  - rewrite option_included.
    intros [[=]|(? & ? & _ & [=] & _)].
Qed.

Lemma view_le_lub V V' W :
  V ⊑ W → V' ⊑ W → (V ⊔ V') ⊑ W.
Proof.
  rewrite !subseteq_view_incl view_join.
  rewrite !lookup_included.
  intros Vle V'le.
  intros ℓ.
  rewrite lookup_op.
  apply option_max_nat_included; done.
Qed.

(* A view is always valid. *)
Lemma view_valid V : ✓ V.
Proof. intros k. case (V !! k); done. Qed.

Lemma view_insert_le V ℓ t :
  (V !!0 ℓ) ≤ t → V ⊑ <[ℓ := MaxNat t]>V.
Proof.
  intros le.
  rewrite subseteq_view_incl.
  rewrite lookup_included.
  intros ℓ'.
  destruct (decide (ℓ = ℓ')).
  - subst. rewrite lookup_insert.
    destruct (V !! ℓ') as [[m]|] eqn:eq; simpl.
    * rewrite eq. simpl in *. apply Some_included_2. apply max_nat_included. done.
    * rewrite eq.
      replace (None) with (ε); last done.
      apply ucmra_unit_least.
  - rewrite lookup_insert_ne; done.
Qed.

Lemma view_insert_op V ℓ t :
  (V !!0 ℓ) ≤ t → (V ⊔ {[ℓ := MaxNat t]}) = (<[ℓ := MaxNat t]> V).
Proof.
  intros le. rewrite view_join.
  apply map_eq. intros ℓ'.
  rewrite lookup_op.
  destruct (decide (ℓ = ℓ')).
  - subst. rewrite lookup_singleton.
    rewrite lookup_insert.
    destruct (V !! ℓ') as [[m]|] eqn:eq; rewrite eq; last done.
    rewrite -Some_op. rewrite max_nat_op.
    f_equiv. f_equiv. simpl in le. lia.
  - rewrite lookup_singleton_ne; last done.
    rewrite right_id.
    rewrite lookup_insert_ne; done.
Qed.

(* Instances of the lattice type classes for products. *)

Global Instance join_prod `{!Join A, !Join B} : Join (A * B) :=
  λ '(a, b) '(a', b'), (a ⊔ a', b ⊔ b').

Global Instance subseteq_prod `{!SqSubsetEq A, !SqSubsetEq B} : SqSubsetEq (A * B) :=
  λ '(a, b) '(a', b'), a ⊑ a' ∧ b ⊑ b'.

Lemma subseteq_prod' `{SqSubsetEq A, SqSubsetEq B} (a a' : A) (b b' : B) :
  (a, b) ⊑ (a', b') = (a ⊑ a' ∧ b ⊑ b').
Proof. done. Qed.

(* Projections are monotone. *)
Global Instance fst_mono `{!SqSubsetEq A, !SqSubsetEq B} : Proper ((⊑) ==> (⊑)) (@fst A B).
Proof. intros [??] [??] [??]. done. Qed.

(* Projections are monotone. *)
Global Instance snd_mono `{!SqSubsetEq A, !SqSubsetEq B} : Proper ((⊑) ==> (⊑)) (@snd A B).
Proof. intros [??] [??] [??]. done. Qed.

Instance pair_preorder `{!SqSubsetEq A, !SqSubsetEq B, !PreOrder (⊑@{A}),
                         !PreOrder (⊑@{B})} : PreOrder (⊑@{A * B}).
Proof.
  constructor.
  - intros [??]. rewrite subseteq_prod'. done.
  - intros [??] [??] [??]. rewrite !subseteq_prod'. intros [??] [??].
    split; etrans; done.
Qed.

(* Global Instance pair_join_mono `{!Join A, !Join B, !SqSubsetEq A, !SqSubsetEq B} : Proper ((⊑@{A * B}) ==> (⊑) ==> (⊑)) (⊔). *)
(* Proof. *)
(*   Check pointwise_relation. *)
(*   intros [??] [??] ? ? ? ?. *)
(* Admitted. *)
  (* solve_proper.
Qed. *)

(* Global Instance foo_mono : *)
(*   Proper (pointwise_relation _ (=) ==> (⊆) ==> (⊆)) (⊑). *)
(* Proof. intros f g ? X Y. set_unfold; naive_solver. Qed. *)
