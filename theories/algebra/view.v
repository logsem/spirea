From stdpp Require Import countable numbers gmap.
From iris.heap_lang Require Export locations.
From iris.algebra Require Export gmap numbers.

Notation time := nat.

(* A view is a finite map from locations to natural numbers. A view is a monoid
  with the empty map as the unit and point-wise max as the operation. To get
  this monoid structure very easily we use the camera of finite maps and the
  max_nat camera. We will use this definition in, for instance, the memory model
  where the full camera structure is not needed. But, this approach simplifies
  things greatly. *)
Notation view := (gmap loc max_nat).

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

Infix "!!0" := (λ m i, default 0 (max_nat_car <$> (m !! i))) (at level 80).

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

Lemma view_le_lub V V' W :
  V ⊑ W → V' ⊑ W → (V ⊔ V') ⊑ W.
Proof. Admitted.

(* A view is always valid. *)
Lemma view_valid V : ✓ V.
Proof. intros k. case (V !! k); done. Qed.

Lemma view_insert_le V ℓ t :
  (V !!0 ℓ) ≤ t → V ⊑ <[ℓ := MaxNat t]>V.
Proof. Admitted.

Lemma view_insert_op V ℓ t :
  (V !!0 ℓ) ≤ t → (V ⊔ {[ℓ := MaxNat t]}) = (<[ℓ := MaxNat t]> V).
Proof.
  intros look.
Admitted.