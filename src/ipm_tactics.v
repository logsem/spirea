From iris.proofmode Require Import tactics.
From iris_named_props Require Import named_props.

Lemma pure_sep_l `{BiAffine PROP} (φ : Prop) (P : PROP) : φ → P ⊢ ⌜φ⌝ ∗ P.
Proof. intros ?. rewrite bi.pure_True; last done. by rewrite left_id. Qed.

Lemma pure_sep_r `{BiAffine PROP} (φ : Prop) (P : PROP) : φ → P ⊢ P ∗ ⌜φ⌝.
Proof. intros ?. rewrite bi.pure_True; last done. by rewrite right_id. Qed.

Ltac iPureGoal :=
  (setoid_rewrite <- pure_sep_l || setoid_rewrite <- pure_sep_r); last first.

Lemma pure_named_True {PROP} name (φ : Prop) : φ → (name ∷ ⌜φ⌝) ⊣⊢@{PROP} True.
Proof. apply bi.pure_True. Qed.

Ltac iPureGoalNamed name :=
  rewrite (pure_named_True name);
  first (rewrite (left_id (True)%I) || rewrite (right_id (True)%I));
  last first.
