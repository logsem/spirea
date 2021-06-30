From iris.proofmode Require Import tactics.
From iris_named_props Require Import named_props.

Ltac iPureGoal :=
  rewrite bi.pure_True;
  first (rewrite (left_id (True)%I) || rewrite (right_id (True)%I));
  last first.

Lemma pure_named_True {PROP} name (φ : Prop) : φ → (name ∷ ⌜φ⌝) ⊣⊢@{PROP} True.
Proof. apply bi.pure_True. Qed.

Ltac iPureGoalNamed name :=
  rewrite (pure_named_True name);
  first (rewrite (left_id (True)%I) || rewrite (right_id (True)%I));
  last first.
