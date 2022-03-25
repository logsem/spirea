From iris.proofmode Require Import tactics.
From iris_named_props Require Import named_props.

Lemma pure_sep_l `{BiAffine PROP} (φ : Prop) (P : PROP) : φ → P ⊢ ⌜φ⌝ ∗ P.
Proof. intros ?. rewrite bi.pure_True; last done. by rewrite left_id. Qed.

Lemma pure_sep_r `{BiAffine PROP} (φ : Prop) (P : PROP) : φ → P ⊢ P ∗ ⌜φ⌝.
Proof. intros ?. rewrite bi.pure_True; last done. by rewrite right_id. Qed.

Ltac iSplitPure := iSplit; first iPureIntro.

Ltac iPureGoal :=
  (setoid_rewrite <- pure_sep_l || setoid_rewrite <- pure_sep_r); last first.

Lemma pure_named_True {PROP} name (φ : Prop) : φ → (name ∷ ⌜φ⌝) ⊣⊢@{PROP} True.
Proof. apply bi.pure_True. Qed.

Ltac iPureGoalNamed name :=
  rewrite (pure_named_True name);
  first (rewrite (left_id (True)%I) || rewrite (right_id (True)%I));
  last first.

(** [iFrameF] takes an assumption (pure or spatial) an tries to frame only the
first conjunct in the goal with the assumption. The key reason to use this
tactic is that it can be much faster than the normal [iFrame] if the goal is
large. *)
Tactic Notation "iFrameF" "(" constr(t1) ")" :=
  iSplit; first iFramePure t1.

Tactic Notation "iFrameF" constr(Hs) :=
  iSplitL Hs; first iFrame Hs.
