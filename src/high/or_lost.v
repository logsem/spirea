From iris.bi Require Import fractional.

From Perennial.Helpers Require Import ipm NamedProps.

From self Require Import extra ipm_tactics.
From self.base Require Import primitive_laws wpr_lifting.
From self.high Require Import dprop dprop_liftings monpred_simpl.

Set Default Proof Using "Type".

Section or_lost_post_crash.
  Context `{nvmBaseFixedG Σ, nvmBaseDeltaG}.

  Definition or_lost_post_crash ℓ (P : nat → iProp Σ) :=
    (∃ (CV : view),
      crashed_at CV ∗
      ((∃ t, ⌜CV !! ℓ = Some (MaxNat t)⌝ ∗ persisted_loc ℓ 0 ∗ P t)
      ∨ ⌜CV !! ℓ = None⌝))%I.

  Global Instance or_lost_post_crash_proper ℓ :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (or_lost_post_crash ℓ).
  Proof. solve_proper. Qed.

  Definition or_lost_post_crash_no_t ℓ (P : iProp Σ) :=
    or_lost_post_crash ℓ (λ _, P).

  Global Instance or_lost_post_crash_no_t_proper ℓ :
    Proper ((⊣⊢) ==> (⊣⊢)) (or_lost_post_crash_no_t ℓ).
  Proof. solve_proper. Qed.

End or_lost_post_crash.

Section or_lost_with_t.
  Context `{nvmBaseFixedG Σ}.

  (* A [dProp] version of [or_lost_post_crash]. *)
  Definition or_lost_with_t ℓ (P : time → dProp Σ) : dProp Σ :=
    ∃ CV,
      crashed_at_d CV ∗
      ((∃ t, ⌜CV !! ℓ = Some (MaxNat t)⌝ ∗ persisted_loc_d ℓ 0 ∗ P t) ∨
        ⌜ CV !! ℓ = None ⌝).

  Global Instance or_lost_with_t_proper ℓ :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) (or_lost_with_t ℓ).
  Proof. solve_proper. Qed.

  (* The predicate [P] holds for [ℓ] or [ℓ] has been lost. *)
  Definition or_lost ℓ (P : dProp Σ) : dProp Σ :=
    or_lost_with_t ℓ (λ _, P).

  Global Instance or_lost_proper ℓ :
    Proper ((⊣⊢) ==> (⊣⊢)) (or_lost ℓ).
  Proof. solve_proper. Qed.

  Lemma or_lost_post_crash_lookup `{nvmBaseDeltaG} (CV : view) ℓ t P :
    CV !! ℓ = Some (MaxNat t) →
    crashed_at CV -∗
    or_lost_post_crash ℓ P -∗
    P t.
  Proof.
    iIntros (look) "crash".
    iIntros "(% & crash' & [l|%])";
      iDestruct (crashed_at_agree with "crash crash'") as %<-;
      last congruence.
    iDestruct "l" as (t' eq) "(per & P)".
    by simplify_eq.
  Qed.

  (* Lemma or_lost_post_crash_no_t_lookup (CV : view) ℓ t P : *)
  (*   CV !! ℓ = Some (MaxNat t) → *)
  (*   crashed_at CV -∗ *)
  (*   or_lost_post_crash_no_t ℓ P -∗ *)
  (*   P. *)
  (* Proof. apply or_lost_post_crash_lookup. Qed. *)

  Lemma or_lost_post_crash_sep `{nvmBaseDeltaG} ℓ P Q :
    or_lost_post_crash ℓ (λ t, P t ∗ Q t) ⊣⊢
    or_lost_post_crash ℓ (λ t, P t) ∗ or_lost_post_crash ℓ (λ t, Q t).
  Proof.
    iSplit.
    - iDestruct 1 as (?) "(#CV & [(%t & %look & #per & P & Q)|%look])".
      * iSplitL "P"; iExists _; iFrame "CV"; iLeft; naive_solver.
      * iSplitL; iExists _; naive_solver.
    - iIntros "[(%CV & cr1 & [(%t1 & %look1 & #per & P)|%look1])
                (%CV' & cr2 & [(%t2 & %look2 & #? & Q)|%look2])]";
        iDestruct (crashed_at_agree with "cr1 cr2") as %eq;
        simplify_eq.
      * iExists _. iFrame. iLeft. iExists _. iFrame "∗#%".
      * iExists _. iFrame. iRight. done.
  Qed.

  Lemma or_lost_post_crash_mono `{nvmBaseDeltaG} ℓ P Q :
    (∀ t CV,
      ("#per" ∷ persisted_loc ℓ 0 ∗
       "#crashed" ∷ crashed_at CV ∗
       "%cvLook" ∷ ⌜ CV !! ℓ = Some (MaxNat t) ⌝) -∗ P t -∗ Q t) -∗
    or_lost_post_crash ℓ P -∗ or_lost_post_crash ℓ Q.
  Proof.
    iIntros "pToQ (%CV & #crashed & disj)".
    iExists CV. iFrame "crashed". iDestruct "disj" as "[(% & % & #per & P) | %lost]".
    - iLeft. iExists _. iFrame "#". iSplitPure; first done.
      iApply ("pToQ" with "[$per $crashed //] P").
    - iRight. iFrame (lost).
  Qed.

  Global Instance or_lost_post_crash_fractional `{nvmBaseDeltaG} ℓ P :
    (∀ t, Fractional (P t)) →
    Fractional (λ q, or_lost_post_crash ℓ (λ t, P t q)).
  Proof.
    intros F q p.
    rewrite -or_lost_post_crash_sep.
    setoid_rewrite fractional.
    done.
  Qed.

  (* Lemma or_lost_to_with_t ℓ P : or_lost ℓ P ⊣⊢ or_lost_with_t ℓ (λ _, P). *)
  (* Proof. rewrite /or_lost. done. Qed. *)

  Lemma or_lost_with_t_at ℓ (P : _ → dProp Σ) TV gnames :
    or_lost_post_crash ℓ (λ t, P t (TV, gnames)) -∗
    (or_lost_with_t ℓ P) (TV, gnames).
  Proof.
    iDestruct 1 as (CV) "[crash disj]".
    iExists _.
    simpl.
    setoid_rewrite monPred_at_embed.
    iFrame "crash disj".
  Qed.

  Lemma or_lost_with_t_sep ℓ (P Q : _ → dProp Σ) :
    or_lost_with_t ℓ P ∗ or_lost_with_t ℓ Q ⊣⊢ or_lost_with_t ℓ (λ t, P t ∗ Q t)%I.
  Proof.
    iSplit.
    - iIntros "[(%CV & crash & MP) (%CV' & crash' & MQ)]".
      iDestruct (crashed_at_d_agree with "crash crash'") as %<-.
      iExists CV. iFrame.
      iDestruct "MP" as "[(% & % & #per & P)|%]"; iDestruct "MQ" as "[(% & % & #? & Q)|%]";
        try (by iRight).
      simplify_eq.
      iLeft. iExists _. iFrame "∗#". done.
    - iIntros "(%CV & #crash & [(% & % & #per & [P Q])|%])".
      * iSplitL "P".
        + iExists CV. iFrame "#". iLeft. iExists _. iFrame. done.
        + iExists CV. iFrame "#". iLeft. iExists _. iFrame. done.
      * iSplitL; iExists CV; iFrame "#%".
  Qed.

  Lemma or_lost_sep ℓ (P Q : dProp Σ) :
    or_lost ℓ P ∗ or_lost ℓ Q ⊣⊢ or_lost ℓ (P ∗ Q)%I.
  Proof. rewrite /or_lost. apply or_lost_with_t_sep. Qed.

  Lemma or_lost_with_t_mono_strong ℓ (P Q : _ → dProp Σ) :
    (∀ t CV,
       ("%look" ∷ ⌜ CV !! ℓ = Some (MaxNat t) ⌝ ∗
        "#per" ∷ persisted_loc_d ℓ 0 ∗
        "#crashed" ∷ crashed_at_d CV) -∗
      P t -∗ Q t) -∗
    or_lost_with_t ℓ P -∗ or_lost_with_t ℓ Q.
  Proof.
    iIntros "pToQ (%CV & #crashed & disj)".
    iExists CV. iFrame "crashed". iDestruct "disj" as "[(% & % & #per & P) | %lost]".
    - iLeft. iExists _. iFrame "#%". (* iSplitPure; first done. *)
      iApply ("pToQ" with "[] P"). iFrame "#%".
    - iRight. iFrame (lost).
  Qed.

  Lemma or_lost_with_t_mono ℓ (P Q : _ → dProp Σ) :
    (∀ t, P t -∗ Q t) -∗ or_lost_with_t ℓ P -∗ or_lost_with_t ℓ Q.
  Proof.
    iIntros "pToQ".
    iApply (or_lost_with_t_mono_strong).
    iIntros (??) "_". iApply "pToQ".
  Qed.

  Lemma or_lost_mono ℓ (P Q : dProp Σ) :
    (P -∗ Q) -∗ or_lost ℓ P -∗ or_lost ℓ Q.
  Proof. iIntros "I". iApply or_lost_with_t_mono. iIntros (_). done. Qed.

  Lemma or_lost_embed ℓ P TV gnames :
    or_lost_post_crash_no_t ℓ P -∗ or_lost ℓ ⎡ P ⎤ (TV, gnames).
  Proof.
    iDestruct 1 as (CV) "[crash disj]". iExists _.
    simpl. setoid_rewrite monPred_at_embed.
    iFrame "crash". done.
  Qed.

  Lemma or_lost_get CV ℓ P :
    is_Some (CV !! ℓ) → crashed_at_d CV -∗ or_lost ℓ P -∗ P.
  Proof.
    iIntros ([[t] look]) "crash (%CV' & crash' & [(% & ? & #per & $)|%look'])".
    iDestruct (crashed_at_d_agree with "crash crash'") as %<-.
    congruence.
  Qed.

  Lemma or_lost_with_t_get CV ℓ t P :
    CV !! ℓ = Some (MaxNat t) → crashed_at_d CV -∗ or_lost_with_t ℓ P -∗ P t.
  Proof.
    rewrite /or_lost_with_t.
    iIntros (look) "crash (%CV' & crash' & [(%t' & %look' & #per & P)|%look'])";
    iDestruct (crashed_at_d_agree with "crash crash'") as %<-.
    - simplify_eq. iFrame "P".
    - congruence.
  Qed.

End or_lost_with_t.

Opaque or_lost_with_t.
Opaque or_lost_post_crash.
