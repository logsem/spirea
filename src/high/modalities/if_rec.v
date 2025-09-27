(** The meaningful part of the definition of [if_rec] have been ported to base spirea.
 ** This file only contains [dProp] lifting definitions and lemmas. *)

From iris.proofmode Require Import proofmode.
From iris_named_props Require Import named_props.

From iris.bi Require Import bi.
From iris.bi Require Import derived_laws.
From self.base Require Import generational_resources.
From self.high Require Import dprop monpred_simpl.

From self.base.modalities Require Import if_rec.
From self.high.modalities Require Import or_lost.

From self.algebra Require Import view.

Notation base_if_rec := self.base.modalities.if_rec.if_rec.

Set Default Proof Using "Type".

(* The predicate [P] holds for [ℓ] or [ℓ] has been lost. *)
(* I believe the [persisted_loc] component is unnecessary
 * (implied by CV, at least in the context of a valid state interpretation),
 * but in case it's necessary in some unforseen way, I'm keeping it for now. *)

(* Yixuan: I'm moving to use [crashed_at_offset] instead of [crashed_at] as much as possible. *)
Definition if_rec `{!nvmBaseGS Σ Ω} (ℓ : loc) (P : dProp Σ) : dProp Σ :=
  ∀ (OCV : view),
  ⌜ is_Some (OCV !! ℓ) ⌝ -∗ ⎡ crashed_at_offset OCV ⎤ -∗ ⎡ persisted_loc ℓ 0 ⎤ -∗ P.

Section lifting.
  Context `{nvmBaseGS}.

  Lemma if_rec_lift_if_rec ℓ P:
    if_rec ℓ ⎡ P ⎤ ⊣⊢ ⎡ base_if_rec ℓ P ⎤.
  Proof.
    rewrite /if_rec /base_if_rec.
    rewrite embed_forall.
    do 2 f_equiv.
    rewrite ?embed_wand embed_pure.
    done.
  Qed.
End lifting.

Class IntoIfRec `{nvmBaseGS} ℓ (P : dProp Σ) (Q : dProp Σ) :=
  into_if_rec : P ⊢ if_rec ℓ Q.
Global Arguments IntoIfRec {_} {_} {_} _ _%I _%I.
Global Arguments into_if_rec  {_} {_} {_} {_} _%I _%I.
Global Hint Mode IntoIfRec ! ! ! + + -  : typeclass_instances.

Section if_rec.
  Context `{nvmBaseGS}.

  Local Ltac ifRecIntro :=
    iIntros (CV);
    iIntros "%look #crashed_at_offset #persisted".

  Lemma if_rec_intro ℓ P : P ⊢ if_rec ℓ P.
  Proof.
    iIntros "P".
    ifRecIntro.
    done.
  Qed.

  Lemma if_rec_and ℓ P Q : if_rec ℓ (P ∧ Q) ⊣⊢ if_rec ℓ P ∧ if_rec ℓ Q.
  Proof.
    iSplit.
    - iIntros "H".
      iSplit; ifRecIntro.
      * iDestruct ("H" $! CV with "[//] [$] [$]") as "[$ _]".
      * iDestruct ("H" $! CV with "[//] [$] [$]") as "[_ $]".
    - iIntros "H". ifRecIntro.
      iSplit.
      * iDestruct "H" as "[H _]". iApply "H"; done.
      * iDestruct "H" as "[_ H]". iApply "H"; done.
  Qed.

  Lemma if_rec_sep ℓ (P Q : dProp Σ) :
    if_rec ℓ P ∗ if_rec ℓ Q ⊢ if_rec ℓ (P ∗ Q)%I.
  Proof.
    iIntros "[P Q]". ifRecIntro.
    iDestruct ("P" $! CV with "[//] [$] [$]") as "$".
    iDestruct ("Q" $! CV with "[//] [$] [$]") as "$".
  Qed.

  Lemma if_rec_mono ℓ (P Q : dProp Σ) :
    (P ⊢ Q) → if_rec ℓ P ⊢ if_rec ℓ Q.
  Proof.
    rewrite /if_rec.
    intros pToQ.
    iIntros "P". ifRecIntro.
    iApply pToQ.
    iApply "P"; done.
  Qed.

  Lemma if_rec_emp ℓ : (emp : dProp Σ) ⊢ if_rec ℓ emp.
  Proof. iIntros "_". ifRecIntro. done. Qed.

  Lemma if_rec_intuitionistically_2 ℓ P : □ (if_rec ℓ P) ⊢ if_rec ℓ (□ P).
  Proof. iIntros "#P". ifRecIntro. iModIntro. iApply "P"; done. Qed.

  Lemma modality_if_rec_mixin (ℓ: loc) :
    modality_mixin (@if_rec Σ _ _ ℓ)
      (MIEnvTransform (IntoIfRec ℓ)) (MIEnvTransform (IntoIfRec ℓ)).
  Proof.
    split; simpl; split_and?;
      eauto using bi.equiv_entails_1_2, if_rec_and, if_rec_emp,
        if_rec_mono, if_rec_sep.
    intros P Q. rewrite /IntoIfRec=> ->.
    by rewrite if_rec_intuitionistically_2.
  Qed.

  Definition modality_if_rec ℓ :=
    Modality _ (modality_if_rec_mixin ℓ).

  Global Instance from_modal_if_rec P ℓ :
    FromModal True (modality_if_rec ℓ) (if_rec ℓ P) (if_rec ℓ P) P.
  Proof. by rewrite /FromModal. Qed.

  Global Instance if_rec_mono' ℓ : Proper ((⊢) ==> (⊢)) (if_rec (Σ := Σ) ℓ).
  Proof. intros P Q. apply if_rec_mono. Qed.

  Global Instance if_rec_proper ℓ : Proper ((⊣⊢) ==> (⊣⊢)) (if_rec (Σ := Σ) ℓ).
  Proof. rewrite /if_rec. intros P Q pToQ. setoid_rewrite pToQ. done. Qed.

  (* Global Instance if_rec_objective ℓ `{!Objective P} : Objective (if_rec ℓ P). *)
  (* Proof. *)
  (*   iIntros (TV1 ?) "P". *)
  (*   iIntros (CV ?? look ??) "crashed". *)
  (*   iIntros (??) "pers". *)
  (*   iSpecialize ("P" $! CV look). *)
  (*   monPred_simpl. iSpecialize ("P" $! TV1 with "[//] crashed"). *)
  (*   monPred_simpl. iSpecialize ("P" $! TV1 with "[//] pers"). *)
  (*   iApply objective_at. *)
  (*   iApply "P". *)
  (* Qed. *)

  Lemma if_rec_get OCV ℓ P :
    is_Some (OCV !! ℓ) → ⎡ crashed_at_offset OCV ⎤ -∗ ⎡ persisted_loc ℓ 0 ⎤ -∗ if_rec ℓ P -∗ P.
  Proof. iIntros ([[t] look]) "#? #? H". iApply "H"; naive_solver. Qed.

  (* Lemma if_rec_with_t_get CV ℓ t P : *)
  (*   CV !! ℓ = Some (MaxNat t) → ⎡ crashed_at CV ⎤ -∗ if_rec_with_t ℓ P -∗ P t. *)
  (* Proof. *)
  (*   rewrite /if_rec_with_t. *)
  (*   iIntros (look) "crash (%CV' & crash' & [(%t' & %look' & P)|%look'])"; *)
  (*   iDestruct (crashed_at_agree with "crash crash'") as %<-. *)
  (*   - simplify_eq. iFrame "P". *)
  (*   - congruence. *)
  (* Qed. *)

  Lemma if_rec_is_rec ℓ :
    ⊢ if_rec ℓ (∃ OCV,
      ⌜ is_Some (OCV !! ℓ) ⌝ ∗ ⎡ crashed_at_offset OCV ⎤).
  Proof. ifRecIntro. iExists CV. iFrame "#%". Qed.

  Lemma if_rec_is_persisted ℓ :
    ⊢ if_rec ℓ ⎡ persisted {[ ℓ := MaxNat 0 ]} ⎤.
  Proof. ifRecIntro. iFrame "#". Qed.

  (* Lemma or_lost_if_rec_at ℓ (P : dProp Σ) TV : *)
  (*   or_lost_post_crash_no_t ℓ (P TV) -∗ (if_rec ℓ P) TV. *)
  (* Proof. *)
  (*   iDestruct 1 as (CV) "[crashed_at disj]". *)
  (*   iIntros (OCV). monPred_simpl. *)
  (*   iIntros (? ?). monPred_simpl. *)
  (*   iIntros ([? Hlook]). iIntros (? ?). monPred_simpl. *)
  (*   iIntros "[%OV crashed_at_both]" (? ?) "persisted_loc". *)
  (*   simpl. *)
  (*   iNamed "crashed_at". *)
  (*   simplify_eq. *)
  (*   iDestruct (crashed_at_both_agree with "agree crashed_at_both") as %[-> ->]. *)
  (*   iApply monPred_mono. *)
  (*   2: { iDestruct "disj" as "[(%t & %look & _ & $) | %lost]". *)
  (*        rewrite view_sub_lookup Hlook /= in lost. *)
  (*        discriminate. } *)
  (*   etrans; first done. etrans; first done. done. *)
  (* Qed. *)

  (* Lemma or_lost_if_rec_embed ℓ P TV: *)
  (*   or_lost_post_crash_no_t ℓ P -∗ (if_rec ℓ ⎡ P ⎤) TV. *)
  (* Proof. *)
  (*   iIntros "H". iApply or_lost_if_rec_at. rewrite monPred_at_embed. iApply "H". *)
  (* Qed. *)

  (* Lemma if_rec_or_lost_with_t ℓ P : *)
  (*   or_lost_with_t ℓ P ⊢ if_rec ℓ (∃ t, P t). *)
  (* Proof. *)
  (*   iIntros "(%CV' & #crashed_at & disj)". *)
  (*   ifRecIntro. destruct look as [? Hlook]. *)
  (*   iDestruct "crashed_at" as (OV OCV OPV) "(<- & agree & rely)". *)
  (*   iDestruct "crashed_at_offset" as (OV') "crashed_at_both". *)
  (*   iDestruct (crashed_at_both_agree with "agree crashed_at_both") as %[-> ->]. *)
  (*   iDestruct "disj" as "[(% & % & #per & P) | %lost]". *)
  (*   { iExists t. iFrame "P". } *)
  (*   { rewrite view_sub_lookup Hlook /= in lost. *)
  (*     discriminate. } *)
  (* Qed. *)

  Global Instance into_if_rec_intro ℓ P : IntoIfRec ℓ P P := if_rec_intro ℓ P.

  Global Instance into_if_rec_if_rec ℓ P : IntoIfRec ℓ (if_rec ℓ P) P.
  Proof. done. Qed.

  Global Instance into_if_rec_sep ℓ P P' Q Q' :
    IntoIfRec ℓ P P' →
    IntoIfRec ℓ Q Q' →
    IntoIfRec ℓ (P ∗ Q) (P' ∗ Q').
  Proof.
    intros ? ?. rewrite /IntoIfRec.
    iIntros "[? ?]". iModIntro. iFrame.
  Qed.

  Global Instance big_sepM_into_if_rec `{Countable K} :
    ∀ ℓ (A : Type) Φ (Ψ : K → A → dProp Σ) (m : gmap K A),
    (∀ (k : K) (x : A), IntoIfRec ℓ (Φ k x) (Ψ k x)) →
    IntoIfRec ℓ ([∗ map] k↦x ∈ m, Φ k x)%I ([∗ map] k↦x ∈ m, Ψ k x)%I.
  Proof.
    intros. induction m using map_ind; rewrite /IntoIfRec.
    - rewrite 2!big_sepM_empty. iIntros "? !>". done.
    - rewrite !big_sepM_insert //.
      iIntros "[??]". iModIntro. iFrame.
  Qed.

End if_rec.
