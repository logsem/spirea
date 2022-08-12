From iris.proofmode Require Import tactics.
From iris.bi Require Import bi.
From iris.bi Require Import derived_laws.
From iris.base_logic Require Import iprop.

From self.base Require Import primitive_laws wpr_lifting.
From self.high Require Import dprop dprop_liftings resources modalities or_lost monpred_simpl.

(* The predicate [P] holds for [ℓ] or [ℓ] has been lost. *)
Definition if_rec `{nvmBaseFixedG Σ}
           (ℓ : loc) (P : dProp Σ) : dProp Σ :=
  ∀ (CV : view),
    ⌜ is_Some (CV !! ℓ) ⌝ -∗ crashed_at_d CV -∗ persisted_loc_d ℓ 0 -∗ P.

(* alt
  P ∨ (∃ CV, ⎡crashed_at CV⎤ ∗ ⌜ℓ ∉ dom (gset _) CV⌝ )
 *)

Class IntoIfRec `{nvmBaseFixedG Σ} ℓ (P : dProp Σ) (Q : dProp Σ) :=
  into_if_rec : P ⊢ if_rec ℓ Q.
Global Arguments IntoIfRec {_} {_} _ _%I _%I.
Global Arguments into_if_rec {_} _%I _%I.
Global Hint Mode IntoIfRec ! ! + + -  : typeclass_instances.

Section if_rec.
  Context `{nvmBaseFixedG Σ}.

  Local Ltac ifRecIntro :=
    iIntros (CV);
    iIntros "%look #crashed #pers".

  Lemma if_rec_intro ℓ P : P -∗ if_rec ℓ P.
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
      * iDestruct ("H" $! CV with "[//] crashed [$]") as "[$ _]".
      * iDestruct ("H" $! CV with "[//] crashed [$]") as "[_ $]".
    - iIntros "H". ifRecIntro.
      iSplit.
      * iDestruct "H" as "[H _]". iApply "H"; done.
      * iDestruct "H" as "[_ H]". iApply "H"; done.
  Qed.

  Lemma if_rec_sep ℓ (P Q : dProp Σ) :
    if_rec ℓ P ∗ if_rec ℓ Q -∗ if_rec ℓ (P ∗ Q)%I.
  Proof.
    iIntros "[P Q]". ifRecIntro.
    iDestruct ("P" $! CV with "[//] crashed [$]") as "$".
    iDestruct ("Q" $! CV with "[//] crashed [$]") as "$".
  Qed.

  Lemma if_rec_mono ℓ (P Q : dProp Σ) :
    (P -∗ Q) → if_rec ℓ P -∗ if_rec ℓ Q.
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

  Lemma modality_if_rec_mixin ℓ :
    modality_mixin (@if_rec Σ _ ℓ)
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

  Lemma if_rec_get CV ℓ P :
    is_Some (CV !! ℓ) → crashed_at_d CV -∗ persisted_loc_d ℓ 0 -∗ if_rec ℓ P -∗ P.
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
    ⊢ if_rec ℓ (∃ CV,
      ⌜ is_Some (CV !! ℓ) ⌝ ∗ crashed_at_d CV ∗ persisted_loc_d ℓ 0).
  Proof. ifRecIntro. iExists CV. iFrame "#%". Qed.

  Lemma if_rec_is_persisted ℓ :
    ⊢ if_rec ℓ (persisted_loc_d ℓ 0).
  Proof. ifRecIntro. iFrame "#". Qed.

  Lemma or_lost_if_rec_at ℓ (P : dProp Σ) TV nD :
    or_lost_post_crash_no_t ℓ (P (TV, nD)) -∗ (if_rec ℓ P) (TV, nD).
  Proof.
    iDestruct 1 as (CV) "[crash disj]".
    iIntros (CV'). monPred_simpl.
    iIntros ([??] [? [= <-]]). monPred_simpl.
    iIntros ([??]). iIntros ([??] [? [= <-]]). monPred_simpl.
    iIntros "crashed" ([??] [? [= <-]]) "pers".
    simpl.
    iDestruct (crashed_at_agree with "crash crashed") as %->.
    iApply monPred_mono.
    2: { iDestruct "disj" as "[(%t & %look & [_ $]) | %]".
         congruence. }
    split; last done.
    etrans; first done. etrans; first done. done.
  Qed.

  Lemma or_lost_if_rec_embed ℓ P TV nD :
    or_lost_post_crash_no_t ℓ P -∗ (if_rec ℓ ⎡ P ⎤) (TV, nD).
  Proof.
    iIntros "H". iApply or_lost_if_rec_at. rewrite monPred_at_embed. iApply "H".
  Qed.

  Lemma or_lost_if_rec_with_names_embed ℓ P TV nD :
    or_lost_post_crash_no_t ℓ (P nD) -∗
    (if_rec ℓ (with_gnames (λ nD', ⎡ P nD' ⎤))) (TV, nD).
  Proof.
    iIntros "H". iApply or_lost_if_rec_at.
    simpl. rewrite monPred_at_embed. iApply "H".
  Qed.

  (* Lemma if_rec_or_lost_with_t ℓ P : *)
  (*   or_lost_with_t ℓ P -∗ if_rec ℓ (∃ t, P t). *)
  (* Proof. *)
  (*   iIntros "(%CV' & #crashed' & disj)". *)
  (*   ifRecIntro. destruct look as [??]. *)
  (*   iDestruct (crashed_at_agree with "crashed crashed'") as %<-. *)
  (*   iDestruct "disj" as "[(% & % & #per & P) | %lost]"; last congruence. *)
  (*   iExists t. iFrame "P". *)
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

Opaque if_rec.
