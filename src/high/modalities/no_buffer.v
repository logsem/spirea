From iris.proofmode Require Import tactics.
From iris.bi Require Import bi.
From iris.bi Require Import derived_laws.
From iris.base_logic Require Import iprop.

From self.high Require Import dprop resources modalities.

(* Class BufferFree {Σ} (P : dProp Σ) := buffer_free : P ⊢ <nobuf> P. *)
(* Global Arguments BufferFree {_} _%I : simpl never. *)
(* Global Arguments buffer_free {_} _%I {_}. *)
(* Global Hint Mode BufferFree + ! : typeclass_instances. *)
(* Global Instance: Params (@BufferFree) 1 := {}. *)

Class IntoNoBuffer {Σ} (P : dProp Σ) (Q : dProp Σ) :=
  into_no_buffer : P ⊢ <nobuf> Q.
Global Arguments IntoNoBuffer {_} _%I _%I.
Global Arguments into_no_buffer {_} _%I _%I {_}.
Global Hint Mode IntoNoBuffer + ! -  : typeclass_instances.

Notation BufferFree p := (IntoNoBuffer p p).

Ltac iModel := iStartProof (iProp _); iIntros (TV).

Section no_buffer.
  Context `{Σ : gFunctors}.
  Implicit Types (P : dProp Σ).

  Lemma no_buff_at_alt P SV PV BV : ((<nobuf> P) (SV, PV, BV) = P (SV, PV, ∅))%I.
  Proof. done. Qed.

  Lemma no_buffer_at P TV : ((<nobuf> P) TV = P (store_view TV, flush_view TV, ∅))%I.
  Proof. destruct TV as [[??]?]. apply no_buff_at_alt. Qed.

  Lemma no_buffer_pure φ : ⌜φ⌝ -∗ <nobuf> (⌜φ⌝ : dProp Σ).
  Proof. iModel. by rewrite no_buffer_at monPred_at_pure. Qed.

  Lemma no_buffer_embed (P : iProp Σ) : ⎡P⎤ -∗ <nobuf> (⎡P⎤ : dProp Σ).
  Proof. iModel. rewrite no_buffer_at monPred_at_embed. naive_solver. Qed.

  Lemma no_buffer_mono P Q : (P ⊢ Q) → <nobuf> P ⊢ <nobuf> Q.
  Proof. intros H. iModel. rewrite 2!no_buffer_at. iApply H. Qed.

  Lemma no_buffer_emp : (emp : dProp Σ) ⊢ <nobuf> emp.
  Proof. iModel. by rewrite no_buffer_at monPred_at_emp. Qed.

  Lemma no_buffer_and P Q : <nobuf> (P ∧ Q) ⊣⊢ <nobuf> P ∧ <nobuf> Q.
  Proof. iModel. rewrite !no_buffer_at. rewrite monPred_at_and. naive_solver. Qed.

  Lemma no_buffer_sep P Q : <nobuf> (P ∗ Q) ⊣⊢ <nobuf> P ∗ <nobuf> Q.
  Proof. iModel. rewrite !no_buffer_at. rewrite monPred_at_sep. naive_solver. Qed.

  Lemma no_buffer_intuitionistically_2 P : □ <nobuf> P ⊢ <nobuf> □ P.
  Proof.
    iModel. rewrite !no_buffer_at monPred_at_intuitionistically. naive_solver.
  Qed.

  Lemma modality_no_buffer_mixin :
    modality_mixin (@no_buffer Σ)
      (MIEnvTransform IntoNoBuffer) (MIEnvTransform IntoNoBuffer).
  Proof.
    split; simpl; split_and?;
    eauto using bi.equiv_entails_1_2, no_buffer_and, no_buffer_emp,
      no_buffer_mono, no_buffer_sep.
    intros P Q. rewrite /IntoNoBuffer=> ->.
    by rewrite no_buffer_intuitionistically_2.
  Qed.
  Definition modality_no_buffer :=
    Modality _ modality_no_buffer_mixin.

  Global Instance from_modal_no_buffer P :
    FromModal True (modality_no_buffer) (<nobuf> P) (<nobuf> P) P.
  Proof. by rewrite /FromModal. Qed.

  (* [BufferFree] instances *)

  Global Instance buffer_free_objective P : Objective P → BufferFree P.
  Proof.
    intros O.
    rewrite /IntoNoBuffer. iModel. destruct TV as [[??]?].
    rewrite no_buffer_at. simpl. iApply objective_at.
  Qed.

  Global Instance into_no_buffer_if (b : bool) (P P' Q Q' : dProp Σ) :
    IntoNoBuffer P P' →
    IntoNoBuffer Q Q' →
    IntoNoBuffer (if b then P else Q) (if b then P' else Q').
  Proof. rewrite /IntoNoBuffer. destruct b; naive_solver. Qed.

  Global Instance into_no_buffer_sep (P P' Q Q' : dProp Σ) :
    IntoNoBuffer P P' → IntoNoBuffer Q Q' → IntoNoBuffer (P ∗ Q)%I (P' ∗ Q')%I.
  Proof. rewrite /IntoNoBuffer no_buffer_sep. by intros <- <-. Qed.

  Global Instance into_no_buffer_no_buffer P : IntoNoBuffer (<nobuf> P) P.
  Proof. rewrite /IntoNoBuffer. by iApply no_buffer_mono. Qed.

  Global Instance into_no_buffer_exists {A} (P Q : A → dProp Σ) :
    (∀ a, IntoNoBuffer (P a) (Q a)) → IntoNoBuffer (∃ a, P a) (∃ a, Q a).
  Proof.
    rewrite /IntoNoBuffer. iIntros (H).
    iDestruct 1 as (?) "P". iDestruct (H with "P") as "P".
    iModIntro. naive_solver.
  Qed.

  Lemma into_no_buffer_at P Q SV FV BV `{!IntoNoBuffer P Q} :
    P (SV, FV, BV) ⊢ Q (SV, FV, ∅).
  Proof.
    erewrite <- no_buff_at_alt.
    apply into_no_buffer.
    done.
  Qed.

  Lemma no_buffer_monPred_in SV FV PV :
    monPred_in (SV, FV, PV) ⊢@{dPropI Σ} <nobuf> monPred_in (SV, FV, ∅).
  Proof.
    iModel.
    iIntros (le). destruct TV as [[??]?]. rewrite no_buffer_at.
    iApply monPred_at_in. iPureIntro.
    repeat split; try apply le; done.
  Qed.

  Global Instance into_no_buffer_monPred_in SV FV PV :
    IntoNoBuffer (monPred_in (SV, FV, PV) : dProp Σ) (monPred_in (SV, FV, ∅)).
  Proof. apply no_buffer_monPred_in. Qed.

End no_buffer.

Section no_buffer_rules.
  (* Some less "basic" rules for <nobuf>. *)
  Context `{nvmFixedG Σ, hGD : nvmDeltaG Σ}.

  Lemma no_buffer_know_flush_lb `{AbstractState ST} ℓ (s : ST) :
    know_flush_lb ℓ s -∗ <nobuf> know_flush_lb ℓ s.
  Proof.
    rewrite /know_flush_lb.
    iModel.
    simpl.
    iDestruct 1 as (?) "HI". iExists _. iFrame.
  Qed.

  Global Instance buffer_free_know_flush_lb `{AbstractState ST} ℓ (s : ST) :
    BufferFree (know_flush_lb ℓ s).
  Proof. rewrite /IntoNoBuffer. eauto using no_buffer_know_flush_lb. Qed.

  Lemma no_buffer_know_store_lb `{AbstractState ST} ℓ (s : ST) :
    know_store_lb ℓ s -∗ <nobuf> know_store_lb ℓ s.
  Proof.
    rewrite /know_store_lb.
    iModel.
    simpl.
    iDestruct 1 as (?) "HI". iExists _. iFrame.
  Qed.

  Global Instance into_no_buffer_know_store_lb `{AbstractState ST} ℓ (s : ST) :
    BufferFree (know_store_lb ℓ s).
  Proof. rewrite /IntoNoBuffer. eauto using no_buffer_know_store_lb. Qed.

  Global Instance mapsto_na_buffer_free `{AbstractState ST} b ℓ q (ss : list ST) :
    BufferFree (mapsto_na b ℓ q ss).
  Proof. rewrite /mapsto_na. apply _. Qed.

End no_buffer_rules.

Section no_buffer_test.

  Context `{Σ : gFunctors}.
  Implicit Types (P : dProp Σ).

  Lemma test φ (P : iProp Σ) :
    ⌜ φ ⌝ -∗ ⎡ P ⎤ -∗ <nobuf> (⌜ φ ⌝ ∗ ⎡ P ⎤).
  Proof.
    iIntros "ph P".
    iModIntro.
    iFrame.
  Qed.

End no_buffer_test.
