From iris.proofmode Require Import tactics.
From iris.bi Require Import bi.
From iris.bi Require Import derived_laws.

From self.high Require Import dprop resources crash_weakestpre weakestpre
     recovery_weakestpre resources lifted_modalities modalities post_crash_modality protocol.

Class IntoNoBuffer {Σ} (P : dProp Σ) (Q : dProp Σ) :=
  into_no_buffer : P ⊢ <nobuf> Q.
Global Arguments IntoNoBuffer {_} _%I _%I.
Global Arguments into_no_buffer {_} _%I _%I {_}.
Global Hint Mode IntoNoBuffer + ! -  : typeclass_instances.

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

  (* Lemma no_buffer_know_protocol ϕ *)
  (*   know_flush_lb ℓa n -∗  *)

  Global Instance from_modal_no_buffer P :
    FromModal True (modality_no_buffer) (<nobuf> P) (<nobuf> P) P.
  Proof. by rewrite /FromModal. Qed.

  Global Instance into_no_buffer_pure φ : IntoNoBuffer (⌜φ⌝ : dProp Σ)%I ⌜φ⌝.
  Proof. rewrite /IntoNoBuffer. eauto using no_buffer_pure. Qed.

  Global Instance into_no_buffer_embed (P : iProp Σ) : IntoNoBuffer ⎡P⎤ ⎡P⎤.
  Proof. rewrite /IntoNoBuffer. eauto using no_buffer_embed. Qed.

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
    iDestruct 1 as (???) "HI".
    iExists _, _.
    iFrame. done.
  Qed.

  Global Instance into_no_buffer_know_flush_lb  `{AbstractState ST} ℓ s :
    IntoNoBuffer (know_flush_lb ℓ s) (know_flush_lb ℓ s).
  Proof. rewrite /IntoNoBuffer. eauto using no_buffer_know_flush_lb. Qed.

End no_buffer_rules.

Section no_buffer_test.

  Context `{Σ : gFunctors}.
  Implicit Types (P : dProp Σ).

  Lemma test φ (P : iProp Σ) :
    ⌜φ⌝ -∗ ⎡P⎤ -∗ <nobuf> (⌜φ⌝ ∗ ⎡P⎤).
  Proof.
    iIntros "ph P".
    iModIntro.
    iFrame.
  Qed.

End no_buffer_test.
