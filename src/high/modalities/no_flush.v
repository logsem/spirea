From iris.proofmode Require Import tactics.
From iris.bi Require Import bi.
From iris.bi Require Import derived_laws.
From iris.base_logic Require Import iprop.

From self.high Require Import dprop resources modalities.

Class IntoNoflushfer {Σ} (P : dProp Σ) (Q : dProp Σ) :=
  into_no_flush : P ⊢ <noflush> Q.
Global Arguments IntoNoflushfer {_} _%I _%I.
Global Arguments into_no_flush {_} _%I _%I {_}.
Global Hint Mode IntoNoflushfer + ! -  : typeclass_instances.

Notation FlushFree p := (IntoNoflushfer p p).

Section no_flush.
  Context `{Σ : gFunctors}.
  Implicit Types (P : dProp Σ).

  Lemma no_flush_at_alt P SV PV BV : ((<noflush> P) (SV, PV, BV) = P (SV, ∅, ∅))%I.
  Proof. done. Qed.

  Lemma no_flush_at P TV : ((<noflush> P) TV = P (store_view TV, ∅, ∅))%I.
  Proof. destruct TV as [[??]?]. apply no_flush_at_alt. Qed.

  Lemma no_flush_pure φ : ⌜φ⌝ -∗ <noflush> (⌜φ⌝ : dProp Σ).
  Proof. iModel. by rewrite no_flush_at monPred_at_pure. Qed.

  Lemma no_flush_embed (P : iProp Σ) : ⎡P⎤ -∗ <noflush> (⎡P⎤ : dProp Σ).
  Proof. iModel. rewrite no_flush_at monPred_at_embed. naive_solver. Qed.

  Lemma no_flush_mono P Q : (P ⊢ Q) → <noflush> P ⊢ <noflush> Q.
  Proof. intros H. iModel. rewrite 2!no_flush_at. iApply H. Qed.

  Lemma no_flush_emp : (emp : dProp Σ) ⊢ <noflush> emp.
  Proof. iModel. by rewrite no_flush_at monPred_at_emp. Qed.

  Lemma no_flush_and P Q : <noflush> (P ∧ Q) ⊣⊢ <noflush> P ∧ <noflush> Q.
  Proof. iModel. rewrite !no_flush_at. rewrite monPred_at_and. naive_solver. Qed.

  Lemma no_flush_sep P Q : <noflush> (P ∗ Q) ⊣⊢ <noflush> P ∗ <noflush> Q.
  Proof. iModel. rewrite !no_flush_at. rewrite monPred_at_sep. naive_solver. Qed.

  Lemma no_flush_intuitionistically_2 P : □ <noflush> P ⊢ <noflush> □ P.
  Proof.
    iModel. rewrite !no_flush_at monPred_at_intuitionistically. naive_solver.
  Qed.

  Lemma modality_no_flush_mixin :
    modality_mixin (@no_flush Σ)
      (MIEnvTransform IntoNoflushfer) (MIEnvTransform IntoNoflushfer).
  Proof.
    split; simpl; split_and?;
    eauto using bi.equiv_entails_1_2, no_flush_and, no_flush_emp,
      no_flush_mono, no_flush_sep.
    intros P Q. rewrite /IntoNoflushfer=> ->.
    by rewrite no_flush_intuitionistically_2.
  Qed.
  Definition modality_no_flush :=
    Modality _ modality_no_flush_mixin.

  Global Instance from_modal_no_flush P :
    FromModal True (modality_no_flush) (<noflush> P) (<noflush> P) P.
  Proof. by rewrite /FromModal. Qed.

  (* [FlushFree] instances. In this file we only declare instances for
  assertions that exist in Iris, instances for the assertions in our logic are
  added at their definitions. *)

  Global Instance flush_free_objective P : Objective P → FlushFree P.
  Proof.
    intros O.
    rewrite /IntoNoflushfer. iModel. destruct TV as [[??]?].
    rewrite no_flush_at. simpl. iApply objective_at.
  Qed.

  Global Instance into_no_flush_if (b : bool) (P P' Q Q' : dProp Σ) :
    IntoNoflushfer P P' →
    IntoNoflushfer Q Q' →
    IntoNoflushfer (if b then P else Q) (if b then P' else Q').
  Proof. rewrite /IntoNoflushfer. destruct b; naive_solver. Qed.

  Global Instance into_no_flush_emp :
    IntoNoflushfer (emp : dProp Σ)%I (emp)%I.
  Proof. rewrite /IntoNoflushfer. apply no_flush_emp. Qed.

  Global Instance into_no_flush_sep (P P' Q Q' : dProp Σ) :
    IntoNoflushfer P P' → IntoNoflushfer Q Q' → IntoNoflushfer (P ∗ Q)%I (P' ∗ Q')%I.
  Proof. rewrite /IntoNoflushfer no_flush_sep. by intros <- <-. Qed.

  Global Instance into_no_flush_no_flush P : IntoNoflushfer (<noflush> P) P.
  Proof. rewrite /IntoNoflushfer. by iApply no_flush_mono. Qed.

  Global Instance into_no_flush_exists {A} (P Q : A → dProp Σ) :
    (∀ a, IntoNoflushfer (P a) (Q a)) → IntoNoflushfer (∃ a, P a) (∃ a, Q a).
  Proof.
    rewrite /IntoNoflushfer. iIntros (H).
    iDestruct 1 as (?) "P". iDestruct (H with "P") as "P".
    iModIntro. naive_solver.
  Qed.

  Lemma into_no_flush_at P Q SV FV BV `{!IntoNoflushfer P Q} :
    P (SV, FV, BV) ⊢ Q (SV, ∅, ∅).
  Proof.
    erewrite <- no_flush_at_alt.
    apply into_no_flush.
    done.
  Qed.

  Lemma no_flush_monPred_in SV FV PV :
    monPred_in (SV, FV, PV) ⊢@{dPropI Σ} <noflush> monPred_in (SV, ∅, ∅).
  Proof.
    iModel.
    iIntros (le). destruct TV as [[??]?]. rewrite no_flush_at.
    iApply monPred_at_in. iPureIntro.
    repeat split; try apply le; done.
  Qed.

  Global Instance into_no_flush_monPred_in SV FV PV :
    IntoNoflushfer (monPred_in (SV, FV, PV) : dProp Σ) (monPred_in (SV, ∅, ∅)).
  Proof. apply no_flush_monPred_in. Qed.

  Global Instance big_sepL_nil_no_flush {A} (Φ : _ → A → dProp Σ) :
    FlushFree ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL_no_flush {A} (Φ : _ → A → dProp Σ) l :
    (∀ k x, FlushFree (Φ k x)) → FlushFree ([∗ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; try apply _. Qed.

End no_flush.

Section no_flush_test.

  Context `{Σ : gFunctors}.
  Implicit Types (P : dProp Σ).

  Lemma test φ (P : iProp Σ) :
    ⌜ φ ⌝ -∗ ⎡ P ⎤ -∗ <noflush> (⌜ φ ⌝ ∗ ⎡ P ⎤).
  Proof.
    iIntros "ph P".
    iModIntro.
    iFrame.
  Qed.

End no_flush_test.
