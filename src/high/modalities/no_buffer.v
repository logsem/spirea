From iris.proofmode Require Import tactics.
From iris.bi Require Import bi.
From iris.bi Require Import derived_laws.
From iris.base_logic Require Import iprop.

From self Require Import solve_view_le.
From self.high Require Import dprop dprop_liftings resources modalities.

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

(* Import uPred. *)
(* Arguments uPred_holds _ !_.  *)

(* Lemma bar {M} : ⊢@{uPredI M} ∃ n, ▷^n False. *)
(* Proof. *)
(*   iLöb as "IH". *)
(*   iDestruct "IH" as (n) "H". *)
(*   iExists (S n). iApply "H". *)
(* Qed. *)

(* Lemma iLob :  *)

(* Lemma foo {M} (P Q1 Q2 : uPred M) : *)
(*   (P -∗ Q1 ∗ Q2) ⊢ (P -∗ Q1) ∗ (P -∗ Q2). *)
(* Proof. *)
(*   unseal. *)
(*   constructor. *)
(*   simpl. *)
(*   intros n x Hx H. *)
(*   specialize (H 0 ε). *)
(* Qed. *)

Section no_buffer.
  Context `{Σ : gFunctors}.
  Implicit Types (P : dProp Σ).

  Lemma no_buffer_at_alt P SV PV BV gnames :
    ((<nobuf> P) (SV, PV, BV, gnames) = P (SV, PV, ∅, gnames))%I.
  Proof. done. Qed.

  Lemma no_buffer_at P TV gnames :
    ((<nobuf> P) (TV, gnames) = P ((store_view TV, flush_view TV, ∅), gnames))%I.
  Proof. destruct TV as [[??]?]. apply no_buffer_at_alt. Qed.

  Global Instance no_buffer_proper :
    Proper ((⊣⊢) ==> (⊣⊢)) (@no_buffer Σ).
  Proof.
    intros ?? eq.
    iModel.
    rewrite 2!no_buffer_at.
    rewrite eq.
    naive_solver.
  Qed.

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

  Lemma no_buffer_or P Q : <nobuf> (P ∨ Q) ⊣⊢ <nobuf> P ∨ <nobuf> Q.
  Proof. iModel. rewrite !no_buffer_at. rewrite monPred_at_or. naive_solver. Qed.

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

  (* [BufferFree] instances. In this file we only declare instances for
  assertions that exist in Iris, instances for the assertions in our logic are
  added at their definitions. *)

  Global Instance buffer_free_objective P : Objective P → BufferFree P.
  Proof.
    intros O.
    rewrite /IntoNoBuffer. iModel. destruct TV as [[??]?].
    rewrite no_buffer_at. simpl. iApply objective_at.
  Qed.

  Global Instance into_no_buffer_with_gnames (P Q : _ → dProp Σ) :
    (∀ nD, IntoNoBuffer (P nD) (Q nD)) →
    IntoNoBuffer (with_gnames P) (with_gnames Q).
  Proof.
    rewrite /IntoNoBuffer.
    intros Hi.
    iModel.
    simpl.
    rewrite Hi.
    auto.
  Qed.

  Global Instance buffer_free_lift_d (Φ : _ → iProp Σ) :
    BufferFree (lift_d Φ).
  Proof. apply _. Qed.

  Global Instance into_no_buffer_if (b : bool) (P P' Q Q' : dProp Σ) :
    IntoNoBuffer P P' →
    IntoNoBuffer Q Q' →
    IntoNoBuffer (if b then P else Q) (if b then P' else Q').
  Proof. rewrite /IntoNoBuffer. destruct b; naive_solver. Qed.

  Global Instance into_no_buffer_emp :
    IntoNoBuffer (emp : dProp Σ)%I (emp)%I.
  Proof. rewrite /IntoNoBuffer. apply no_buffer_emp. Qed.

  Global Instance into_no_buffer_or (P P' Q Q' : dProp Σ) :
    IntoNoBuffer P P' → IntoNoBuffer Q Q' → IntoNoBuffer (P ∨ Q)%I (P' ∨ Q')%I.
  Proof. rewrite /IntoNoBuffer no_buffer_or. by intros <- <-. Qed.

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

  Lemma into_no_buffer_at P Q SV FV BV gnames `{!IntoNoBuffer P Q} :
    P (SV, FV, BV, gnames) ⊢ Q (SV, FV, ∅, gnames).
  Proof.
    erewrite <- no_buffer_at_alt.
    apply into_no_buffer.
    done.
  Qed.

  Lemma buffer_free_at P SV FV BV gnames `{!BufferFree P} :
    P (SV, FV, BV, gnames) ⊣⊢ P (SV, FV, ∅, gnames).
  Proof.
    iSplit; first iApply into_no_buffer_at.
    iApply monPred_mono.
    split; last done.
    solve_view_le.
  Qed.

  Lemma no_buffer_monPred_in SV FV PV gn :
    monPred_in (SV, FV, PV, gn) ⊢@{dPropI Σ} <nobuf> monPred_in (SV, FV, ∅, gn).
  Proof.
    iModel.
    iIntros (le). destruct TV as [[??]?]. rewrite no_buffer_at.
    iApply monPred_at_in. iPureIntro.
    repeat split; try apply le; done.
  Qed.

  Lemma later_no_buffer (P : dProp Σ) : ▷ (<nobuf> P) ⊢ <nobuf> (▷ P).
  Proof. iModel. rewrite 2!no_buffer_at monPred_at_later. naive_solver. Qed.

  Global Instance into_no_buffer_monPred_in SV FV PV gn :
    IntoNoBuffer (monPred_in (SV, FV, PV, gn) : dProp Σ) (monPred_in (SV, FV, ∅, gn)).
  Proof. apply no_buffer_monPred_in. Qed.

  Global Instance have_thread_view_buffer_free SV FV PV :
    IntoNoBuffer (have_thread_view (SV, FV, PV) : dProp Σ) (have_thread_view (SV, FV, ∅)).
  Proof.
    rewrite /IntoNoBuffer. iModel.
    destruct TV as [[??]?].
    iIntros ([[??]?]).
    iPureIntro.
    repeat split; done.
  Qed.

  Global Instance big_sepL_nil_no_buffer {A} (Φ : _ → A → dProp Σ) :
    BufferFree ([∗ list] k↦x ∈ [], Φ k x).
  Proof. simpl; apply _. Qed.
  Global Instance big_sepL_no_buffer {A} (Φ : _ → A → dProp Σ) l :
    (∀ k x, BufferFree (Φ k x)) → BufferFree ([∗ list] k↦x ∈ l, Φ k x).
  Proof. revert Φ. induction l as [|x l IH]=> Φ ? /=; try apply _. Qed.

  Global Instance big_sepM_into_no_buffer `{Countable K} {A} (Φ Ψ : K → A → dProp Σ) m :
    (∀ k x, IntoNoBuffer (Φ k x) (Ψ k x)) →
    IntoNoBuffer ([∗ map] k↦x ∈ m, Φ k x) ([∗ map] k↦x ∈ m, Ψ k x).
  Proof.
    intros into.
    rewrite /IntoNoBuffer.
    induction m as [|???? IH] using map_ind.
    - rewrite !big_opM_empty.
      iIntros "_ !>". done.
    - rewrite !big_opM_insert //.
      iIntros "[A B]".
      iDestruct (IH with "B") as "B".
      iModIntro.
      iFrame "A B".
  Qed.

  Global Instance buffer_free_have_SV ℓ t :
    BufferFree (have_SV ℓ t : dProp Σ).
  Proof. rewrite /IntoNoBuffer. iModel. destruct TV as [[??]?]. done. Qed.

  Global Instance buffer_free_have_FV ℓ t :
    BufferFree (have_FV ℓ t : dProp Σ).
  Proof. rewrite /IntoNoBuffer. iModel. destruct TV as [[??]?]. done. Qed.

  Global Instance buffer_free_have_FV_strong ℓ t :
    BufferFree (have_FV_strong ℓ t : dProp Σ).
  Proof. apply _. Qed.

  Global Instance into_no_buffer_proper :
    Proper ((⊣⊢) ==> (⊣⊢) ==> (impl)) (@IntoNoBuffer Σ).
  Proof.
    rewrite /IntoNoBuffer.
    intros P P' pEq Q Q' qEq ?.
    rewrite -pEq -qEq.
    assumption.
  Qed.

  Global Instance into_no_buffer_later (P P' : dProp Σ) :
    IntoNoBuffer P P' → IntoNoBuffer (▷ P)%I (▷ P')%I.
  Proof.
    rewrite /IntoNoBuffer.
    intros impl.
    rewrite impl.
    apply later_no_buffer.
  Qed.

End no_buffer.

(*
Section no_buffer_rules.
  (* Some less "basic" rules for <nobuf>. *)
  Context `{nvmG Σ, hGD : nvmDeltaG}.

End no_buffer_rules.
*)

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
