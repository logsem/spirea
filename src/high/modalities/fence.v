From iris.proofmode Require Import tactics.
From iris.bi Require Import bi.
From iris.bi Require Import derived_laws.

From self.high Require Import dprop resources crash_weakestpre weakestpre
     recovery_weakestpre resources lifted_modalities modalities post_crash_modality protocol.

Class IntoFence {Σ} (P: dProp Σ) (Q : dProp Σ) :=
  into_fence : P ⊢ <fence> Q.
Global Arguments IntoFence {_} _%I _%I.
Global Arguments into_fence {_} _%I _%I {_}.
Global Hint Mode IntoFence + ! -  : typeclass_instances.

Section post_fence.
  Context `{Σ : gFunctors}.
  Implicit Types (P : dProp Σ).

  Lemma post_fence_at P tv :
    ((<fence> P) tv = P (store_view tv, (flush_view tv ⊔ buffer_view tv), buffer_view tv))%I.
  Proof. done. Qed.

  Lemma post_fence_at_alt P SV PV BV :
    ((<fence> P) (SV, PV, BV) = P (SV, PV ⊔ BV, BV))%I.
  Proof. done. Qed.

  Lemma post_fence_mono P Q : (P ⊢ Q) → <fence> P ⊢ <fence> Q.
  Proof. intros H. iModel. rewrite 2!post_fence_at. iApply H. Qed.

  Lemma post_fence_idemp P : <fence> <fence> P ⊢ <fence> P.
  Proof.
    iModel. destruct TV as [[??]?]. rewrite !post_fence_at. simpl.
    iApply monPred_mono. repeat split; auto.
    rewrite -assoc.
    f_equiv.
    rewrite view_join_id.
    reflexivity.
  Qed.

  Lemma post_fence_intro P : P ⊢ <fence> P.
  Proof.
    iModel. destruct TV as [[??]?]. rewrite post_fence_at /=.
    iApply monPred_mono. repeat split; auto using view_le_l.
  Qed.

  Lemma post_fence_emp : (emp : dProp Σ) ⊢ <fence> emp.
  Proof. apply post_fence_intro. Qed.

  Lemma post_fence_and P Q : <fence> (P ∧ Q) ⊣⊢ <fence> P ∧ <fence> Q.
  Proof. iModel. rewrite !post_fence_at. rewrite monPred_at_and. naive_solver. Qed.

  Lemma post_fence_sep P Q : <fence> (P ∗ Q) ⊣⊢ <fence> P ∗ <fence> Q.
  Proof.
    iStartProof (iProp _). iIntros ([[sv pv] bv]).
    cbn.
    rewrite monPred_at_sep.
    iSplit; iIntros "$".
  Qed.

  Lemma post_fence_intuitionistically_2 P : □ <fence> P ⊢ <fence> □ P.
  Proof.
    iModel. rewrite !post_fence_at monPred_at_intuitionistically. naive_solver.
  Qed.

  Lemma modality_post_fence_mixin :
    modality_mixin (@post_fence Σ)
      (MIEnvTransform IntoFence) (MIEnvTransform IntoFence).
  Proof.
    split; simpl; split_and?;
    eauto using bi.equiv_entails_1_2, post_fence_and, post_fence_emp,
      post_fence_mono, post_fence_sep.
    intros P Q. rewrite /IntoFence=> ->.
    by rewrite post_fence_intuitionistically_2.
  Qed.
  Definition modality_post_fence :=
    Modality _ modality_post_fence_mixin.

  Global Instance from_modal_post_fence P :
    FromModal True (modality_post_fence) (<fence> P) (<fence> P) P.
  Proof. by rewrite /FromModal. Qed.

  Global Instance into_post_fence_default P : IntoFence P P.
  Proof. apply post_fence_intro. Qed.

  Global Instance into_post_fence_fence P : IntoFence (<fence> P) P.
  Proof. done. Qed.

  Lemma post_fence_objective' P : post_fence (<obj> P) ⊢ P.
  Proof.
    iStartProof (iProp _). iIntros (TV).
    rewrite post_fence_at.
    rewrite monPred_at_objectively.
    naive_solver.
  Qed.

  Lemma post_fence_objective P `{!Objective P} : post_fence P ⊢ P.
  Proof.
    iStartProof (iProp _). iIntros (TV).
    rewrite post_fence_at. iApply objective_at.
  Qed.

  Global Instance post_fence_persistent P :
    Persistent P → Persistent (post_fence P).
  Proof.
    rewrite /Persistent.
    intros pers.
    iStartProof (iProp _).
    iIntros (TV) "H".
    rewrite post_fence_at.
    iApply pers.
    iApply "H".
  Qed.

  Lemma post_fence_extract P Q : post_fence P -∗ (P -∗ <obj> Q) -∗ Q.
  Proof.
    iIntros "P pToQ".
    iEval (rewrite -(post_fence_objective' Q)).
    iModIntro. iApply "pToQ". done.
  Qed.

  Lemma post_fence_extract' P Q `{!Objective Q} : post_fence P -∗ (P -∗ Q) -∗ Q.
  Proof.
    iIntros "P pToQ".
    iApply (post_fence_extract with "P").
    rewrite -(objective_objectively Q).
    done.
  Qed.

End post_fence.
