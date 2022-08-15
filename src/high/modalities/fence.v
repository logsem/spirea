From iris.proofmode Require Import tactics.
From iris.bi Require Import bi.
From iris.bi Require Import derived_laws.

From self Require Import solve_view_le.
From self.base Require Import primitive_laws.
From self.high Require Import dprop resources crash_weakestpre weakestpre
     recovery_weakestpre resources lifted_modalities modalities post_crash_modality protocol.
From self.high.modalities Require Import no_flush.

Class IntoFence {Σ} (P: dProp Σ) (Q : dProp Σ) :=
  into_fence : P ⊢ <fence> Q.
Global Arguments IntoFence {_} _%I _%I.
Global Arguments into_fence {_} _%I _%I {_}.
Global Hint Mode IntoFence + ! -  : typeclass_instances.

Section post_fence.
  Context `{Σ : gFunctors}.
  Implicit Types (P : dProp Σ).

  Lemma post_fence_at P TV gnames :
    ((<fence> P) (TV, gnames) =
       P (store_view TV, (flush_view TV ⊔ buffer_view TV), buffer_view TV, gnames))%I.
  Proof. done. Qed.

  Lemma post_fence_at_alt P SV PV BV gnames :
    ((<fence> P) (SV, PV, BV, gnames) = P (SV, PV ⊔ BV, BV, gnames))%I.
  Proof. done. Qed.

  Lemma post_fence_mono P Q : (P ⊢ Q) → <fence> P ⊢ <fence> Q.
  Proof. intros H. iModel. rewrite 2!post_fence_at. iApply H. Qed.

  Global Instance post_fence_mono' : Proper ((⊢) ==> (⊢)) (post_fence (Σ := Σ)).
  Proof. intros P Q. apply post_fence_mono. Qed.

  Lemma post_fence_wand P Q : (P -∗ Q) -∗ <fence> P -∗ <fence> Q.
  Proof.
    iModel. iIntros "H".
    introsIndex TV2 le.
    rewrite !post_fence_at.
    monPred_simpl.
    iApply "H".
    iPureIntro. split; last done. solve_view_le.
  Qed.

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
    iModel.
    cbn.
    rewrite monPred_at_sep.
    iSplit; iIntros "$".
  Qed.

  Global Instance into_sep_post_fence P Q1 Q2 :
    IntoSep P Q1 Q2 →
    IntoSep (<fence> P) (<fence> Q1) (<fence> Q2).
  Proof.
  rewrite /IntoSep /= => ->. rewrite post_fence_sep. done. Qed.

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
    iModel.
    rewrite post_fence_at.
    rewrite monPred_at_objectively.
    naive_solver.
  Qed.

  Lemma post_fence_no_flush P : <fence> (<noflush> P) ⊢ P.
  Proof.
    iModel.
    rewrite post_fence_at. rewrite into_no_flush_at.
    iApply monPred_mono. split; last done. solve_view_le.
  Qed.

  Lemma post_fence_flush_free P `{FlushFree P} : post_fence P ⊢ P.
  Proof.
    rewrite -> (into_no_flush P P) at 1.
    iModel.
    rewrite post_fence_at. rewrite into_no_flush_at.
    iApply monPred_mono. split; last done. solve_view_le.
  Qed.

  Global Instance post_fence_persistent P :
    Persistent P → Persistent (post_fence P).
  Proof.
    rewrite /Persistent.
    intros pers.
    iModel.
    iIntros "H".
    rewrite post_fence_at.
    iApply pers.
    iApply "H".
  Qed.

  Lemma post_fence_extract P Q1 Q2 :
    <fence> P -∗ (P -∗ Q1 ∗ <noflush> Q2) -∗ <fence> Q1 ∗ Q2.
  Proof.
    iIntros "P W".
    iDestruct (post_fence_wand with "W P") as "[$ Q]".
    iDestruct (post_fence_no_flush with "Q") as "$".
  Qed.

  Lemma post_fence_extract' P Q `{!FlushFree Q} :
    post_fence P -∗ (P -∗ Q) -∗ Q.
  Proof.
    iIntros "P W".
    iDestruct (post_fence_wand with "W P") as "Q".
    iDestruct (post_fence_flush_free with "Q") as "$".
  Qed.

End post_fence.

Class IntoFenceSync `{nvmG Σ, nvmDeltaG}
      (P: dProp Σ) (Q : dProp Σ) :=
  into_fence_sync : P ⊢ <fence_sync> Q.
Global Arguments IntoFenceSync {_} {_} {_} _%I _%I.
Global Arguments into_fence_sync {_} _%I _%I {_}.
Global Hint Mode IntoFenceSync - - + ! -  : typeclass_instances.

Section post_fence_sync.
  Context `{nvmG Σ, nvmDeltaG}.

  Implicit Types (P : dProp Σ).

  Lemma post_fenc_sync_post_fence P :
    <fence> P -∗ <fence_sync> P.
  Proof. iModel. simpl. iIntros "$ _". done. Qed.

  (* Lemma post_fence_sync_at P TV : *)
  (*   ((<fence_sync> P) TV = *)
  (*      P (store_view TV, (flush_view TV ⊔ buffer_view TV), buffer_view TV))%I. *)
  (* Proof. done. Qed. *)

  (* Lemma post_fence_sync_at_alt P SV PV BV : *)
  (*   ((<fence_sync> P) (SV, PV, BV) = P (SV, PV ⊔ BV, BV))%I. *)
  (* Proof. done. Qed. *)

  Lemma post_fence_sync_mono P Q : (P ⊢ Q) → <fence_sync> P ⊢ <fence_sync> Q.
  Proof.
    intros Hi. iModel. simpl.
    iIntros "H pers". iApply Hi. iApply "H". done.
  Qed.

  (* Global Instance post_fence_sync_mono' : Proper ((⊢) ==> (⊢)) (post_fence (Σ := Σ)). *)
  (* Proof. intros P Q. apply post_fence_sync_mono. Qed. *)

  (* Lemma post_fence_sync_wand P Q : (P -∗ Q) -∗ <fence_sync> P -∗ <fence_sync> Q. *)
  (* Proof. *)
  (*   iModel. iIntros "H". iIntros (TV2 le) "P". *)
  (*   rewrite !post_fence_sync_at. *)
  (*   monPred_simpl. *)
  (*   iApply "H". { iPureIntro. solve_view_le. } *)
  (*   done. *)
  (* Qed. *)

  (* Lemma post_fence_sync_idemp P : <fence_sync> <fence_sync> P ⊢ <fence_sync> P. *)
  (* Proof. *)
  (*   iModel. destruct TV as [[??]?]. rewrite !post_fence_sync_at. simpl. *)
  (*   iApply monPred_mono. repeat split; auto. *)
  (*   rewrite -assoc. *)
  (*   f_equiv. *)
  (*   rewrite view_join_id. *)
  (*   reflexivity. *)
  (* Qed. *)

  Lemma post_fence_sync_intro P : P ⊢ <fence_sync> P.
  Proof.
    iModel. destruct TV as [[??]?]. simpl.
    iIntros "P pers".
    iApply (monPred_mono with "P"). repeat split; auto using view_le_l.
  Qed.

  Lemma post_fence_sync_emp : (emp : dProp Σ) ⊢ <fence_sync> emp.
  Proof. apply post_fence_sync_intro. Qed.

  Lemma post_fence_sync_and P Q : <fence_sync> (P ∧ Q) ⊣⊢ <fence_sync> P ∧ <fence_sync> Q.
  Proof.
    iModel. simpl.
    rewrite monPred_at_and. iSplit.
    - iIntros "impl".
      iSplit.
      * iIntros "pers". iDestruct ("impl" with "pers") as "[$ _]".
      * iIntros "pers". iDestruct ("impl" with "pers") as "[_ $]".
    - iIntros "impl pers".
      iSplit.
      * iDestruct "impl" as "[impl _]". iApply "impl". done.
      * iDestruct "impl" as "[_ impl]". iApply "impl". done.
  Qed.

  Lemma post_fence_sync_sep P Q : <fence_sync> P ∗ <fence_sync> Q -∗ <fence_sync> (P ∗ Q) .
  Proof.
    iStartProof (iProp _). iIntros ([[??]?]).
    cbn.
    rewrite monPred_at_sep.
    iIntros "[HP HQ] #per".
    iDestruct ("HP" with "per") as "$".
    iDestruct ("HQ" with "per") as "$".
  Qed.

  (* Global Instance into_sep_post_fence_sync P Q1 Q2 : *)
  (*   IntoSep P Q1 Q2 → *)
  (*   IntoSep (<fence_sync> P) (<fence_sync> Q1) (<fence_sync> Q2). *)
  (* Proof. *)
  (* rewrite /IntoSep /= => ->. rewrite post_fence_sync_sep. done. Qed. *)

  Lemma post_fence_sync_intuitionistically_2 P : □ <fence_sync> P ⊢ <fence_sync> □ P.
  Proof.
    iModel. simpl. rewrite monPred_at_intuitionistically.
    iIntros "#impl #pers". iModIntro. iApply "impl". done.
  Qed.

  Lemma modality_post_fence_sync_mixin :
    modality_mixin (@post_fence_sync _ _)
      (MIEnvTransform IntoFenceSync) (MIEnvTransform IntoFenceSync).
  Proof.
    split; simpl; split_and?;
    eauto using bi.equiv_entails_1_2, post_fence_sync_and, post_fence_sync_emp,
      post_fence_sync_mono, post_fence_sync_sep.
    intros P Q. rewrite /IntoFenceSync=> ->.
    by rewrite post_fence_sync_intuitionistically_2.
  Qed.
  Definition modality_post_fence_sync :=
    Modality _ modality_post_fence_sync_mixin.

  Global Instance from_modal_post_fence_sync P :
    FromModal True (modality_post_fence_sync) (<fence_sync> P) (<fence_sync> P) P.
  Proof. by rewrite /FromModal. Qed.

  Global Instance into_post_fence_sync_default P : IntoFenceSync P P.
  Proof. apply post_fence_sync_intro. Qed.

  Global Instance into_post_fence_sync_fence P : IntoFenceSync (<fence_sync> P) P.
  Proof. done. Qed.

  (* Lemma post_fence_sync_objective' P : post_fence (<obj> P) ⊢ P. *)
  (* Proof. *)
  (*   iStartProof (iProp _). iIntros (TV). *)
  (*   rewrite post_fence_sync_at. *)
  (*   rewrite monPred_at_objectively. *)
  (*   naive_solver. *)
  (* Qed. *)

  (* Lemma post_fence_sync_no_flush P : <fence_sync> (<noflush> P) ⊢ P. *)
  (* Proof. *)
  (*   iModel. *)
  (*   rewrite post_fence_sync_at. rewrite into_no_flush_at. *)
  (*   iApply monPred_mono. solve_view_le. *)
  (* Qed. *)

  (* Lemma post_fence_sync_flush_free P `{FlushFree P} : post_fence P ⊢ P. *)
  (* Proof. *)
  (*   rewrite -> (into_no_flush P P) at 1. *)
  (*   iModel. *)
  (*   rewrite post_fence_sync_at. rewrite into_no_flush_at. *)
  (*   iApply monPred_mono. solve_view_le. *)
  (* Qed. *)

  (* NOTE: This seems to not hold. *)
  (* Global Instance post_fence_sync_persistent P `{!Persistent P} : *)
  (*   Persistent (post_fence_sync P). *)
  (* Proof. *)
  (*   rewrite /Persistent. *)
  (*   iStartProof (iProp _). *)
  (*   simpl. *)
  (*   iIntros (TV) "H". *)
  (*   assert (Persistent (persisted TV.2 -∗ P (store_view TV, flush_view TV ⊔ TV.2, TV.2))). *)
  (*   { apply: wand_persistent. *)
  (*     Plain *)
  (*   specialize (wand_persistent (persisted TV.2) (P (store_view TV, flush_view TV ⊔ TV.2, TV.2))). *)
  (*   iModIntro. *)
  (*   rewrite post_fence_sync_at. *)
  (*   iApply pers. *)
  (*   iApply "H". *)
  (* Qed. *)

  (* Lemma post_fence_sync_extract P Q1 Q2 : *)
  (*   <fence_sync> P -∗ (P -∗ Q1 ∗ <noflush> Q2) -∗ <fence_sync> Q1 ∗ Q2. *)
  (* Proof. *)
  (*   iIntros "P W". *)
  (*   iDestruct (post_fence_sync_wand with "W P") as "[$ Q]". *)
  (*   iDestruct (post_fence_sync_no_flush with "Q") as "$". *)
  (* Qed. *)

  (* Lemma post_fence_sync_extract' P Q `{!FlushFree Q} : *)
  (*   post_fence_sync P -∗ (P -∗ Q) -∗ Q. *)
  (* Proof. *)
  (*   iIntros "P W". *)
  (*   iDestruct (post_fence_sync_wand with "W P") as "Q". *)
  (*   iDestruct (post_fence_sync_flush_free with "Q") as "$". *)
  (* Qed. *)

End post_fence_sync.
