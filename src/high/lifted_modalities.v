(** Here we "lift" the various modalities in Perennial from [iProp] to
[dProp]. This is mostly just boilerplate. *)

From iris.bi Require Import derived_laws.
From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic.lib Require Import ncfupd.
From Perennial.program_logic Require Import crash_weakestpre cfupd.

From self.high Require Import dprop monpred_simpl.

Program Definition uPred_fupd_split_level_def `{!invGS Σ}
           (E1 E2 : coPset) (k : nat) mj (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV, uPred_fupd_split_level_def E1 E2 k mj (P TV))%I _.
Next Obligation. solve_proper. Qed.

Definition uPred_fupd_split_level_aux `{!invGS Σ} : seal uPred_fupd_split_level_def.
Proof. by eexists. Qed.
Definition uPred_fupd_split_level `{!invGS Σ} := uPred_fupd_split_level_aux.(unseal).
Definition uPred_fupd_split_level_eq `{!invGS Σ} :
    uPred_fupd_split_level = uPred_fupd_split_level_def :=
  uPred_fupd_split_level_aux.(seal_eq).

Definition uPred_fupd_level_def `{!invGS Σ} (E1 E2 : coPset) (k : nat) (P : dProp Σ) : dProp Σ :=
  uPred_fupd_split_level E1 E2 k None P.
Definition uPred_fupd_level_aux `{!invGS Σ} : seal uPred_fupd_level_def.
Proof. by eexists. Qed.
Definition uPred_fupd_level `{!invGS Σ} := uPred_fupd_level_aux.(unseal).
Definition uPred_fupd_level_eq `{!invGS Σ} : uPred_fupd_level = uPred_fupd_level_def :=
  uPred_fupd_level_aux.(seal_eq).

Notation "| k , j ={ E1 , E2 }=> Q" := (uPred_fupd_split_level E1 E2 k j Q) : bi_scope.
Notation "| k , j ={ E1 }=> Q" := (uPred_fupd_split_level E1 E1 k j Q) : bi_scope.
Notation "| k ={ E1 , E2 }=> Q" := (uPred_fupd_level E1 E2 k Q) : bi_scope.
Notation "| k ={ E1 }=> Q" := (uPred_fupd_level E1 E1 k Q) : bi_scope.

Section lifted_fupd_level.
  Context `{!invGS Σ}.

  (*** fupd_level*)

  Global Instance except_0_fupd_level' E1 E2 k P :
    IsExcept0 (|k={E1,E2}=> P).
  Proof. Abort. (* by rewrite /IsExcept0 except_0_fupd_level. Qed. *)

  Global Instance from_modal_fupd_level E k P :
    FromModal True modality_id (|k={E}=> P) (|k={E}=> P) P.
  Proof. Abort. (* by rewrite /FromModal True /= -fupd_level_intro. Qed. *)

  Global Instance elim_modal_bupd_fupd_level p E1 E2 k P Q :
    ElimModal True p false (|==> P) P (|k={E1,E2}=> Q) (|k={E1,E2}=> Q) | 10.
  Proof. Abort.
  (*   by rewrite /ElimModal intuitionistically_if_elim *)
  (*     (bupd_fupd_level E1 k) fupd_level_frame_r wand_elim_r fupd_level_trans. *)
  (* Qed. *)
  Global Instance elim_modal_fupd_level_fupd_level p E1 E2 E3 k P Q :
    ElimModal True p false (|k={E1,E2}=> P) P (|k={E1,E3}=> Q) (|k={E2,E3}=> Q).
  Proof. Abort.
  (*   by rewrite /ElimModal intuitionistically_if_elim *)
  (*     fupd_level_frame_r wand_elim_r fupd_level_trans. *)
  (* Qed. *)
  Lemma fupd_split_level_unfold_at E1 E2 k mj P TV :
    (uPred_fupd_split_level E1 E2 k mj P) TV = fupd_level.uPred_fupd_split_level E1 E2 k mj (P TV).
  Proof.
    rewrite uPred_fupd_split_level_eq.
    rewrite /uPred_fupd_split_level_def.
    rewrite fupd_level.uPred_fupd_split_level_eq.
    reflexivity.
  Qed.

  (* NOTE: This lemma may not be needed anymore. *)
  Lemma fupd_level_unfold_at E1 E2 k P TV :
    (uPred_fupd_level E1 E2 k P) TV = fupd_level.uPred_fupd_level E1 E2 k (P TV).
  Proof.
    rewrite uPred_fupd_level_eq.
    rewrite /uPred_fupd_level_def.
    rewrite fupd_level.uPred_fupd_level_eq.
    apply fupd_split_level_unfold_at.
  Qed.

End lifted_fupd_level.

Program Definition ncfupd_def `{!invGS Σ, !crashGS Σ} (E1 E2 : coPset) (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV, ncfupd E1 E2 (P TV))%I _.
Next Obligation. solve_proper. Qed.
Definition ncfupd_aux `{!invGS Σ, !crashGS Σ} : seal (ncfupd_def). Proof. by eexists. Qed.
Definition ncfupd `{!invGS Σ, !crashGS Σ} := ncfupd_aux.(unseal).
Definition ncfupd_eq `{!invGS Σ, !crashGS Σ} : ncfupd = ncfupd_def := ncfupd_aux.(seal_eq).

Notation "|NC={ E1 }=> Q" := (ncfupd E1 E1 Q)
  (at level 99, E1 at level 50, Q at level 200,
   format "'[  ' |NC={ E1 }=>  '/' Q ']'") : bi_scope.
Notation "|NC={ E1 , E2 }=> P" := (ncfupd E1 E2 P)
      (at level 99, E1, E2 at level 50, P at level 200,
       format "'[  ' |NC={ E1 , E2 }=>  '/' P ']'") : bi_scope.
Notation "|NC={ Eo } [ Ei ]▷=> Q" := (∀ q, NC q -∗ |={Eo,Ei}=> ▷ |={Ei,Eo}=> Q ∗ NC q)%I
  (at level 99, Eo, Ei at level 50, Q at level 200,
   format "'[  ' |NC={ Eo } [ Ei ]▷=>  '/' Q ']'") : bi_scope.
Notation "|NC={ E1 } [ E2 ]▷=>^ n Q" := (Nat.iter n (λ P, |NC={E1}[E2]▷=> P) Q)%I
  (at level 99, E1, E2 at level 50, n at level 9, Q at level 200,
   format "'[  ' |NC={ E1 } [ E2 ]▷=>^ n  '/' Q ']'").

Program Definition cfupd `{!invGS Σ, !crashGS Σ} E1 (P : dProp Σ) :=
  (⎡C⎤ -∗ |={E1}=> P)%I.
  (* MonPred (λ TV, cfupd k E1 (P TV))%I _. *)
(* Next Obligation. solve_proper. Qed. *)

Notation "|C={ E1 }=> P" := (cfupd E1 P)
      (at level 99, E1 at level 50, P at level 200,
       format "'[  ' |C={ E1 }=>  '/' P ']'").

Section lifted_modalities.
  Context `{crashGS Σ, invGS Σ}.

  (*** ncfupd *)

  Global Instance from_modal_ncfupd E P :
    FromModal True modality_id (|NC={E}=> P) (|NC={E}=> P) P.
  Proof.
    rewrite /FromModal ncfupd_eq /=. iStartProof (iProp _). iIntros (_ TV).
    iIntros "$". rewrite ncfupd.ncfupd_eq. iIntros (q) "$". done.
  Qed.

  Lemma ncfupd_unfold_at E1 E2 P TV :
    (ncfupd E1 E2 P) TV = ncfupd.ncfupd E1 E2 (P TV).
  Proof. rewrite ncfupd_eq /ncfupd_def. reflexivity. Qed.

  Global Instance elim_modal_bupd_ncfupd p E1 E2 P Q :
    ElimModal True p false (|==> P) P (|NC={E1,E2}=> Q) (|NC={E1,E2}=> Q) | 10.
  Proof.
    rewrite /ElimModal.
    iStartProof (iProp _). iIntros (_ TV).
    rewrite ncfupd_eq.
    monPred_simpl. simpl.
    rewrite bi.intuitionistically_if_elim (bupd_ncfupd E1).
    rewrite ncfupd_frame_r.
    iIntros "H".
    iDestruct (ncfupd.ncfupd_mono with "H") as "H".
    { iIntros "[P i]". iSpecialize ("i" with "[] P"); first done. iApply "i". }
    iApply ncfupd_trans.
    done.
  Qed.

  Lemma ncfupd_frame_r E1 E2 P R:
    (|NC={E1,E2}=> P) ∗ R ⊢ |NC={E1,E2}=> P ∗ R.
  Proof.
    iStartProof (iProp _). iIntros (TV).
    rewrite 2!ncfupd_unfold_at.
    rewrite monPred_at_sep.
    iApply ncfupd_frame_r.
  Qed.

  Lemma ncfupd_trans E1 E2 E3 P : (|NC={E1,E2}=> |NC={E2,E3}=> P) ⊢ |NC={E1,E3}=> P.
  Proof.
    iStartProof (iProp _). iIntros (TV).
    rewrite 3!ncfupd_unfold_at.
    iApply ncfupd_trans.
  Qed.

  Global Instance ncfupd_ne E1 E2 :
    NonExpansive (ncfupd E1 E2).
  Proof. rewrite ncfupd_eq. split. intros TV. solve_proper. Qed.

  Global Instance ncfupd_proper E1 E2 :
    Proper ((≡) ==> (≡)) (ncfupd E1 E2) := ne_proper _.

  Lemma ncfupd_mono E1 E2 P Q : (P ⊢ Q) → (|NC={E1,E2}=> P) ⊢ |NC={E1,E2}=> Q.
  Proof.
    iStartProof (iProp _). iIntros (I TV).
    rewrite 2!ncfupd_unfold_at.
    iApply ncfupd_mono.
    iApply I.
  Qed.

  Global Instance ncfupd_mono' E1 E2 : Proper ((⊢) ==> (⊢)) (ncfupd E1 E2).
  Proof. intros P Q; apply ncfupd_mono. Qed.
  Global Instance ncfupd_flip_mono' E1 E2 :
    Proper (flip (⊢) ==> flip (⊢)) (ncfupd E1 E2).
  Proof. intros P Q; apply ncfupd_mono. Qed.

  Global Instance elim_modal_ncfupd_ncfupd p E1 E2 E3 P Q :
    ElimModal True p false (|NC={E1,E2}=> P) P (|NC={E1,E3}=> Q) (|NC={E2,E3}=> Q).
  Proof.
    rewrite /ElimModal. rewrite bi.intuitionistically_if_elim.
    rewrite ncfupd_frame_r. rewrite bi.wand_elim_r. rewrite ncfupd_trans.
    done.
  Qed.

  Lemma fupd_ncfupd E1 E2 P : (|={E1,E2}=> P) ⊢ |NC={E1,E2}=> P.
  Proof.
    iStartProof (iProp _). iIntros (TV).
    rewrite ncfupd_unfold_at.
    iApply fupd_ncfupd.
  Qed.

  Global Instance elim_modal_fupd_ncfupd p E1 E2 E3 P Q :
    ElimModal True p false (|={E1,E2}=> P) P (|NC={E1,E3}=> Q) (|NC={E2,E3}=> Q).
  Proof.
    rewrite /ElimModal => ?. rewrite (fupd_ncfupd _ _) bi.intuitionistically_if_elim
      ncfupd_frame_r bi.wand_elim_r ncfupd_trans //=.
  Qed.

  (*** cfupd *)

  Lemma cfupd_unfold_at E1 P TV :
    (cfupd E1 P) TV ⊣⊢ cfupd.cfupd E1 (P TV).
  Proof.
    rewrite /cfupd. rewrite /cfupd.cfupd.
    monPred_simpl.
    setoid_rewrite monPred_at_fupd.
    setoid_rewrite monPred_at_embed.
    iSplit.
    - iIntros "H". iApply "H". done.
    - iIntros "H". iIntros (? incl) "C".
      iApply monPred_mono; first apply incl.
      iApply "H". iFrame.
  Qed.

  Global Instance from_modal_cfupd E1 P :
    FromModal True modality_id (cfupd E1 P) (cfupd E1 P) (P).
  Proof.
    rewrite /FromModal /=.
    iIntros (_) "HP _".
    iModIntro. by iFrame.
  Qed.

End lifted_modalities.

(** A few hints. These are declared outside of the section as Coq does not allow
adding global hints inside a section. *)

(** This hint makes [auto] work when the goal is behind a ncfupd modality. *)
Global Hint Extern 1 (environments.envs_entails _ (|NC={_}=> _)) => iModIntro : core.
