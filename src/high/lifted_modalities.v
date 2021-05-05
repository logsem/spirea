(** Here we "lift" the various modalities in Perennial from [iProp] to
[dProp]. This is mostly just boilerplate. *)

From iris.bi Require Import derived_laws.
From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic.lib Require Import ncfupd.
From Perennial.program_logic Require Import crash_weakestpre.

From self.high Require Import dprop.

(* fupd_level *)

Program Definition uPred_fupd_split_level_def `{!invG Σ}
           (E1 E2 : coPset) (k : nat) mj (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV, uPred_fupd_split_level_def E1 E2 k mj (P TV))%I _.
Next Obligation. solve_proper. Qed.

Definition uPred_fupd_split_level_aux `{!invG Σ} : seal uPred_fupd_split_level_def.
Proof. by eexists. Qed.
Definition uPred_fupd_split_level `{!invG Σ} := uPred_fupd_split_level_aux.(unseal).
Definition uPred_fupd_split_level_eq `{!invG Σ} :
    uPred_fupd_split_level = uPred_fupd_split_level_def :=
  uPred_fupd_split_level_aux.(seal_eq).

Definition uPred_fupd_level_def `{!invG Σ} (E1 E2 : coPset) (k : nat) (P : dProp Σ) : dProp Σ :=
  uPred_fupd_split_level E1 E2 k None P.
Definition uPred_fupd_level_aux `{!invG Σ} : seal uPred_fupd_level_def.
Proof. by eexists. Qed.
Definition uPred_fupd_level `{!invG Σ} := uPred_fupd_level_aux.(unseal).
Definition uPred_fupd_level_eq `{!invG Σ} : uPred_fupd_level = uPred_fupd_level_def :=
  uPred_fupd_level_aux.(seal_eq).

Notation "| k , j ={ E1 , E2 }=> Q" := (uPred_fupd_split_level E1 E2 k j Q) : bi_scope.
Notation "| k , j ={ E1 }=> Q" := (uPred_fupd_split_level E1 E1 k j Q) : bi_scope.
Notation "| k ={ E1 , E2 }=> Q" := (uPred_fupd_level E1 E2 k Q) : bi_scope.
Notation "| k ={ E1 }=> Q" := (uPred_fupd_level E1 E1 k Q) : bi_scope.

Program Definition ncfupd_def `{!invG Σ, !crashG Σ} (E1 E2 : coPset) (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV, ncfupd E1 E2 (P TV))%I _.
Next Obligation. solve_proper. Qed.
Definition ncfupd_aux `{!invG Σ, !crashG Σ} : seal (ncfupd_def). Proof. by eexists. Qed.
Definition ncfupd `{!invG Σ, !crashG Σ} := ncfupd_aux.(unseal).
Definition ncfupd_eq `{!invG Σ, !crashG Σ} : ncfupd = ncfupd_def := ncfupd_aux.(seal_eq).

Notation "|NC={ E1 }=> Q" := (ncfupd E1 E1 Q)
  (at level 99, E1 at level 50, Q at level 200,
  format "|NC={ E1 }=>  Q") : bi_scope.
Notation "|NC={ E1 , E2 }=> P" := (ncfupd E1 E2 P)
      (at level 99, E1, E2 at level 50, P at level 200,
      format "|NC={ E1 , E2 }=>  P") : bi_scope.
Notation "|NC={ Eo } [ Ei ]▷=> Q" := (∀ q, NC q -∗ |={Eo,Ei}=> ▷ |={Ei,Eo}=> Q ∗ NC q)%I
  (at level 99, Eo, Ei at level 50, Q at level 200,
  format "|NC={ Eo } [ Ei ]▷=>  Q") : bi_scope.
Notation "|NC={ E1 } [ E2 ]▷=>^ n Q" := (Nat.iter n (λ P, |NC={E1}[E2]▷=> P) Q)%I
  (at level 99, E1, E2 at level 50, n at level 9, Q at level 200,
  format "|NC={ E1 } [ E2 ]▷=>^ n  Q").

Program Definition cfupd `{!invG Σ, !crashG Σ}(k: nat) E1 (P : dProp Σ) :=
  MonPred (λ TV, cfupd k E1 (P TV))%I _.
Next Obligation. solve_proper. Qed.

Notation "|C={ E1 }_ k => P" := (cfupd k E1 P)
      (at level 99, E1 at level 50, P at level 200,
      format "|C={ E1 }_ k =>  P").

Program Definition own_discrete_fupd_def `{!invG Σ} (P : dProp Σ) : dProp Σ :=
  MonPred (λ TV, own_discrete_fupd (P TV)) _.
Next Obligation. solve_proper. Qed.
Definition own_discrete_fupd_aux `{!invG Σ} : seal own_discrete_fupd_def.
Proof. by eexists. Qed.
Definition own_discrete_fupd `{!invG Σ} := own_discrete_fupd_aux.(unseal).
Definition own_discrete_fupd_eq `{!invG Σ} : own_discrete_fupd = own_discrete_fupd_def :=
  own_discrete_fupd_aux.(seal_eq).
Arguments own_discrete_fupd {_ _} _%I.

Notation "'<disc>' P" := (own_discrete_fupd P) (at level 20, right associativity) : bi_scope.

Section lifted_modalities.
  Context `{crashG Σ, invG Σ}.

  (*** ncfupd *)

  Global Instance from_modal_ncfupd E P :
    FromModal modality_id (|NC={E}=> P) (|NC={E}=> P) P.
  Proof.
    rewrite /FromModal ncfupd_eq /=. iStartProof (iProp _). iIntros (TV).
    iIntros "$". rewrite ncfupd.ncfupd_eq. iIntros (q) "$". done.
  Qed.

  Global Instance elim_modal_bupd_ncfupd p E1 E2 P Q :
    ElimModal True p false (|==> P) P (|NC={E1,E2}=> Q) (|NC={E1,E2}=> Q) | 10.
  Proof.
    rewrite /ElimModal. rewrite bi.intuitionistically_if_elim.
  Admitted.
  (*   rewrite (bupd_ncfupd E1). ncfupd_frame_r wand_elim_r ncfupd_trans. *)
  (* Qed. *)
  Global Instance elim_modal_ncfupd_ncfupd p E1 E2 E3 P Q :
    ElimModal True p false (|NC={E1,E2}=> P) P (|NC={E1,E3}=> Q) (|NC={E2,E3}=> Q).
  Proof.
  Admitted.
  (*   by rewrite /ElimModal intuitionistically_if_elim *)
  (*     ncfupd_frame_r wand_elim_r ncfupd_trans. *)
  (* Qed. *)

  Global Instance elim_modal_fupd_ncfupd p E1 E2 E3 P Q :
    ElimModal True p false (|={E1,E2}=> P) P (|NC={E1,E3}=> Q) (|NC={E2,E3}=> Q).
  Proof.
    rewrite /ElimModal => ?.
  Admitted.
  (*   rewrite (fupd_ncfupd _ _) intuitionistically_if_elim *)
  (*     ncfupd_frame_r wand_elim_r ncfupd_trans //=. *)
  (* Qed. *)

  Lemma ncfupd_unfold_at E1 E2 P TV :
    (ncfupd E1 E2 P) TV = ncfupd.ncfupd_def E1 E2 (P TV).
  Proof.
    rewrite ncfupd_eq /ncfupd_def. simpl. rewrite ncfupd.ncfupd_eq. reflexivity.
  Qed.

  (*** cfupd *)

  Global Instance from_modal_cfupd k E1 P :
    FromModal modality_id (cfupd k E1 P) (cfupd k E1 P) (P).
  Proof.
    rewrite /FromModal /=.
    iStartProof (iProp _). iIntros (TV).
    iIntros "P".
    iIntros "_".
    iModIntro. iFrame.
  Qed.

  Class IntoDiscreteFupd `{!invG Σ} (P Q : dProp Σ) :=
    into_discrete_fupd : P ⊢ own_discrete_fupd Q.
  Arguments IntoDiscreteFupd {_} _%I _%I.
  Arguments into_discrete_fupd {_} _%I _%I {_}.
  Hint Mode IntoDiscreteFupd + ! - : typeclass_instances.

  Global Instance own_discrete_fupd_into_discrete_fupd P:
    IntoDiscreteFupd (own_discrete_fupd P) P.
  Proof. rewrite /IntoDiscreteFupd//=. Qed.

  (* Global Instance own_discrete_into_discrete_fupd P: *)
  (*   IntoDiscreteFupd (own_discrete P) P. *)
  (* Proof. rewrite /IntoDiscreteFupd//=. apply own_disc_own_disc_fupd. Qed. *)

  (* Global Instance into_discrete_into_discrete_fupd P P': *)
  (*   IntoDiscrete P P' → *)
  (*   IntoDiscreteFupd P P'. *)
  (* Proof. *)
  (*   rewrite /Discretizable/IntoDiscreteFupd//=. *)
  (*   iIntros (?) "HP". rewrite (into_discrete P). iModIntro. auto. *)
  (* Qed. *)

  (* Global Instance from_pure_own_discrete a P φ : *)
  (*   FromPure a P φ → FromPure a (<disc> P) φ. *)
  (* Proof. *)
  (*   rewrite /FromPure=> <-. destruct a; simpl; iIntros (?); iModIntro; done. *)
  (* Qed. *)

  (*** disc *)

  Lemma modality_own_discrete_fupd_mixin :
    modality_mixin (@own_discrete_fupd Σ _)
                   (MIEnvId)
                   (MIEnvTransform (IntoDiscreteFupd)).
  Proof.
    rewrite own_discrete_fupd_eq.
    split; red; iStartProof (iProp _); iIntros (P TV).
    - iIntros. iApply own_disc_own_disc_fupd. iModIntro.
      rewrite monPred_at_intuitionistically. done.
    - iIntros (Hfupd ?). rewrite Hfupd. rewrite own_discrete_fupd_eq. auto.
    - iIntros. iApply own_disc_own_disc_fupd. by iModIntro.
    - iIntros (HH ?) "H /=". rewrite own_discrete.own_discrete_fupd_eq /own_discrete_fupd_def.
      iModIntro. iMod "H". iModIntro. by iApply HH.
    - iIntros (?) "(H1&H2) /=". rewrite own_discrete.own_discrete_fupd_eq /own_discrete_fupd_def.
      iModIntro. iMod "H1". iMod "H2". by iFrame.
  Qed.
  Definition modality_own_discrete_fupd :=
    Modality _ (modality_own_discrete_fupd_mixin).

  Global Instance from_modal_own_discrete_fupd (P : dProp Σ) :
    FromModal modality_own_discrete_fupd (own_discrete_fupd P) (own_discrete_fupd P) P.
  Proof. rewrite /FromModal//=. Qed.
  Lemma disc_unfold_at P TV :
    (own_discrete_fupd P) TV = own_discrete.own_discrete_fupd (P TV).
  Proof.
    rewrite own_discrete_fupd_eq. simpl.
    rewrite own_discrete.own_discrete_fupd_eq. reflexivity.
  Qed.

  Global Instance own_discrete_fupd_ne : NonExpansive own_discrete_fupd.
  Proof.
    rewrite own_discrete_fupd_eq.
    constructor. intros ?. simpl.
    rewrite own_discrete.own_discrete_fupd_eq. solve_proper.
  Qed.
  Global Instance own_discrete_fupd_proper : Proper ((≡) ==> (≡)) own_discrete_fupd := ne_proper _.
  Global Instance own_discrete_fupd_mono' : Proper ((⊢) ==> (⊢)) own_discrete_fupd.
  Proof.
    rewrite own_discrete_fupd_eq. rewrite /own_discrete_fupd_def.
    constructor. intros ?. simpl.
    rewrite own_discrete.own_discrete_fupd_eq. solve_proper.
  Qed.
  Global Instance own_discrete_fupd_flip_mono' :
    Proper (flip (⊢) ==> flip (⊢)) own_discrete_fupd.
  Proof. solve_proper. Qed.

End lifted_modalities.

(** A few hints. These are declared outside of the section as Coq does not allow
adding global hints inside a section. *)

(** This hint makes [auto] work when the goal is behind a ncfupd modality. *)
Global Hint Extern 1 (environments.envs_entails _ (|NC={_}=> _)) => iModIntro : core.

Global Hint Extern 1 (environments.envs_entails _ (<disc> _)) => iModIntro : core.
