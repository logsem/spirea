(** Here we "lift" the various modalities in Perennial from [iProp] to
[dProp]. This is mostly just boilerplate. *)

From iris.bi Require Import derived_laws.
From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic.lib Require Import ncfupd.
From Perennial.program_logic Require Import crash_weakestpre.

From self.high Require Import dprop monpred_simpl.

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

Section lifted_fupd_level.
  Context `{!invG Σ}.

  (*** fupd_level*)

  Global Instance except_0_fupd_level' E1 E2 k P :
    IsExcept0 (|k={E1,E2}=> P).
  Proof. Admitted. (* by rewrite /IsExcept0 except_0_fupd_level. Qed. *)

  Global Instance from_modal_fupd_level E k P :
    FromModal modality_id (|k={E}=> P) (|k={E}=> P) P.
  Proof. Admitted. (* by rewrite /FromModal /= -fupd_level_intro. Qed. *)

  Global Instance elim_modal_bupd_fupd_level p E1 E2 k P Q :
    ElimModal True p false (|==> P) P (|k={E1,E2}=> Q) (|k={E1,E2}=> Q) | 10.
  Proof. Admitted.
  (*   by rewrite /ElimModal intuitionistically_if_elim *)
  (*     (bupd_fupd_level E1 k) fupd_level_frame_r wand_elim_r fupd_level_trans. *)
  (* Qed. *)
  Global Instance elim_modal_fupd_level_fupd_level p E1 E2 E3 k P Q :
    ElimModal True p false (|k={E1,E2}=> P) P (|k={E1,E3}=> Q) (|k={E2,E3}=> Q).
  Proof. Admitted.
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

  Lemma fupd_level_unfold_at E1 E2 k P TV :
    (uPred_fupd_level E1 E2 k P) TV = fupd_level.uPred_fupd_level E1 E2 k (P TV).
  Proof.
    rewrite uPred_fupd_level_eq.
    rewrite /uPred_fupd_level_def.
    rewrite fupd_level.uPred_fupd_level_eq.
    apply fupd_split_level_unfold_at.
  Qed.

End lifted_fupd_level.

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

Program Definition cfupd `{!invG Σ, !crashG Σ} (k: nat) E1 (P : dProp Σ) :=
  (⎡C⎤ -∗ |k={E1}=> P)%I.
  (* MonPred (λ TV, cfupd k E1 (P TV))%I _. *)
(* Next Obligation. solve_proper. Qed. *)

Notation "|C={ E1 }_ k => P" := (cfupd k E1 P)
      (at level 99, E1 at level 50, P at level 200,
      format "|C={ E1 }_ k =>  P").

(*** own_discrete *)
Section lifted_own_discrete.
  Context {Σ : gFunctors}.

  Program Definition own_discrete_def (P : dProp Σ) :=
    MonPred (λ TV, own_discrete (P TV)) _ .
  Next Obligation. solve_proper. Qed.
  Definition own_discrete_aux : seal own_discrete_def. Proof. by eexists. Qed.
  Definition own_discrete := own_discrete_aux.(unseal).
  Definition own_discrete_eq  : own_discrete = own_discrete_def :=
    own_discrete_aux.(seal_eq).
  Arguments own_discrete _%I.

  Lemma own_discrete_elim Q :
    own_discrete Q -∗ Q.
  Proof.
    rewrite own_discrete_eq.
    iStartProof (iProp _). iIntros (tv).
    iApply own_discrete_elim.
  Qed.

  Lemma own_discrete_sep P Q : own_discrete P ∗ own_discrete Q ⊢ own_discrete (P ∗ Q).
  Proof.
    rewrite own_discrete_eq.
    iStartProof (iProp _). iIntros (tv).
    simpl.
    rewrite monPred_at_sep.
    iApply own_discrete_sep.
  Qed.

  Lemma own_discrete_wand Q1 Q2:
    □ (Q1 -∗ Q2) -∗ (own_discrete Q1 -∗ own_discrete Q2).
  Proof.
    rewrite own_discrete_eq.
    iStartProof (iProp _). iIntros (tv).
    simpl.
    rewrite !monPred_at_wand.
    iIntros "#W".
    iIntros (tv' incl).
    iSpecialize ("W" $! tv' incl).
    iApply own_discrete_wand.
    done.
  Qed.

  Class Discretizable (P : dProp Σ) := discretizable : P -∗ own_discrete P.
  Arguments Discretizable _%I : simpl never.
  Arguments discretizable _%I {_}.
  Hint Mode Discretizable ! : typeclass_instances.

  Class IntoDiscrete (P Q : dProp Σ) :=
    into_discrete : P ⊢ own_discrete Q.
  Arguments IntoDiscrete _%I _%I.
  Arguments into_discrete _%I _%I.
  Hint Mode IntoDiscrete ! - : typeclass_instances.

  Global Instance Discretizable_proper : Proper ((≡) ==> iff) Discretizable.
  Proof.
  Abort. (* Seem like something that _should_ be easy with [solve_proper]. *)
    (* rewrite /Discretizable. *)
    (* rewrite own_discrete_eq. *)
    (* rewrite /own_discrete_def. *)
    (* simpl. *)
    (* rewrite /Proper. *)
    (* intros P P' eq. *)
    (* split. *)
    (* - iStartProof (iProp _). iIntros (i H) "P". iApply i. rewrite -eq. *)
    (* solve_proper. Qed. *)

  Global Instance sep_discretizable P Q:
    Discretizable P →
    Discretizable Q →
    Discretizable (P ∗ Q).
  Proof.
    rewrite /Discretizable.
    iStartProof (iProp _). iIntros (Pd Qd tv) "(P & Q)".
    iApply own_discrete_sep.
    iPoseProof (Pd with "[$]") as "$".
    iPoseProof (Qd with "[$]") as "$".
  Qed.

  Global Instance exist_discretizable {A} (Φ : A → dProp Σ):
    (∀ x, Discretizable (Φ x)) → Discretizable (∃ x, Φ x).
  Proof.
    rewrite /Discretizable.
    iIntros (HΦ) "HΦ".
    iDestruct "HΦ" as (x) "Hx".
    iPoseProof (HΦ with "[$]") as "Hx".
    iApply (own_discrete_wand with "[] Hx").
    iModIntro. eauto.
  Qed.

  Global Instance or_discretizable P Q:
    Discretizable P →
    Discretizable Q →
    Discretizable (P ∨ Q).
  Proof.
    rewrite /Discretizable.
  Abort. (* Prove this later if we need it. *)
  (*   iIntros (HPd HQd) "[HP|HQ]". *)
  (*   - iApply own_discrete_or_l. *)
  (*     iApply (HPd with "HP"). *)
  (*   - iApply own_discrete_or_r. *)
  (*     iApply (HQd with "HQ"). *)
  (* Qed. *)

  (* Global Instance ownM_discretizable (a : M): *)
  (*   Discrete a → *)
  (*   Discretizable (uPred_ownM a). *)
  (* Proof. intros ?. by apply own_discrete_ownM. Qed. *)

  (* Global Instance discretizable_into_discrete (P: uPred M): *)
  (*   Discretizable P → *)
  (*   IntoDiscrete P P. *)
  (* Proof. rewrite /Discretizable/IntoDiscrete//=. Qed. *)

  (* Global Instance own_discrete_into_discrete (P: uPred M): *)
  (*   IntoDiscrete (own_discrete P) P. *)
  (* Proof. rewrite /Discretizable/IntoDiscrete//=. Qed. *)

  Global Instance monPred_discretizable (P : thread_view → iProp Σ) prf :
    (∀ i, own_discrete.Discretizable (P i)) →
    Discretizable ({| monPred_at := P; monPred_mono := prf |}).
  Proof.
    rewrite /Discretizable own_discrete_eq.
    iStartProof (iProp _). iIntros (Hd ?).
    simpl.
    unfold own_discrete.Discretizable in Hd.
    iApply Hd.
  Qed.

  Global Instance embed_discretizable (P : iProp Σ) :
    own_discrete.Discretizable P → Discretizable ⎡P⎤.
  Proof. rewrite monPred_embed_eq. apply _. Qed.

  Global Instance persistent_discretizable (P : dProp Σ) :
    Persistent P → Discretizable P.
  Proof.
    rewrite /Discretizable.
    rewrite own_discrete_eq.
    iStartProof (iProp _). iIntros (pers tv) "#P".
    iModIntro.
    iApply "P".
  Qed.

  Global Instance discretizable_into_discrete (P : dProp Σ):
    Discretizable P → IntoDiscrete P P.
  Proof. rewrite /Discretizable. rewrite /IntoDiscrete. done. Qed.

End lifted_own_discrete.

Notation "'<bdisc>' P" := (own_discrete P) (at level 20, right associativity) : bi_scope.

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
    (ncfupd E1 E2 P) TV = ncfupd.ncfupd E1 E2 (P TV).
  Proof. rewrite ncfupd_eq /ncfupd_def. reflexivity. Qed.

  (*** cfupd *)

  Lemma cfupd_unfold_at E1 E2 P TV :
    (cfupd E1 E2 P) TV ⊣⊢ crash_weakestpre.cfupd E1 E2 (P TV).
  Proof.
    rewrite /cfupd. rewrite /crash_weakestpre.cfupd.
    (* rewrite monPred_at_wand. *)
    monPred_simpl.
    setoid_rewrite fupd_level_unfold_at.
    setoid_rewrite monPred_at_embed.
    iSplit.
    - iIntros "H". iApply "H". done.
    - iIntros "H". iIntros (? incl) "C".
      iApply monPred_mono; first apply incl.
      iApply "H". iFrame.
  Qed.

  Global Instance from_modal_cfupd k E1 P :
    FromModal modality_id (cfupd k E1 P) (cfupd k E1 P) (P).
  Proof.
    rewrite /FromModal /=.
    iIntros "HP".
    iIntros "_".
    iModIntro. by iFrame.
    (* rewrite /FromModal /=. *)
    (* iStartProof (iProp _). iIntros (TV). *)
    (* iIntros "P". *)
    (* iIntros "_". *)
    (* iModIntro. iFrame. *)
  Qed.

  (*** <disc> *)

  Class IntoDiscreteFupd `{!invG Σ} (P Q : dProp Σ) :=
    into_discrete_fupd : P ⊢ own_discrete_fupd Q.
  Arguments IntoDiscreteFupd {_} _%I _%I.
  Arguments into_discrete_fupd {_} _%I _%I {_}.
  Hint Mode IntoDiscreteFupd + ! - : typeclass_instances.

  (* Global Instance own_discrete_into_discrete_fupd P: *)
  (*   IntoDiscreteFupd (own_discrete P) P. *)
  (* Proof. rewrite /IntoDiscreteFupd//=. apply own_disc_own_disc_fupd. Qed. *)

  (* Global Instance from_pure_own_discrete a P φ : *)
  (*   FromPure a P φ → FromPure a (<disc> P) φ. *)
  (* Proof. *)
  (*   rewrite /FromPure=> <-. destruct a; simpl; iIntros (?); iModIntro; done. *)
  (* Qed. *)

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

  Lemma own_disc_own_disc_fupd (P : dProp Σ) : <bdisc> P -∗ <disc> P.
  Proof.
    rewrite own_discrete_fupd_eq. rewrite /own_discrete_fupd_def.
    rewrite own_discrete_eq. rewrite /own_discrete_def.
    iStartProof (iProp _). iIntros (tv).
    iApply own_disc_own_disc_fupd.
  Qed.

  Global Instance own_discrete_fupd_into_discrete_fupd P:
    IntoDiscreteFupd (own_discrete_fupd P) P.
  Proof. rewrite /IntoDiscreteFupd. done. Qed.

  Global Instance own_discrete_into_discrete_fupd P:
    IntoDiscreteFupd (own_discrete P) P.
  Proof. rewrite /IntoDiscreteFupd. simpl. apply own_disc_own_disc_fupd. Qed.

  Global Instance into_discrete_into_discrete_fupd P P':
    IntoDiscrete P P' →
    IntoDiscreteFupd P P'.
  Proof.
    (* rewrite /Discretizable/IntoDiscreteFupd. *)
    rewrite /Discretizable. rewrite /IntoDiscreteFupd.
    iIntros (?) "HP". rewrite (@into_discrete _ P). iModIntro. auto.
  Qed.

End lifted_modalities.

(** A few hints. These are declared outside of the section as Coq does not allow
adding global hints inside a section. *)

(** This hint makes [auto] work when the goal is behind a ncfupd modality. *)
Global Hint Extern 1 (environments.envs_entails _ (|NC={_}=> _)) => iModIntro : core.

Global Hint Extern 1 (environments.envs_entails _ (<disc> _)) => iModIntro : core.
