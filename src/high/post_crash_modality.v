From iris.algebra Require Import auth.
From self.base Require Import primitive_laws.
From self.base Require post_crash_modality.
From self.high Require Import dprop weakestpre.

Set Default Proof Using "Type".

Notation base_post_crash := post_crash_modality.post_crash.

Definition know_history_post_crash {Σ}
            (hG : nvmG Σ) ℓ (hist : gmap time st) : iProp Σ :=
  (∃ t state,
    ⌜hist !! t = Some state⌝ ∗
    know_full_encoded_history_loc ℓ ({[ 0 := state ]}) ∗
    recovered {[ ℓ := MaxNat t ]}) ∨
  (∀ t, ¬ (recovered {[ ℓ := MaxNat t ]})).

(** This map is used to exchange [know_full_history_loc] valid prior to a crash
into a version valid after the crash. *)
Definition post_crash_map {Σ} (hh : gmap loc (gmap time st)) (hG hG' : nvmG Σ) : iProp Σ :=
  (* Used to conclude that the locations owned are included in the heap in question. *)
  (∀ ℓ hist, (know_full_encoded_history_loc (hG := hG) ℓ hist) -∗ ⌜hh !! ℓ = Some hist⌝) ∗
  (* The map used to the the exchange. *)
  [∗ map] ℓ ↦ hist ∈ hh,
    (know_full_encoded_history_loc (hG := hG) ℓ hist) ∨ (know_history_post_crash hG' ℓ hist).

Program Definition post_crash {Σ} (P : nvmG Σ → dProp Σ) `{hG : !nvmG Σ} : dProp Σ :=
  MonPred (λ TV,
    ∀ (hhG' : nvmHighG Σ) hh,
      base_post_crash (λ hG',
        (post_crash_map hh hG (NvmG _ hG' hhG')) -∗ P (NvmG _ hG' hhG') (∅, ∅, ∅)
                                    ∗ (post_crash_map hh hG (NvmG _ hG' hhG'))))%I
    _.
(* Next Obligation. solve_proper. Qed. *)

Section post_crash_prop.
  Context `{hG: !nvmG Σ}.

  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types efs : list thread_state.
  Implicit Types σ : mem_config.
  Implicit Types v : thread_val.

  (** Tiny shortcut for introducing the assumption for a [post_crash]. *)
  Ltac iIntrosPostCrash := iIntros (hG' hh).

  (* Lemma post_crash_intro Q: *)
  (*   (⊢ Q) → *)
  (*   (⊢ post_crash (λ _, Q)). *)
  (* Proof. *)
  (*   iStartProof (iProp _). iIntros (TV'). *)
  (*   iIntros (Hmono). *)
  (*   iIntrosPostCrash. *)
  (*   iFrame "∗". *)
  (*   iApply Hmono. *)
  (* Qed. *)

  Lemma post_crash_mono P Q:
    (∀ hG, P hG -∗ Q hG) →
    post_crash P -∗ post_crash Q.
  Proof.
    iStartProof (iProp _). iIntros (Hmono TV') "HP".
    iIntrosPostCrash.
    iDestruct ("HP" $! hG') as "P".
    iApply (post_crash_modality.post_crash_mono with "P").
    iIntros (hG2).
    iIntros "P M".
    iDestruct ("P" with "M") as "[P $]".
    iDestruct (Hmono with "P") as "H".
    done.
  Qed.

  Lemma post_crash_know_full_history_loc `{Countable ST} ℓ (abs_hist : abs_history ST) :
    ⎡know_full_history_loc ℓ abs_hist⎤ -∗
    post_crash (λ hG',
      (∃ (t : time) (state : ST),
        ⌜abs_hist !! t = Some state⌝ ∗
        ⎡recovered {[ ℓ := MaxNat t ]}⎤ ∗
        ⎡know_full_history_loc ℓ {[ 0 := state ]}⎤) ∨
      (∀ t, ⎡¬ (recovered {[ ℓ := MaxNat t ]})⎤)).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_intro with "HP") as "HP".
    post_crash_modality.iCrash.
    iIntros "[in M]".
    rewrite know_full_equiv.
    iAssert (⌜hh !! _ = Some _⌝)%I as %HI.
    { iApply ("in" with "HP"). }
    iDestruct (big_sepM_lookup_acc with "M") as "[[H|H] reIns]"; first done.
    { iDestruct (own_valid_2 with "HP H") as %V.
      rewrite -auth_frag_op in V.
      apply auth_frag_valid_1 in V.
      rewrite singleton_op in V.
      apply singleton_valid in V.
      apply auth_auth_op_valid in V.
      done. }
    iDestruct ("reIns" with "[$HP]") as "$".
    iFrame "in".
    iDestruct "H" as "[H|H]"; [iLeft|iRight; iFrame].
    iDestruct "H" as (t estate) "(%look & hist & rec)".
    apply lookup_fmap_Some in look as [st [eq yo]].
    iExists t, st.
    iFrame "rec".
    iSplit; first done.
    rewrite know_full_equiv.
    rewrite -eq.
    rewrite map_fmap_singleton.
    iFrame.
  Qed.

End post_crash_prop.
