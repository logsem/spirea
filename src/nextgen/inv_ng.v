(* Wrappers around Perennials' invariant/fupd resources that survive crashes. *)

From iris.algebra Require Import gmap auth agree gset coPset list vector excl.
From iris.base_logic Require Import lib.later_credits.
From PerennialNG.Helpers Require Import ipm.
From Perennial.algebra Require Import mlist.

From self.nextgen Require Import nextgen_promises_ng.

(** The ghost state for later credits *)
Class ngLcGS (Σ : gFunctors) Ω `{!inG Σ (authR natUR)} := NgLcGS {
  ngLcGS_inG :: ngInG Σ Ω (authR natUR);
}.
Global Hint Mode ngLcGS - - - : typeclass_instances.
Local Existing Instances lcGS_inG lcGpreS_inG.

Section ngInv_lemmas.
  Context `{!lcGS Σ} `{!ngLcGS Σ Ω}.

  Lemma nextgen_lc k : £ k ⊢ ⚡==> £ k.
  Proof using lcGS0 ngLcGS0 Σ Ω.
    iIntros "O".
    rewrite later_credits.lc_unseal /later_credits.lc_def.
    iModIntro.
    done.
  Qed.

  #[global]
    Instance into_nextgen_lc k : IntoNextgen _ _ := nextgen_lc k.

  Lemma nextgen_lc_supply n : later_credits.lc_supply n ⊢ ⚡==> later_credits.lc_supply n.
  Proof using lcGS0 ngLcGS0 Σ Ω.
    iIntros "O".
    rewrite later_credits.lc_supply_unseal /later_credits.lc_supply_def.
    iModIntro. done.
  Qed.

  #[global]
    Instance into_nextgen_lc_supply k : IntoNextgen _ _ := nextgen_lc_supply k.

End ngInv_lemmas.



Class ngFmlistG (A : Type) {Heq: EqDecision A} Σ Ω `{!inG Σ (fmlistUR A)} :=
  { ngFmlist_inG :: ngInG Σ Ω (fmlistUR A) }.

Section ngInv_lemmas.
  Context `{!EqDecision A} `{!fmlistG A Σ} `{!ngFmlistG A Σ Ω}.

  Lemma nextgen_fmlist γ q1 l1 : fmlist γ q1 l1 ⊢ ⚡==> fmlist γ q1 l1.
  Proof using A EqDecision0 fmlistG0 ngFmlistG0 Σ Ω.
    iIntros "O". rewrite /fmlist.
    by iModIntro.
  Qed.

  #[global]
    Instance into_nextgen_fmlist γ q1 l1 : IntoNextgen _ _ := nextgen_fmlist γ q1 l1.

  Lemma nextgen_fmlist_lb γ l2 : fmlist_lb γ l2 ⊢ ⚡==> fmlist_lb γ l2.
  Proof using A EqDecision0 fmlistG0 ngFmlistG0 Σ Ω.
    iIntros "O". rewrite /fmlist_lb.
    by iModIntro.
  Qed.

  #[global]
    Instance into_nextgen_fmlist_lb γ l2 : IntoNextgen _ _ := nextgen_fmlist_lb γ l2.

  Lemma nextgen_fmlist_idx γ i a2 : fmlist_idx γ i a2 ⊢ ⚡==> fmlist_idx γ i a2.
  Proof using A EqDecision0 fmlistG0 ngFmlistG0 Σ Ω.
    rewrite /fmlist_idx. iIntros "(%l & %Heq & O)".
    iModIntro. eauto.
  Qed.

  #[global]
    Instance into_nextgen_fmlist_idx γ i a2 : IntoNextgen _ _ := nextgen_fmlist_idx γ i a2.

End ngInv_lemmas.
