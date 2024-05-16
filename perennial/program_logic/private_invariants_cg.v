From stdpp Require Export namespaces.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap frac.
From self.nextgen Require Import nextgen_promises.
From self.nextgen Require Export nextgen_inv_promises.
From Perennial.base_logic.lib Require Export fancy_updates.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Import crash_weakestpre step_fupd_extra.
From Perennial.Helpers Require Import Qextra.
From Perennial.program_logic Require Export private_invariants.
Set Default Proof Using "Type".
Unset Implicit Arguments.
Import uPred.

(** A version of pri_inv that hold for a single generation, and get
    disabled by the nextgen modality *)

Section def.
  Context `{IRISG: !irisGS Λ Σ Ω}.
  Context `{!pri_invG IRISG}.
  Context `{!endisNG Σ Ω}.
  
  Definition pri_cg_inv_def E P : iProp Σ := ∃ γ, pri_inv E ((P ∗ endis_en γ) ∨ endis_dis γ) ∗ endis_en γ.
  Definition pri_cg_inv_aux : seal (@pri_cg_inv_def). Proof. by eexists. Qed.
  Definition pri_cg_inv := pri_cg_inv_aux.(unseal).
  Definition pri_cg_inv_eq : @pri_cg_inv = @pri_cg_inv_def := pri_cg_inv_aux.(seal_eq).
  Typeclasses Opaque pri_cg_inv.

  Global Instance pri_cg_inv_contractive E : Contractive (pri_cg_inv E).
  Proof.
    rewrite pri_cg_inv_eq /pri_cg_inv_def => n ?? Hequiv.
    f_equiv. intros ?. f_equiv. apply pri_inv_contractive.
    split. intros. f_equiv. f_equiv. by apply Hequiv.
  Qed.

End def.

Section pri_inv.
  Context `{IRISG: !irisGS Λ Σ Ω, !generationGS Λ Σ}.
  Context `{PRI: !pri_invG IRISG}.
  Context `{!endisNG Σ Ω}.

  Implicit Types i : positive.
  Implicit Types E : coPset.
  Implicit Types P Q R : iProp Σ.
  Implicit Types Ps Qs Rs : list (iProp Σ).

  Lemma pri_cg_inv_alloc E E1 E2 P : set_infinite E → ▷ P -∗ ||={E1|E2, E1|E2}=> pri_cg_inv E P.
  Proof.
    iIntros (inf) "HP".
    iMod (endis_en_alloc) as (γ) "#Henabled".
    iMod (pri_inv_alloc _ _ _ ((P ∗ endis_en γ) ∨ endis_dis γ) with "[HP] []") as "#Hinv";[eauto|..].
    { iNext. iLeft. iFrame "# ∗". }
    { iClear "Henabled". iModIntro. iIntros "[[HP Hen]|Hdis]".
      - iModIntro. iRight. auto.
      - iModIntro. iRight. auto. }
    iModIntro. rewrite pri_cg_inv_eq. iExists γ.
    iFrame "#".
  Qed.

  Lemma pri_cg_inv_acc E1 E2 E P :
    E ⊆ E2 → pri_cg_inv E P -∗ ||={E1|E2,E1|E2∖E}=> ▷ P ∗ (▷ P -∗ ||={E1|E2∖E,E1|E2}=> True).
  Proof.
    rewrite pri_cg_inv_eq.
    iIntros (Hsub) "[%γ [Hpri #Hen]]".
    iMod (pri_inv_acc with "Hpri") as "[[[HP _]|>Hdis] Hcls]";[auto|..].
    - iModIntro. iFrame.
      iIntros "HP".
      iMod ("Hcls" with "[HP]");[|auto].
      iNext. iLeft. iFrame "∗ #".
    - by iDestruct (endis_en_shot_False with "[$] [$]") as "F".
  Qed.

  Global Instance pri_cg_inv_persistent E P : Persistent (pri_cg_inv E P).
  Proof. rewrite pri_cg_inv_eq. apply _. Qed.

End pri_inv.




