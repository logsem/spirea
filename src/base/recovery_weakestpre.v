(* This is the recovery weakestpre from Perennial updated to use the nextgen
 * modality. *)

From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang crash_weakestpre.
Import uPred.

From self.nextgen Require Import nextgen_promises.

Set Default Proof Using "Type".

(*** Recovery ***)

(* A recovery WP is parameterized by three predicates: [Φ] is the postcondition
   for normal non-crashing execution, [Φinv] is a condition that holds at each restart
   point, and [Φr] is the postcondition satisfied in case of a crash.

   Compared to the [wpr] in Perennial, in this variant [generationGS] is a
   fixed argument, not one that changes on each crash, as generations are
   handled by the nextgen modality.

   We don't support the [NC] token in a meaningful way, and only demand a
   [generationGS] as the Perennial program logic needs such an instance. The
   [NC] token is a single-shot camera that reserts at every crash. We could
   easily support such a thing with the nextgen modality, but we would have to
   make more changes to Perennial's program logic, and we don't use the token
   for anything anyway. *)
Definition wpr_pre {Σ} {Ω : gGenCmras Σ} `{irisGS Λ Σ, generationGS Λ Σ}
    (CS : crash_semantics Λ) (s : stuckness)
    (wpr : coPset -d> expr Λ -d> expr Λ -d>
                     (val Λ -d> iPropO Σ) -d>
                     (iPropO Σ) -d>
                     (val Λ -d> iPropO Σ) -d> iPropO Σ) :
  coPset -d> expr Λ -d> expr Λ -d>
  (val Λ -d> iPropO Σ) -d>
  (iPropO Σ) -d>
  (val Λ -d> iPropO Σ) -d>
  iPropO Σ :=
  λ E e rec Φ Φinv Φr,
  (WPC e @ s ; E
     {{ Φ }}
     {{ ∀ σ g mj D σ' (HC : crash_prim_step CS σ σ') ns κs n,
        state_interp σ n -∗ global_state_interp g ns mj D κs ={E}=∗ ▷
          ⚡==> (* this is where we want the post crash modality *)
         |={E}=>
          (* NC 1 ∗ *) (* Here you would get an [NC] token but we don't care. *)
          state_interp σ' 0 ∗
          global_state_interp g (step_count_next ns) mj D κs ∗
          (Φinv ∧ wpr E rec rec Φr Φinv Φr) }})%I.

Local Instance wpr_pre_contractive {Σ} {Ω : gGenCmras Σ} `{!irisGS Λ Σ, generationGS Λ Σ} CS s :
  Contractive (wpr_pre CS s).
Proof.
  rewrite /wpr_pre=> n wp wp' Hwp E1 e1 rec Φ Φinv Φc.
  apply wpc_ne; eauto;
  repeat (f_contractive || f_equiv). apply Hwp.
Qed.

Definition wpr_def {Σ} {Ω : gGenCmras Σ} `{!irisGS Λ Σ, generationGS Λ Σ} CS (s : stuckness) :
  coPset → expr Λ → expr Λ →
  (val Λ → iProp Σ) →
  (iProp Σ) →
  (val Λ → iProp Σ) → iProp Σ := fixpoint (wpr_pre CS s).
Definition wpr_aux {Σ} {Ω : gGenCmras Σ} `{!irisGS Λ Σ, generationGS Λ Σ} : seal (@wpr_def Σ _ Λ _ _).
Proof. by eexists. Qed.
Definition wpr {Σ} {Ω : gGenCmras Σ} `{!irisGS Λ Σ, generationGS Λ Σ} := wpr_aux.(unseal).
Definition wpr_eq {Σ} {Ω : gGenCmras Σ} `{!irisGS Λ Σ, generationGS Λ Σ} :
  wpr = @wpr_def Σ _ Λ _ _ := wpr_aux.(seal_eq).

(* Make [generationGS] implicit.
Arguments wpr {Λ Σ _} _ _ _ {_}. *)

Lemma wpr_unfold {Σ} {Ω : gGenCmras Σ} `{!irisGS Λ Σ, generationGS Λ Σ}
    CS s E e rec Φ Φinv Φc :
  wpr CS s E e rec Φ Φinv Φc ⊣⊢ wpr_pre CS s (wpr CS s) E e rec Φ Φinv Φc.
Proof. rewrite wpr_eq. apply (fixpoint_unfold (wpr_pre _ s)). Qed.

Section wpr.
  Context {Σ} {Ω : gGenCmras Σ} `{!irisGS Λ Σ, generationGS Λ Σ}.
  Implicit Types CS : crash_semantics Λ.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types Φc : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  (* About löb_wand_intuitionistically. *)

  Lemma löb_wand_plainly P : ■ (■ ▷ P -∗ P) ⊢ P.
  Proof.
    rewrite -{3}(plainly_elim P).
    rewrite -(löb (■ P)). apply impl_intro_l.
    rewrite later_plainly.
    rewrite plainly_and_sep_l.
    iIntros "[#A #B]".
    iModIntro.
    iApply "B".
    done.
  Qed.

  (* There's a stronger version of this *)
  Lemma wpr_strong_mono CS s E e rec Φ Ψ Φinv Ψinv Φr Ψr :
    wpr CS s E e rec Φ Φinv Φr -∗
    ■ ((∀ v, Φ v ==∗ Ψ v) ∧ (Φinv -∗ Ψinv) ∧ (∀ v, Φr v ==∗ Ψr v)) -∗
    wpr CS s E e rec Ψ Ψinv Ψr.
  Proof.
    iRevert (e E Φ Ψ Φinv Ψinv Φr Ψr).
    iApply löb_wand_plainly.
    iIntros "!> IH". iIntros (e E Φ Ψ Φinv Ψinv Φr Ψr) "H #HΦ".
    (* iLöb as "IH" forall (e E Φ Ψ Φinv Ψinv Φr Ψr). *)
    rewrite (wpr_unfold CS s E e rec Ψ Ψinv Ψr).
    rewrite wpr_unfold /wpr_pre.
    iApply (wpc_strong_mono' with "H") ; auto.
    iSplit.
    { iDestruct "HΦ" as "(H&_)". iIntros. iMod ("H" with "[$]"); eauto. }
    iDestruct "HΦ" as "(_&HΦ)".
    iIntros "H".
    iModIntro. iIntros (?????????) "Hσ Hg". iMod ("H" with "[//] Hσ Hg") as "H".
    iModIntro. iNext.
    iModIntro.
    iMod "H" as "H".
    iModIntro.
    iDestruct "H" as "(?&?&H)".
    iFrame.
    iSplit.
    - iDestruct "H" as "(H&_)". iDestruct "HΦ" as "(HΦ&_)". by iApply "HΦ".
    - iDestruct "H" as "(_&H)".
      iApply ("IH" with "[$]").
      iModIntro.
      iSplit; last by auto.
      iIntros. iDestruct ("HΦ") as "(_ & H)"; by iMod ("H" with "[$]").
  Qed.

  (* To prove a recovery wp for e with rec, it suffices to prove a crash wp for e,
     where the crash condition implies the precondition for a crash wp for rec *)
  Lemma idempotence_wpr CS s E1 e rec Φx Φinv Φrx (Φcx: iProp Σ) :
    ⊢ WPC e @ s ; E1 {{ Φx }} {{ Φcx }} -∗
     (■ ∀ σ g σ' (HC: crash_prim_step CS σ σ') ns mj D κs n,
          Φcx -∗ state_interp σ n -∗ global_state_interp g ns mj D κs ={E1}=∗
          ▷ ⚡==> |={E1}=>
              (* NC 1 ∗ *)
              state_interp σ' 0 ∗ global_state_interp g (step_count_next ns) mj D κs ∗
              (Φinv ∧ WPC rec @ s ; E1 {{ Φrx }} {{ Φcx }})) -∗
      wpr CS s E1 e rec (Φx) Φinv Φrx.
  Proof.
    iRevert (E1 e Φx).
    iApply löb_wand_plainly.
    iIntros "!> #IH". iIntros (E1 e Φx) "He #Hidemp".
    (* iLöb as "IH" forall (E1 e Φx). *)
    (* iIntros  "He #Hidemp". *)
    (* rewrite (wpr_unfold CS s E1 e rec Ψ Ψinv Ψr). *)
    rewrite wpr_unfold. rewrite /wpr_pre.
    iApply (wpc_strong_mono' with "He"); [ by auto | by auto | ].
    iSplit; first auto. iIntros "Hcx".
    iApply @fupd_mask_intro_discard.
    { set_solver +. }
    iIntros. iMod ("Hidemp" with "[ ] [$] [$] [$]") as "H".
    { eauto. }
    iModIntro. iNext. iModIntro.
    iMod "H" as "H".
    iModIntro.
    iDestruct "H" as "(?&?&Hc)".
    iFrame.
    iSplit.
    { iDestruct "Hc" as "($&_)". }
    iDestruct "Hc" as "(_&Hc)".
    iApply ("IH" $! E1 rec (λ v, Φrx v)%I with "[Hc]").
    { iApply (wpc_strong_mono' with "Hc"); auto. }
    eauto.
  Qed.

End wpr.

(* NOTE: Perennial's [recovery_weakestpre.v] also defines a [wpr0], but I have
 * no idea what that is for, so it is not reproduced here. *)
