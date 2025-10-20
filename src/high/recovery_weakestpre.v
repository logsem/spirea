(* Implementation of the recovery weakest precondition for NVMLang. *)

From Coq Require Import QArith Qcanon.

From stdpp Require Import sets.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris_named_props Require Import named_props.
From self.program_logic Require Import crash_weakestpre recovery_weakestpre recovery_adequacy.

From self.high Require Import dprop generational_resources wrappers protocol.
From self Require Import view map_extra extra ipm_tactics if_non_zero view_slice solve_view_le.
From self.base Require Import primitive_laws wpr_lifting.
From self.high Require Import generational_resources crash_weakestpre.
From self.high.modalities Require Import or_lost nextgen.
From self.nextgen Require Import nextgen_promises.

Set Default Proof Using "Type*".
(* (*** Recovery ***) *)

(* (* A recovery WP is parameterized by three predicates: [Φ] is the postcondition *)
(*    for normal non-crashing execution, [Φinv] is a condition that holds at each restart *)
(*    point, and [Φr] is the postcondition satisfied in case of a crash. *)

(*    Compared to the [wpr] in Perennial, in this variant [generationGS] is a *)
(*    fixed argument, not one that changes on each crash, as generations are *)
(*    handled by the nextgen modality. *)

(*    We don't support the [NC] token in a meaningful way, and only demand a *)
(*    [generationGS] as the Perennial program logic needs such an instance. The *)
(*    [NC] token is a single-shot camera that reserts at every crash. We could *)
(*    easily support such a thing with the nextgen modality, but we would have to *)
(*    make more changes to Perennial's program logic, and we don't use the token *)
(*    for anything anyway. *) *)

(* Definition wpr_pre {Σ Ω} `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ} (s : stuckness) *)
(*     (wpr : coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d> (val -d> dPropO Σ) -d> dPropO Σ) : *)
(*   coPset -d> expr -d> expr -d> *)
(*   (val -d> dPropO Σ) -d> *)
(*   (val -d> dPropO Σ) -d> *)
(*   dPropO Σ := *)
(*   λ E e rec Φ Φr, *)
(*   (WPC e @ s ; E *)
(*      {{ Φ }} *)
(*      {{ ∀ σ g mj D σ' (HC : crash_step σ σ') ns κs n, *)
(*         ⎡ state_interp σ n -∗ global_state_interp g ns mj D κs ={E}=∗ ▷ *)
(*          ⚡==> (* this is where we want the post crash modality *) *)
(*          |={E}=> *)
(*           (* NC 1 ∗ *) (* Here you would get an [NC] token but we don't care. *) *)
(*           state_interp σ' 0 ∗ *)
(*           global_state_interp g (step_count_next ns) mj D κs ∗ *)
(*           validV ∅ ∗ (wpr E rec rec Φr Φr) ⊥ ⎤ }})%I. *)

(* Local Instance wpr_pre_contractive {Σ} {Ω : gGenCmras Σ} `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ} s : *)
(*   Contractive (wpr_pre s). *)
(* Proof. *)
(*   rewrite /wpr_pre=> n wp wp' Hwp E1 e1 rec Φ Φr. *)
(*   apply wpc_ne; eauto; *)
(*   repeat (f_contractive || f_equiv). apply Hwp. *)
(* Qed. *)

(* Definition wpr_def {Σ} {Ω : gGenCmras Σ} `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ} (s : stuckness) : *)
(*   coPset → expr → expr → *)
(*   (val → dProp Σ) → *)
(*   (val → dProp Σ) → dProp Σ := fixpoint (wpr_pre s). *)
(* Definition wpr_aux {Σ} {Ω : gGenCmras Σ} `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ} : seal (@wpr_def Σ Ω _ _ _). *)
(* Proof. by eexists. Qed. *)
(* Definition wpr {Σ} {Ω : gGenCmras Σ} `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ} := wpr_aux.(unseal). *)
(* Definition wpr_eq {Σ} {Ω : gGenCmras Σ} `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ} : *)
(*   wpr = @wpr_def Σ _ _ _ _ := wpr_aux.(seal_eq). *)

(* (* Make [generationGS] implicit. *)
(* Arguments wpr {Λ Σ _} _ _ _ {_}. *) *)

(* Lemma wpr_unfold {Σ} {Ω : gGenCmras Σ} `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ} *)
(*     s E e rec Φ Φc : *)
(*   wpr s E e rec Φ Φc ⊣⊢ wpr_pre s (wpr s) E e rec Φ Φc. *)
(* Proof. rewrite wpr_eq. apply (fixpoint_unfold (wpr_pre s)). Qed. *)

(* Section wpr. *)
(*   Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ}. *)
(*   Implicit Types s : stuckness. *)
(*   Implicit Types P : dProp Σ. *)
(*   Implicit Types Φ : val → dProp Σ. *)
(*   Implicit Types Φc : val → dProp Σ. *)
(*   Implicit Types v : val. *)
(*   Implicit Types e : expr. *)

(*   (* About löb_wand_intuitionistically. *) *)

(*   Lemma löb_wand_plainly P : ■ (■ ▷ P -∗ P) ⊢ P. *)
(*   Proof. *)
(*     rewrite -{3}(plainly_elim P). *)
(*     rewrite -(bi.löb (■ P)%I). apply bi.impl_intro_l. *)
(*     rewrite later_plainly. *)
(*     rewrite plainly_and_sep_l. *)
(*     iIntros "[#A #B]". *)
(*     iModIntro. *)
(*     iApply "B". *)
(*     done. *)
(*   Qed. *)

(*   (* There's a stronger version of this *) *)
(*   Lemma wpr_strong_mono s E e rec Φ Ψ Φr Ψr : *)
(*     wpr s E e rec Φ Φr -∗ *)
(*     ■ ((∀ v, Φ v ==∗ Ψ v) ∧ (∀ v, Φr v ==∗ Ψr v)) -∗ *)
(*     wpr s E e rec Ψ Ψr. *)
(*   Proof. *)
(*     iRevert (e E Φ Ψ Φr Ψr). *)
(*     iApply löb_wand_plainly. *)
(*     iIntros "!> IH". iIntros (e E Φ Ψ Φr Ψr) "H #HΦ". *)
(*     (* iLöb as "IH" forall (e E Φ Ψ Φinv Ψinv Φr Ψr). *) *)
(*     rewrite (wpr_unfold s E e rec Ψ Ψr). *)
(*     rewrite wpr_unfold /wpr_pre. *)
(*     iApply (wpc_strong_mono' with "H") ; auto. *)
(*     iSplit. *)
(*     { iDestruct "HΦ" as "(H&_)". iIntros. iMod ("H" with "[$]"); eauto. } *)
(*     iDestruct "HΦ" as "(_&HΦ)". *)
(*     iIntros "H". *)
(*     iModIntro. iIntros (?????????) "Hσ Hg". iMod ("H" with "[//] Hσ Hg") as "H". *)
(*     iModIntro. iModIntro. iNext. *)
(*     iModIntro. *)
(*     iMod "H" as "H". *)
(*     iModIntro. *)
(*     iDestruct "H" as "(?&?&?&H)". *)
(*     iFrame. *)
(*     iApply ("IH" with "[$]"). *)
(*     rewrite monPred_at_plainly. *)
(*     iIntros (j). *)
(*     iSpecialize ("HΦ" $! j). *)
(*     rewrite monPred_at_plainly monPred_at_and. *)
(*     iSpecialize ("HΦ" $! j). *)
(*     iApply (plainly_mono with "HΦ"). *)
(*     iIntros "HΦ". *)
(*     by iSplit. *)
(*   Qed. *)

(*   (* To prove a recovery wp for e with rec, it suffices to prove a crash wp for e, *)
(*      where the crash condition implies the precondition for a crash wp for rec *) *)
(*   Lemma idempotence_wpr s E1 e rec Φx Φrx (Φcx: dProp Σ) `{!Objective Φcx}: *)
(*     ⊢ WPC e @ s ; E1 {{ Φx }} {{ Φcx }} -∗ *)
(*      (<obj> ■ ∀ σ g σ' (HC: crash_step σ σ') ns mj D κs n, *)
(*           Φcx -∗ ⎡ state_interp σ n ⎤ -∗ ⎡ global_state_interp g ns mj D κs ⎤ ={E1}=∗ *)
(*           ▷ <NG> |={E1}=> *)
(*               (* NC 1 ∗ *) *)
(*               ⎡ validV ∅ ⎤ ∗ ⎡ state_interp σ' 0 ⎤ ∗ ⎡ global_state_interp g (step_count_next ns) mj D κs ⎤ ∗ *)
(*               (WPC rec @ s ; E1 {{ Φrx }} {{ Φcx }})) -∗ *)
(*       wpr s E1 e rec (Φx) Φrx. *)
(*   Proof. *)
(*     iRevert (E1 e Φx). *)
(*     iApply löb_wand_plainly. *)
(*     iIntros "!> #IH". iIntros (E1 e Φx) "He #Hidemp". *)
(*     (* iLöb as "IH" forall (E1 e Φx). *) *)
(*     (* iIntros  "He #Hidemp". *) *)
(*     (* rewrite (wpr_unfold CS s E1 e rec Ψ Ψinv Ψr). *) *)
(*     rewrite wpr_unfold. rewrite /wpr_pre. *)
(*     iApply (wpc_strong_mono' with "He"); [ by eauto | by auto | ]. *)
(*     iSplit; first auto. iIntros "Hcx". *)
(*     iApply @fupd_mask_intro_discard. *)
(*     { set_solver +. } *)
(*     iIntros. *)
(*     iIntros "interp global". *)
(*     iModIntro. *)
(*     iSpecialize ("Hidemp" $! ⊥). *)
(*     iSpecialize ("Hcx" $! ⊥). *)
(*     rewrite monPred_objectively_elim monPred_at_plainly. *)
(*     iMod ("Hidemp" with "[ ] [$] [$] [$]") as "H". *)
(*     { eauto. } *)
(*     iModIntro. iNext. *)
(*     iEval (rewrite /nextgen.nextgen /=) in "H". *)
(*     iModIntro. *)
(*     iMod ("H") as "H". *)
(*     iModIntro. *)
(*     iDestruct "H" as "(?&?&?&Hc)". *)
(*     iFrame. *)
(*     iSpecialize ("IH" $! ⊥). *)
(*     rewrite monPred_at_plainly. *)
(*     iSpecialize ("IH" $! ⊥). *)
(*     iApply ("IH" $! E1 rec (λ v, Φrx v)%I with "Hc"). *)
(*     iApply monPred_at_objectively. *)
(*     iIntros (j). *)
(*     rewrite monPred_at_plainly. *)
(*     iIntros (j'). *)
(*     iSpecialize ("Hidemp" $! j'). *)
(*     done. *)
(*     Unshelve. all: refine (∅, ∅, ∅). *)
(*   Qed. *)
(* End wpr. *)

Section wpr.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ}.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val → dProp Σ.
  Implicit Types Φc : dProp Σ.
  Implicit Types v : thread_val.
  Implicit Types e : thread_state.

  Lemma extra_state_nextgen: ∀ CV σ1 σ2,
    CV_crash_step CV σ1 σ2 →
    extra_state_interp -∗
    (∃ OCV, crashed_at_offset OCV ∗ picked_out crashed_at_name (crashed_at_trans (OCV `view_add` CV))) -∗
    |==> ▷ ⚡==> |==> extra_state_interp.
  Admitted.
  
  Lemma idempotence_wpr
      s E1 e e_rec Φ Φinv Φr Φc :
    ⊢ validV (store_view e.(ts_view)) -∗
    (WPC e.(ts_expr) @ s; E1 {{ Φ }} {{ Φc }}) e.(ts_view)-∗
    (* TODO: have an expert double check this modality *)
    ■ ((Φc -∗ ▷ <NG> (⎡ Φinv ⎤ ∧ WPC e_rec @ s ; E1 {{ Φr }} {{ Φc }})) ⊥) -∗
      wpr s E1 e (e_rec `at` ⊥) (λ v, Φ v.(val_val) v.(val_view)) Φinv (λ v, Φr v.(val_val) v.(val_view)).
  Proof.
    iIntros "#validV Hwpc #Hidemp".
    iApply (idempotence_wpr extra_state_nextgen s E1 e (e_rec `at` ⊥) _ _ _ (Φc ⊥)
                            with "[Hwpc] [Hidemp]").
    { iClear "Hidemp".
      rewrite wpc_eq /wpc_def /wpc /=.
      iSpecialize ("Hwpc" $! (e.(ts_view)) with "[//] [$]").
      destruct e.
      simpl.
      (* Set Printing All. *)
      iApply (program_logic.crash_weakestpre.wpc_mono' with "[] [] Hwpc").
      { iIntros ([v TV']) "(% & _ & $)". }
      { iIntros. iAccu. } }
    (* { iApply (wpc_crash_mono with "[] Hwpc"). *)
    (*   iIntros "HΦcx". iExists _. destruct nG. by iFrame. } *)
    iApply (plainly_mono with "[$]").
    iIntros "Hidemp Φc".
    iSpecialize ("Hidemp" with "Φc").
    iModIntro.
    rewrite /nextgen.nextgen /=.
    iIntros "!> validV".
    rewrite monPred_at_and monPred_at_embed.
    iSplit; first iDestruct "Hidemp" as "[$ _]".
    iDestruct "Hidemp"as "[_ Hwpc]".
    rewrite wpc_eq /wpc_def /wpc /=.

    iSpecialize ("Hwpc" $! ⊥ with "[//] [$]").
    iApply (program_logic.crash_weakestpre.wpc_mono' with "[] [] Hwpc").
    { iIntros ([v TV']) "(_ & _ & $)". }
    { iIntros. iAccu. }
  Qed.
End wpr.
