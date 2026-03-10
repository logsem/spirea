From stdpp Require Import numbers.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth dfrac.
(* From Perennial.base_logic.lib Require Import proph_map. *)
(* From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy. *)
From self.program_logic Require Import recovery_weakestpre recovery_adequacy.

From self.nextgen Require Import omega.
From self Require Import extra map_extra ipm_tactics if_non_zero view_slice.
From self.lang Require Import lang.
From self.base Require Import generational_resources primitive_laws.
From self.nextgen Require Import nextgen_promises.

Set Default Proof Using "Type*".

Definition wpr `{!nvmBaseGS Σ Ω, !extraStateInterp Σ, !PerennialG Σ}
           (s : stuckness) (E : coPset)
           (e : thread_state) (recv : thread_state) (Φ : thread_val → iProp Σ)
           (Φinv : iProp Σ)
           (Φr : thread_val → iProp Σ) :=
  wpr
    nvm_crash_lang s E e recv Φ
    (Φinv)%I
    (λ v, Φr v)%I.

Section wpr.
  Context `{!nvmBaseGS Σ Ω, !extraStateInterp Σ, !PerennialG Σ}.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types Φc : iProp Σ.
  Implicit Types v : thread_val.
  Implicit Types e : thread_state.

  Lemma wpr_strong_mono
        s E e rec Φ Ψ Φinv Ψinv Φr Ψr :
    wpr s E e rec Φ Φinv Φr -∗
    (* TODO: what is this modality? *)
    ■ ((∀ v, Φ v ==∗ Ψ v) ∧ ((Φinv -∗ Ψinv) ∧ (∀ v, Φr v ==∗ Ψr v))) -∗
    wpr s E e rec Ψ Ψinv Ψr.
  Proof.
    rewrite /wpr. iIntros "Hwpr Himpl".
    iApply (wpr_strong_mono with "Hwpr [Himpl]").
    repeat iSplit.
    - by iDestruct "Himpl" as "($ & _)".
    - by iDestruct "Himpl" as "(_ & $ & _)".
    - by iDestruct "Himpl" as "(_ & _ & $)".
  Qed.

  Variable (crashed_in_impl: view.view → iProp Σ).
  
  (* Is this the only thing I need to prove for high spirea (other than views of course)? *)
  Hypothesis extra_state_nextgen: ∀ CV σ1 σ2,
    CV_crash_step CV σ1 σ2 →
    extra_state_interp -∗
    (∃ OCV, crashed_at_offset OCV ∗ picked_out crashed_at_name (crashed_at_trans (OCV `view_add` CV))) -∗
    |==> ▷ ⚡==> |==> extra_state_interp ∗ (∃ OCV, crashed_in_impl OCV).

  Lemma idempotence_wpr
      s E1 e e_rec Φ Φinv Φr Φc :
    ⊢ WPC e @ s; E1 {{ Φ }} {{ Φc }} -∗
    (* TODO: have an expert double check this modality *)
    ■ (Φc -∗ ▷ ⚡==> ∀ OCV, crashed_in_impl OCV -∗ validV ∅ -∗ (Φinv ∧ WPC e_rec @ s ; E1 {{ Φr }} {{ Φc }})) -∗
      wpr s E1 e e_rec Φ Φinv Φr.
  Proof.
    iIntros "Hwpc #Hidemp".
    iApply (idempotence_wpr nvm_crash_lang s E1 e e_rec _ _ _ Φc
                            with "[$Hwpc] [Hidemp]").
    (* { iApply (wpc_crash_mono with "[] Hwpc"). *)
    (*   iIntros "HΦcx". iExists _. destruct nG. by iFrame. } *)
    iApply (plainly_mono with "[$]").
    iIntros "Hidemp" (σ_pre_crash g σ_post_crash Hcrash ns mj D κs ?) "ϕc".
    (* iMod (NC_alloc_strong) as (γcrash) "HNC". *)
    iIntros "[interp extra] #g".
    iSpecialize ("Hidemp" with "ϕc").
    (* rewrite eq. *)
    (* iMod (nvm_heap_reinit_alt _ _ _ _ γcrash _ Hcrash with "interp Hidemp") *)
    (*   as (hnames) "(%cEq & map & interp' & idemp)". *)
    destruct Hcrash as [CV Hcrash].
    iDestruct (heap_ctx_next_generation _ _ _ Hcrash with "interp") as ">(%OCV & HCV & picked_out & interp)".
    iDestruct (extra_state_nextgen with "extra [picked_out HCV]") as ">extra"; first done.
    { iExists _. iFrame. }
    do 3 iModIntro.
    iDestruct "interp" as ">[persisted interp]".
    iDestruct "extra" as ">[extra impl]".
    iAssert (|==> validV ∅ ∗ nvm_heap_ctx σ_post_crash)%I with "[interp]" as ">[#? interp]".
    { rewrite /nvm_heap_ctx.
      iDestruct "interp" as (???) "[[store_view_auth ?] ?]".
      rewrite /named_props.named.
      iDestruct (gen_own_update with "store_view_auth") as ">[? $]".
      { by apply auth_update_alloc. }
      iModIntro. iExistsN.
      iFrame. }
    iAssert (global_state_interp g (step_count_next ns) mj D κs)%I as "$". { iFrame "#". by iExistsN. }
    (* iMod (global_state_interp_le (Λ := nvm_lang) _ _ () _ _ κs with "[$]") as "$"; *)
    (*   first (rewrite /step_count_next; simpl; lia). *)
    iModIntro.
    rewrite /state_interp //=.
    iFrame.
    iDestruct "impl" as (?) "impl".
    by iApply ("Hidemp" with "impl").
  Qed.
End wpr.
