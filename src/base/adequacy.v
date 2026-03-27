(* In this file we show adequacy of the recovery weakest precondition in the
base logic. *)

From iris.proofmode Require Import ltac_tactics.
From iris.algebra Require Import auth.
(* From PerennialNG.base_logic.lib Require Import proph_map. *)
From self.program_logic Require Import recovery_weakestpre recovery_adequacy.
(* From PerennialNG.Helpers Require Import ipm. *)

From self Require Import ipm_tactics.
From self.base Require Import cred_frag.
From self.base Require Import wpr_lifting primitive_laws generational_resources.
From self.nextgen Require Import nextgen_promises.

Set Default Proof Using "Type".

(* I'm still not quite sure what's the proper way to handle these ghost resources,
 * For what I can see,
 * [invGpreS Σ]: the standard Iris invariant resources, which will be solved by [subG] eventually.
 * [ngInvG Σ Ω]: a list of resources created by Aina for invariants across generations. It's not really
 * being used in high-level Spirea, but they are tied in Perennial's adequacy proof so very difficult to remove.
 * [credit_preG Σ]: the resources for a second set of later credits, also not being used at all. *)
Class Perennial_preG Σ Ω := {
  P_invGpreS :> wsat.invGS.invGpreS Σ;
  P_preG_credit :> credit_preG Σ;
  P_ngInvG :> ngInvG Σ Ω;
}.

Definition Build_credit_G Σ `{!Perennial_preG Σ Ω} (cred_names: cr_names): creditGS Σ :=
  creditGS_update_pre Σ P_preG_credit cred_names.

Section base_adequacy.
  Instance empExtraStateInterp {Σ} : extraStateInterp Σ := {
    extra_state_interp := True%I
  }.

  (* The adequacy theorem for the base logic.

  This adequacy theorem makes use of the invariant feature in Perennial (the
  [φinv] and [Φinv]). This makes the statement a bit more complex and we do not
  actually need the invariant feature at all. Hence we also have a simpler
  variant below for the case where the invariant is alwasy true.  *)
  
  Theorem base_recv_adequacy Σ (Ω: gGenCmras Σ) `{!nvmBaseGpreS Σ Ω, !Perennial_preG Σ Ω}
    s e r σ PV g φ φr φinv Φinv :
    valid_heap σ →
    (∀ `{!nvmBaseGS Σ Ω} `{!PerennialG Σ},
       ⊢
        (* TODO: restore crash borrow after porting the dependencies *)
        (* pre_borrowN n -∗ *)
        ([∗ map] l ↦ v ∈ σ, l ↦fh v) -∗
        validV ∅ -∗
        persisted PV -∗ (
          (* TODO: confirm these modalities *)
          ■ (∀ σ nt, state_interp σ nt -∗ |={⊤,∅}=> ⌜ φinv σ ⌝) ∗
          ■ (Φinv -∗ □ ∀ σ nt, state_interp σ nt -∗ |={⊤,∅}=> ⌜ φinv σ ⌝) ∗
          wpr s ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ v, ⌜φr v⌝))) →
    recv_adequate (CS := nvm_crash_lang) s e r (σ, PV) g (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, φinv σ).
  Proof.
    intros val Hwp.
    eapply (wp_recv_adequacy_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    (* eapply (wp_recv_adequacy_inv _ _ _ nvmBaseDeltaGO _ _ _ _ _ _ _ _ _ _). *)
    iIntros (? ?) "".

    assert (∃ name_credit: cr_names, True) as [name_credit _].
    { by exists (Build_cr_names (xH) (xH)). }
    (* iMod (credit_name_init (crash_borrow_ginv_number)) as *)
        (* (name_credit) "(Hcred_auth & Hcred & Htok)". *)
    (* iDestruct (cred_frag_split with "Hcred") as "(Hpre & Hcred)". *)
    (* iAssert (|={⊤}=> crash_borrow_ginv)%I with "[Hcred]" as ">#Hinv". *)
    (* { rewrite /crash_borrow_ginv. iApply (inv_alloc _). iNext. eauto. } *)

    iMod (nvm_heap_ctx_alloc σ PV)
      as (nvm_base_GS) "(interp & pts & #validV & crashedAt & pers)"; first done.

    set (PG := Build_PerennialG Σ Hinv (Build_credit_G Σ name_credit)).

    iExists state_interp, global_state_interp, fork_post.
    iExists _, _.
    iExists (λ inv, Φinv)%I.

    (* iDestruct (@cred_frag_to_pre_borrowN _ hG _ _ n with "Hpre") as "Hpre". *)
    iDestruct (Hwp nvm_base_GS PG with "pts validV pers") as "(#H1 & #H2 & Hwp)".

    iModIntro.
    iSplitR.
    { iApply "H1". }
    iSplitR.
    { iApply "H2". }
    iFrame.
    iFrame "#".
    by iExistsN.
    Unshelve. refine 0.
  Qed.

  (* Similar to the [recv_adequate] in Perennial except that:
    1. The invariant is removed.
    2. We ignore the global state (which is [unit] for nvm_lang). *)
  Record recv_adequate (s : stuckness) (e1 r1 : thread_state) (σ1 : state nvm_lang)
        (φ φr: thread_val → state nvm_lang → Prop) := {
    recv_adequate_result_normal t2 σ2 v2 :
      erased_rsteps (CS := nvm_crash_lang) r1 ([e1], (σ1, ())) (* NOTE: The unit is the unused global state. *)
                    (thread_of_val v2 :: t2, (σ2, ())) Normal →
      φ v2 σ2;
    recv_adequate_result_crashed t2 σ2 v2 :
      erased_rsteps (CS := nvm_crash_lang) r1 ([e1], (σ1, ()))
                    (thread_of_val v2 :: t2, (σ2, ())) Crashed →
      φr v2 σ2;
    recv_adequate_not_stuck t2 σ2 e2 stat :
      s = NotStuck →
      erased_rsteps (CS := nvm_crash_lang) r1 ([e1], (σ1,())) (t2, (σ2,())) stat →
      e2 ∈ t2 → (is_Some (thread_to_val e2) ∨ reducible (Λ := nvm_lang) e2 σ2 ());
  }.

  Lemma adequacy_impl (s : stuckness) (e1 r1: thread_state) (σ1 : state nvm_lang)
        (φ φr: thread_val → state nvm_lang → Prop) :
    recovery_adequacy.recv_adequate (CS := nvm_crash_lang)
                                    s e1 r1 σ1 () (λ v σ _, φ v σ) (λ v σ _, φr v σ) (λ _ _, True) →
    recv_adequate s e1 r1 σ1 φ φr.
  Proof. intros [????]. split; try naive_solver. Qed.

  (* This is the simpler adequacy result. *)
  Corollary base_recv_adequacy_simpl Σ Ω `{hPre : !nvmBaseGpreS Σ Ω, hP: !Perennial_preG Σ Ω} s e r σ PV φ φr:
    valid_heap σ →
    (∀ `{Hheap: !nvmBaseGS Σ Ω, HP: !PerennialG Σ},
      ⊢ ([∗ map] l ↦ v ∈ σ, l ↦fh v) -∗
        persisted PV -∗
        wpr s ⊤ e r (λ v, ⌜φ v⌝) True (λ v, ⌜φr v⌝)) →
    recv_adequate s e r (σ, PV) (λ v _, φ v) (λ v _, φr v).
  Proof.
    intros val hyp.
    apply adequacy_impl.
    eapply (base_recv_adequacy Σ Ω); first done.
    intros nB nBD.
    specialize (hyp nB nBD).
    iIntros "ptsMap crashedAt pers".
    iDestruct (hyp with "ptsMap pers") as "wpr".
    iSplit.
    { iIntros "!>" (? ?) "_". iApply fupd_mask_intro; naive_solver. }
    iSplit.
    { iIntros "!> ? !>". iIntros (? ?) "?".
      iApply fupd_mask_intro; naive_solver. }
    iFrame.
  Qed.

  Corollary base_recv_adequacy_simpl_crash_weakestpre Σ Ω `{hPre : !nvmBaseGpreS Σ Ω, hP: !Perennial_preG Σ Ω} s e r σ PV φ φc φr:
    valid_heap σ →
    (∀ `{Hheap: !nvmBaseGS Σ Ω, HP: !PerennialG Σ},
      ⊢ ([∗ map] l ↦ v ∈ σ, l ↦fh v) -∗
        persisted PV -∗
        WPC e @ s; ⊤ {{ λ v, ⌜ φ v ⌝ }} {{ φc }} ∗
        (* TODO: have an expert double check this modality *)
        ■ (φc -∗ ▷ ⚡==> (True ∧ WPC r @ s; ⊤ {{ λ v, ⌜ φr v ⌝ }} {{ φc }}))) →
    recv_adequate s e r (σ, PV) (λ v _, φ v) (λ v _, φr v).
  Proof.
    intros val hyp.
    apply (base_recv_adequacy_simpl Σ Ω); first done.
    iIntros (Hheap HP) "fmapsto #persisted".
    iPoseProof (hyp with "fmapsto persisted") as "[WPC recover]".
    iApply (idempotence_wpr with "WPC [recover]").
    - iIntros. rewrite /extra_state_interp /=. by repeat iModIntro.
    - iApply (plainly_mono with "recover").
      iIntros "Hwpc Φc".
      iSpecialize ("Hwpc" with "Φc").
      iModIntro.
      iModIntro.
      by iIntros "_".
  Qed.
End base_adequacy.
