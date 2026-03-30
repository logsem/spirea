From iris.proofmode Require Import ltac_tactics.
From iris.algebra Require Import auth.
From iris_named_props Require Import named_props.

From self Require Import ipm_tactics.
From self.program_logic Require Import recovery_adequacy.
From self.base Require Import wpr_lifting primitive_laws generational_resources cred_frag.
From self.high Require Import crash_weakestpre recovery_weakestpre generational_resources state_interpretation.
From self.high.modalities Require Import nextgen.
From self.nextgen Require Import nextgen_promises.

From self.high.resources Require Import
  gen_ghost_map gen_ghost_map_ofe gen_ghost_map_map gen_alocs gen_predicates auth_map_map.

(* I'm still not quite sure what's the proper way to handle these ghost resources,
 * For what I can see,
 * [invGpreS Σ]: the standard Iris invariant resources, which will be solved by [subG] eventually.
 * [ngInvG Σ Ω]: a list of resources created by Aina for invariants across generations. It's not really
 * being used in high-level Spirea, but they are tied in Perennial's adequacy proof so very difficult to remove.
 * [credit_preG Σ]: the resources for a second set of later credits, also not being used at all. *)
Class Perennial_preG Σ Ω := {
  P_invGpreS :: wsat.invGS.invGpreS Σ;
  P_preG_credit :: credit_preG Σ;
  P_ngInvG :: ngInvG Σ Ω;
}.

Definition Build_credit_G Σ `{!Perennial_preG Σ Ω} (cred_names: cr_names): creditGS Σ :=
  creditGS_update_pre Σ P_preG_credit cred_names.

Section high_adequacy.
  (* begin missing proofs. *)
  Lemma extra_state_interp_alloc `{baseG: !nvmBaseGS Σ Ω, preG: !nvmHighGpreS Σ Ω} (σ: store) PV:
    valid_heap σ →
    ([∗ map] l↦v ∈ σ, l ↦fh v) -∗
    crashed_at ∅ -∗
    persisted PV ==∗
    ∃ (_: nvmHighGS Σ Ω), extra_state_interp.
  Proof.
    iIntros (?) "_ #CV #PV".
    iNamed "CV".
    iAssert (crashed_at_offset OCV)%I as "#OCV".
    { by iExists _. }
    rewrite /extra_state_interp /highExtraStateInterp /interp.
    iMod (gen_alocs_alloc ∅ OCV OPV  with "OCV rely") as (new_locs_name) "[newLocs _]".
    iMod (auth_map_map_alloc OCV OPV with "OCV rely") as (phy_history_name) "physHists".
    iMod (ghost_map_alloc (V := positive → option positive) OPV OCV ∅ (DfracOwn 1) with "OCV rely")
      as (bumpers_name) "[allBumpers _]"; first done.
    iMod (full_map_alloc bumpers_name OPV OCV ∅ with "[] OCV rely") as (abs_history_name) "[history _]".
    { by rewrite big_sepS_empty. }
    iMod (ghost_mapO_alloc (t := gen_predicates.drop_OCV) (V := predicateO Σ) OPV OCV ∅ (DfracOwn 1) with "OCV rely")
      as (full_predicates_name) "[full_predicates _]"; first done.
    iMod (ghost_mapO_alloc (t := gen_predicates.drop_OCV) (V := predicateO Σ) OPV OCV ∅ (DfracOwn 1) with "OCV rely")
      as (read_predicates_name) "[read_predicates _]"; first done.
    iMod (ghost_mapO_alloc (t := gen_predicates.drop_OCV) (V := predicateO Σ) OPV OCV ∅ (DfracOwn 1) with "OCV rely")
      as (pers_predicates_name) "[pers_predicates _]"; first done.
    iMod (ghost_map_alloc (V := extra.relation2 positive) OPV OCV ∅ (DfracOwn 1) with "OCV rely")
      as (preorders_name) "[allOrders _]"; first done.
    iMod (gen_alocs_alloc ∅ OCV OPV with "OCV rely") as (exclusive_locs_name) "[naLocs _]".
    iMod (gen_alocs_alloc ∅ OCV OPV with "OCV rely") as (shared_locs_name) "[atLocs _]".
    iMod (ghost_map_alloc (V := view.view) OPV OCV ∅ (DfracOwn 1) with "OCV rely")
      as (non_atomic_views_gname) "[naView _]"; first done.
    iModIntro.
    iExists (NvmHighG Σ Ω baseG preG full_predicates_name read_predicates_name pers_predicates_name
               abs_history_name phy_history_name non_atomic_views_gname
               preorders_name exclusive_locs_name shared_locs_name new_locs_name bumpers_name).
    rewrite /own_all_bumpers.
    repeat (iExists ∅).
    iFrameNamed.
    rewrite ?big_sepM_empty ?big_sepM2_empty.
    rewrite ?left_id.
    iSplitL "newLocs".
    { iExists OCV. iFrame "∗#". naive_solver. }
    iSplit; first by iExists _.
    repeat (iSplitPure; first (try (done || set_solver ))).
    done.
  Qed.

  (* FIXME: this should be treated by the [solve_inG] equivalent for [Ω]. *)
  Context (Build_nvmHighGpreS: ∀ Σ Ω (nvmBase: nvmBaseGS Σ Ω), nvmHighGpreS Σ Ω).
  
  (* ends missing proofs. *)    
  Theorem high_recv_adequacy Σ Ω `{!nvmBaseGpreS Σ Ω, !Perennial_preG Σ Ω}
    s e r σ PV g φ φr φinv Φinv :
    valid_heap σ →
    (∀ `{!nvmBaseGS Σ Ω} `{!nvmHighGS Σ Ω} `{!PerennialG Σ},
       ⊢
        (* TODO: restore crash borrow after porting the dependencies *)
        (* pre_borrowN n -∗ *)
        validV ∅ -∗
        persisted PV -∗ (
          (* TODO: confirm these modalities *)
          ■ (∀ σ nt, state_interp σ nt -∗ |={⊤,∅}=> ⌜ φinv σ ⌝) ∗
          ■ (Φinv -∗ □ ∀ σ nt, state_interp σ nt -∗ |={⊤,∅}=> ⌜ φinv σ ⌝) ∗
          wpr s ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ v, ⌜φr v⌝))) →
    recv_adequate (CS := nvm_crash_lang) s e r (σ, PV) g (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, φinv σ).
  Proof using Build_nvmHighGpreS.
    intros val Hwp.
    eapply (wp_recv_adequacy_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    (* eapply (wp_recv_adequacy_inv _ _ _ nvmBaseDeltaGO _ _ _ _ _ _ _ _ _ _). *)
    iIntros (? ?) "".
    iStartProof.
    assert (∃ name_credit: cr_names, True) as [name_credit _].
    { by exists (Build_cr_names (xH) (xH)). }
    (* iMod (credit_name_init (crash_borrow_ginv_number)) as *)
        (* (name_credit) "(Hcred_auth & Hcred & Htok)". *)
    (* iDestruct (cred_frag_split with "Hcred") as "(Hpre & Hcred)". *)
    (* iAssert (|={⊤}=> crash_borrow_ginv)%I with "[Hcred]" as ">#Hinv". *)
    (* { rewrite /crash_borrow_ginv. iApply (inv_alloc _). iNext. eauto. } *)

    (* FIXME: some kind of typeclass failure? *)
    iPoseProof (nvm_heap_ctx_alloc σ PV) as "heap"; first done.
    iMod "heap" as (nvm_base_GS) "(interp & pts & #validV & crashedAt & #pers)".

    set (highPreG := Build_nvmHighGpreS _ _ nvm_base_GS).
    set (PG := Build_PerennialG Σ Hinv (Build_credit_G Σ name_credit)).

    iMod (extra_state_interp_alloc σ PV with "[$] [$] [#$]") as (nvm_high_GS) "extra"; first done.
    
    iExists state_interp, global_state_interp, fork_post.
    iExists _, _.
    iExists (λ inv, Φinv)%I.

    (* iDestruct (@cred_frag_to_pre_borrowN _ hG _ _ n with "Hpre") as "Hpre". *)
    iDestruct (Hwp nvm_base_GS nvm_high_GS PG with "validV pers") as "(#H1 & #H2 & Hwp)".

    iModIntro.
    iSplitR.
    { iApply "H1". }
    iSplitR.
    { iApply "H2". }
    iFrame.
    iFrame "#".
    by iExistsN.
    Unshelve.
    - refine 0.
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
  Corollary high_recv_adequacy_simpl Σ Ω `{HbasePre : !nvmBaseGpreS Σ Ω, hP: !Perennial_preG Σ Ω} s e r σ PV φ φr:
    valid_heap σ →
    (∀ `{Hheap: !nvmBaseGS Σ Ω, Hhigh: !nvmHighGS Σ Ω, HP: !PerennialG Σ},
      ⊢ validV ∅ -∗
        persisted PV -∗
        wpr s ⊤ e r (λ v, ⌜φ v⌝) True (λ v, ⌜φr v⌝)) →
    recv_adequate s e r (σ, PV) (λ v _, φ v) (λ v _, φr v).
  Proof using Build_nvmHighGpreS.
    intros val hyp.
    apply adequacy_impl.
    eapply (high_recv_adequacy Σ Ω); first done.
    intros nB nH nBD.
    specialize (hyp nB nH nBD).
    iIntros "validV pers".
    iDestruct (hyp with "validV pers") as "wpr".
    iSplit.
    { iIntros "!>" (? ?) "_". iApply fupd_mask_intro; naive_solver. }
    iSplit.
    { iIntros "!> ? !>". iIntros (? ?) "?".
      iApply fupd_mask_intro; naive_solver. }
    iFrame.
  Qed.

  Corollary base_recv_adequacy_simpl_crash_weakestpre Σ Ω `{hPre : !nvmBaseGpreS Σ Ω, hP: !Perennial_preG Σ Ω} s (e r: expr) σ PV φ φc φr:
    valid_heap σ →
    (∀ `{Hheap: !nvmBaseGS Σ Ω, Hhigh: !nvmHighGS Σ Ω, HP: !PerennialG Σ},
      ⊢ validV ∅ -∗
        persisted PV -∗
        (WPC e @ s; ⊤ {{ λ v, ⌜ φ v ⌝ }} {{ φc }} ⊥) ∗
        (* TODO: have an expert double check this modality *)
        ■ (φc -∗ ▷ <NG> (WPC r @ s; ⊤ {{ λ v, ⌜ φr v ⌝ }} {{ φc }})) ⊥) →
    recv_adequate s (e `at` ⊥) (r `at` ⊥) (σ, PV) (λ v _, φ v.(val_val)) (λ v _, φr v.(val_val)).
  Proof using Build_nvmHighGpreS.
    intros val hyp.
    apply (high_recv_adequacy_simpl Σ Ω); first done.
    iIntros (Hheap Hhigh HP) "#validV #persisted".
    iPoseProof (hyp with "validV persisted") as "[WPC recover]".
    iApply wpr_strong_mono.
    - iApply (idempotence_wpr _ _ _ _ _).
      + done.
      + done.
      + iApply (plainly_mono with "recover").
        rewrite ?monPred_at_wand.
        iIntros "Hwpc %i % Φc".
        iSpecialize ("Hwpc" $! i with "[//] [$]").
        rewrite ?monPred_at_later.
        iModIntro.
        rewrite /nextgen.nextgen /=.
        iIntros "!> #Hfrag".
        iSpecialize ("Hwpc" with "Hfrag").
        done.
    - iApply (plainly_intro True); last done.
      iIntros (_).
      repeat iSplit; naive_solver. 
  Qed.
End high_adequacy.
