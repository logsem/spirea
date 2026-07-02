(* In this file we show adequacy of the recovery weakest precondition in the
base logic. *)

From Equations Require Import Equations.
From iris.proofmode Require Import ltac_tactics.
From iris.algebra Require Import auth numbers coPset gset.
(* From PerennialNG.base_logic.lib Require Import proph_map. *)
From self.program_logic Require Import recovery_weakestpre recovery_adequacy.
(* From PerennialNG.Helpers Require Import ipm. *)

From self Require Import ipm_tactics.
From self.base Require Import cred_frag.
From self.base Require Import wpr_lifting primitive_laws generational_resources.
From self.nextgen Require Import nextgen_promises nextgen_promises_ng inv_ng.
From Perennial.algebra Require Import mlist.

Set Default Proof Using "Type".

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


    (* FIXME: some kind of typeclass failure? *)
    iPoseProof (nvm_heap_ctx_alloc σ PV) as "heap"; first done.
    iMod "heap"
      as (nvm_base_GS) "(interp & pts & #validV & crashedAt & #crashedOffset & pers)".

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
    iApply (idempotence_wpr emp with "WPC [recover]").
    - iIntros.
      iMod (heap_ctx_next_generation with "[$]") as (?) "(_ & _ & heap)"; first done.
      do 3 iModIntro.
      by iMod "heap" as "[_ $]".
    - iApply (plainly_mono with "recover").
      iIntros "Hwpc Φc".
      iSpecialize ("Hwpc" with "Φc").
      iModIntro.
      iModIntro.
      by iIntros "_ _".
  Qed.
End base_adequacy.

(* ** A concrete [Σ]/[Ω] to instantiate [base_recv_adequacy].
 *
 * [base_recv_adequacy] is parametric in [Σ]/[Ω] behind [nvmBaseGpreS] and
 * [Perennial_preG].  To *apply* it to a closed program we need a concrete model
 * that discharges both.  [nvmBaseΩ] contains the four generational resources of
 * the base logic at gids 0-3 (mirroring [myΩ] in [nextgen_test.v]); the
 * [invΣ]/[creditΣ] functors that [Perennial_preG] needs are appended afterwards,
 * so they live in [Σ] but outside [Ω]'s generational map. *)

(* Fully destruct a [fin n] with a concrete [n]. *)
Ltac dep_inv_fin idx :=
  let H := fresh in
  let T := type of idx in
  match eval hnf in T with
  | fin ?n =>
    match eval hnf in n with
    | 0 => inversion idx
    | 1 => dependent elimination idx as [Fin.F1]
    | S ?n => dependent elimination idx as [Fin.F1 | FS H];
              last rename H into idx
    end
  end.
Ltac destruct_fin i1 := repeat (dep_inv_fin i1).
Ltac solve_gid_uniq := intros i1 i2 neq; destruct_fin i1; destruct_fin i2; done.
Ltac solve_omega_wf := intros idx dIdx look; destruct_fin idx; destruct_fin dIdx; done.

Section base_omega.

  (* The four generational functors first (gids 0-3), then the non-generational
   * Perennial resources. *)
  Definition nvmBaseΣ : gFunctors := #[
    GFunctor (generational_cmraR store_viewR [#]);
    GFunctor (generational_cmraR crashed_atR [#]);
    GFunctor (generational_cmraR persistedR [#crashed_atR]);
    GFunctor (generational_cmraR heapR [#crashed_atR]);
    wsat.invGS.invΣ;
    creditΣ
  ].

  Program Definition nvmBaseΩ : gGenCmras nvmBaseΣ := {|
    gc_len := 4;
    gc_map := λ (i : fin 4), _;
  |}.
  Next Obligation.
    intros idx.
    (* 0 : store_view *)
    dependent elimination idx as [Fin.F1 | FS idx].
    { apply {| gcd_cmra := store_viewR; gcd_n := 0; gcd_deps := [#];
               gcd_deps_ids := [#]; gcd_gid := (0%fin : gid nvmBaseΣ);
               gcd_cmra_eq := eq_refl; |}. }
    (* 1 : crashed_at *)
    dependent elimination idx as [Fin.F1 | FS idx].
    { apply {| gcd_cmra := crashed_atR; gcd_n := 0; gcd_deps := [#];
               gcd_deps_ids := [#]; gcd_gid := (1%fin : gid nvmBaseΣ);
               gcd_cmra_eq := eq_refl; |}. }
    (* 2 : persisted, depends on crashed_at (index 1) *)
    dependent elimination idx as [Fin.F1 | FS idx].
    { apply {| gcd_cmra := persistedR; gcd_n := 1; gcd_deps := [#crashed_atR];
               gcd_deps_ids := [#1%fin]; gcd_gid := (2%fin : gid nvmBaseΣ);
               gcd_cmra_eq := eq_refl; |}. }
    (* 3 : heap, depends on crashed_at (index 1) *)
    apply {| gcd_cmra := heapR; gcd_n := 1; gcd_deps := [#crashed_atR];
             gcd_deps_ids := [#1%fin]; gcd_gid := (3%fin : gid nvmBaseΣ);
             gcd_cmra_eq := eq_refl; |}.
  Defined.
  Next Obligation. solve_omega_wf. Qed.
  Next Obligation. solve_gid_uniq. Qed.

  (* The [genInG] instances tie each resource to its index in [Ω].  All [Defined]
   * so that [genInG_id] reduces (needed by the dependency well-formedness
   * equations below). *)
  #[global] Instance nvmBase_store_view_genInG : genInG nvmBaseΣ nvmBaseΩ store_viewR [#].
  Proof. eapply (GenInG _ nvmBaseΣ nvmBaseΩ _ _ 0%fin eq_refl); done. Defined.

  #[global] Instance nvmBase_crashed_at_genInG : genInG nvmBaseΣ nvmBaseΩ crashed_atR [#].
  Proof. eapply (GenInG _ nvmBaseΣ nvmBaseΩ _ _ 1%fin eq_refl); done. Defined.

  #[global] Instance nvmBase_persisted_genInG : genInG nvmBaseΣ nvmBaseΩ persistedR [#crashed_atR].
  Proof. eapply (GenInG _ nvmBaseΣ nvmBaseΩ _ _ 2%fin eq_refl); done. Defined.

  #[global] Instance nvmBase_heap_genInG : genInG nvmBaseΣ nvmBaseΩ heapR [#crashed_atR].
  Proof. eapply (GenInG _ nvmBaseΣ nvmBaseΩ _ _ 3%fin eq_refl); done. Defined.

  (* The dependency-free [genInDepsG] instances.  [nvmBase_crashed_at_genInDepsG]
   * must stay [Defined]: the [persisted]/[heap] well-formedness equations reduce
   * [genInG_id] through it. *)
  #[global] Instance nvmBase_store_view_genInDepsG : genInDepsG nvmBaseΣ nvmBaseΩ store_viewR [#].
  Proof. eapply (GenDepsInG _ nvmBaseΣ nvmBaseΩ store_viewR _). intros i; destruct_fin i. Qed.

  #[global] Instance nvmBase_crashed_at_genInDepsG : genInDepsG nvmBaseΣ nvmBaseΩ crashed_atR [#].
  Proof. eapply (GenDepsInG _ nvmBaseΣ nvmBaseΩ crashed_atR _). intros i; destruct_fin i. Defined.

  (* The pre-ghost-state classes.  For [persisted]/[heap] the dependency-aware
   * [genInDepsG] is built *inline* so its [gs] matches the one demanded by the
   * class field (cf. the [subG_raΣ_3_deps] warning in [nextgen_test.v]). *)
  #[global] Instance nvmBase_store_viewGpreS : store_viewGpreS nvmBaseΣ nvmBaseΩ :=
    {| store_viewGpreS_store_view := _ |}.

  #[global] Instance nvmBase_crashed_atGpreS : crashed_atGpreS nvmBaseΣ nvmBaseΩ :=
    {| crashed_atGpreS_crashed_at := _ |}.

  #[global] Instance nvmBase_persistedGpreS : persistedGpreS nvmBaseΣ nvmBaseΩ.
  Proof.
    refine {| persistedGpreS_persisted := _ |}.
    eapply (GenDepsInG _ nvmBaseΣ nvmBaseΩ persistedR _). intros i; destruct_fin i; done.
  Qed.

  #[global] Instance nvmBase_heapGpreS : heapGpreS nvmBaseΣ nvmBaseΩ.
  Proof.
    refine {| heapGpreS_heap := _ |}.
    eapply (GenDepsInG _ nvmBaseΣ nvmBaseΩ heapR _). intros i; destruct_fin i; done.
  Qed.

  #[global] Instance nvmBase_baseGpreS : nvmBaseGpreS nvmBaseΣ nvmBaseΩ :=
    {| nvmBaseGpreS_store_viewGpreS := _;
       nvmBaseGpreS_crashed_atGpreS := _;
       nvmBaseGpreS_persistedGpreS := _;
       nvmBaseGpreS_heapGpreS := _ |}.

  (* --- [Perennial_preG]. ---
   * The invariant/credit resources are non-generational: they sit in [nvmBaseΣ]
   * at gids ≥ 4, disjoint from [nvmBaseΩ]'s generational gids 0-3.  We do NOT
   * obtain their [inG]s via [subG] (whose gids are opaque and do not reduce);
   * instead we expose each as an explicit [inG] at its *literal* index.  Crucially
   * [ngInvG] hard-codes its component [inG]s to be exactly the fields of the
   * ambient [invGpreS], so we build [nvmBase_invGpreS] itself out of these literal
   * [inG]s.  Then the [ngInG] disjointness evidence [∀ i, Ogid nvmBaseΩ i ≠ inG_id]
   * closes by a finite case split on [i ∈ fin 4] (both sides are literal [fin]s).
   * [invΣ] contributes 5 functors, in order:
   *   4 : invR   5 : coPset_disjR   6 : gset_disjR positive
   *   7 : fmlistUR invariant_level_names   8 : authR natUR (later credits). *)
  (* [inG_prf := eq_refl] for the *functorial* [invR] (it contains
   * [laterO (iPropO Σ)]) forces the kernel to convert
   * [invR nvmBaseΣ ≡ rFunctor_apply (…) (iPropO nvmBaseΣ)], which unfolds the
   * whole nested functor over [iPropO nvmBaseΣ] and takes ~90s.  These strategy
   * hints (the same trick [wsat.v] uses for [solve_inG]) keep those constructors
   * folded during conversion and bring it down to instant. *)
  Local Strategy 100
    [authR gmapUR gmapURF agreeR prodR optionR prodO laterO listO].

  Definition nvmBase_invR_inG : inG nvmBaseΣ (wsat.invGS.invR nvmBaseΣ) :=
    {| inG_id := (4%fin : gid nvmBaseΣ); inG_prf := eq_refl |}.
  Definition nvmBase_coPset_inG : inG nvmBaseΣ coPset_disjR :=
    {| inG_id := (5%fin : gid nvmBaseΣ); inG_prf := eq_refl |}.
  Definition nvmBase_gset_inG : inG nvmBaseΣ (gset_disjR positive) :=
    {| inG_id := (6%fin : gid nvmBaseΣ); inG_prf := eq_refl |}.
  Definition nvmBase_fmlist_inG : inG nvmBaseΣ (fmlistUR wsat.invariant_level_names) :=
    {| inG_id := (7%fin : gid nvmBaseΣ); inG_prf := eq_refl |}.
  Definition nvmBase_lc_inG : inG nvmBaseΣ (authR natUR) :=
    {| inG_id := (8%fin : gid nvmBaseΣ); inG_prf := eq_refl |}.

  (* [invGpreS] built from the literal [inG]s (transparent, so its projections
   * reduce to the literals above). *)
  #[global] Instance nvmBase_invGpreS : wsat.invGS.invGpreS nvmBaseΣ :=
    {| wsat.invGS.inv_inPreG := nvmBase_invR_inG;
       wsat.invGS.enabled_inPreG := nvmBase_coPset_inG;
       wsat.invGS.disabled_inPreG := nvmBase_gset_inG;
       wsat.invGS.mlist_inPreG := {| fmlist_inG := nvmBase_fmlist_inG |};
       wsat.invGS.inv_lcPreG := {| lcGpreS_inG := nvmBase_lc_inG |} |}.

  #[global] Instance nvmBase_credit_preG : credit_preG nvmBaseΣ.
  Proof. apply _. Qed.

  (* Each [ngInG] evidence is a finite case split; both sides reduce to literal
   * [fin]s so [done] discriminates. *)
  Ltac solve_ngInG := econstructor; intros i; destruct_fin i; done.

  #[global] Instance nvmBase_ng_invR : @ngInG nvmBaseΣ nvmBaseΩ _ nvmBase_invR_inG.
  Proof. solve_ngInG. Qed.
  #[global] Instance nvmBase_ng_coPset : @ngInG nvmBaseΣ nvmBaseΩ _ nvmBase_coPset_inG.
  Proof. solve_ngInG. Qed.
  #[global] Instance nvmBase_ng_gset : @ngInG nvmBaseΣ nvmBaseΩ _ nvmBase_gset_inG.
  Proof. solve_ngInG. Qed.
  #[global] Instance nvmBase_ng_fmlist : @ngInG nvmBaseΣ nvmBaseΩ _ nvmBase_fmlist_inG.
  Proof. solve_ngInG. Qed.
  #[global] Instance nvmBase_ng_lc : @ngInG nvmBaseΣ nvmBaseΩ _ nvmBase_lc_inG.
  Proof. solve_ngInG. Qed.

  #[global] Instance nvmBase_ngLcGS : @ngLcGS nvmBaseΣ nvmBaseΩ nvmBase_lc_inG :=
    {| ngLcGS_inG := nvmBase_ng_lc |}.

  #[global] Instance nvmBase_ngFmlistG :
    @ngFmlistG wsat.invariant_level_names _ nvmBaseΣ nvmBaseΩ nvmBase_fmlist_inG :=
    {| ngFmlist_inG := nvmBase_ng_fmlist |}.

  (* The component [inG]s of [ngInvG] are the fields of [nvmBase_invGpreS], which
   * reduce to the literal [inG]s above — so the evidence instances match. *)
  #[global] Instance nvmBase_ngInvG : ngInvG nvmBaseΣ nvmBaseΩ.
  Proof. econstructor; apply _. Qed.

  #[global] Instance nvmBase_Perennial_preG : Perennial_preG nvmBaseΣ nvmBaseΩ :=
    {| P_invGpreS := nvmBase_invGpreS;
       P_preG_credit := nvmBase_credit_preG;
       P_ngInvG := nvmBase_ngInvG |}.

End base_omega.
