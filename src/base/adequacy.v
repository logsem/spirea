(* In this file we show adequacy of the recovery weakest precondition in the
base logic. *)

From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map.
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
From Perennial.Helpers Require Import ipm.

From self Require Import ipm_tactics.
From self.base Require Import cred_frag crash_borrow.
From self.base Require Export wpr_lifting primitive_laws.

Set Default Proof Using "Type".

Definition nvm_build_base Σ (hpreG : nvmBaseGpreS Σ) (Hinv : invGS Σ) crIn
           (cred_names : cr_names) : nvmBaseFixedG Σ :=
  {|
    nvmBaseG_invGS := Hinv;
    nvmBaseG_gen_heapGS := nvmBase_preG_gen_heapGS;
    nvmBaseG_crashGS := crIn;
    view_inG := nvmBase_preG_view_inG;
    crashed_at_inG := nvmBase_preG_crashed_at;
    nvm_base_creditG :=
      creditGS_update_pre Σ (nvmBase_preG_credit) cred_names;
  |}.

(* Allocate the state intepretation in the base logic for any valid heap. *)
Lemma allocate_state_interp `{hPre : !nvmBaseGpreS Σ} Hinv crIn γcrash σ PV cred_names :
  valid_heap σ →
  ⊢ |==> ∃ (hGD : nvmBaseDeltaG),
    let hG := nvm_build_base _ hPre Hinv crIn cred_names in
    ⌜ @crash_token_name hGD = γcrash ⌝ ∗
    nvm_heap_ctx (σ, PV) ∗
    ([∗ map] l↦v ∈ σ, l ↦h v) ∗
    validV ∅ ∗
    crashed_at ∅ ∗
    persisted PV.
Proof.
  intros val.
  iMod (gen_heap_init_names σ) as (γh γm) "(yo & lo & holo)".
  iMod (own_alloc (● max_view σ ⋅ ◯ ε)) as (store_view_name) "[HIP ?]".
  { apply auth_both_valid_2; auto using view_valid, ucmra_unit_least. }
  iMod (own_alloc (● PV ⋅ ◯ PV)) as (persist_view_name) "[? ?]".
  { apply auth_both_valid_2; auto using view_valid. }
  iMod (own_alloc (to_agree ∅ : agreeR viewO)) as (crashed_at_name) "#crashed".
  { done. }
  iExists ({| heap_names_name := {| name_gen_heap := γh; name_gen_meta := γm |};
              crash_token_name := γcrash;
              store_view_name := store_view_name;
              persist_view_name := persist_view_name;
              crashed_at_view_name := crashed_at_name |}).
  iModIntro.
  iFrame "∗#%".
  rewrite /valid_heap.
  rewrite /hist_inv.
  iSplitPure; first done.
  iExists _. iFrame "∗#". iPureIntro. rewrite dom_empty. set_solver.
Qed.

Section base_adequacy.

  Instance empExtraStateInterp {Σ} : extraStateInterp Σ := {
    extra_state_interp := True%I
  }.

  (* The adequacy theorem for the base logic.

  This adequacy theorem makes use of the invariant feature in Perennial (the
  [φinv] and [Φinv]). This makes the statement a bit more complex and we do not
  actually need the invariant feature at all. Hence we also have a simpler
  variant below for the case where the invariant is alwasy true.  *)
  Theorem base_recv_adequacy Σ `{hPre : !nvmBaseGpreS Σ} s e r σ PV g φ φr φinv Φinv n :
    valid_heap σ →
    (∀ `{Hheap : !nvmBaseFixedG Σ, hD : !nvmBaseDeltaG},
      ⊢ pre_borrowN n -∗
        ([∗ map] l ↦ v ∈ σ, l ↦h v) -∗
        validV ∅ -∗
        persisted PV -∗ (
          □ (∀ σ nt, state_interp σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
          □ (∀ hGD, Φinv hGD -∗ □ ∀ σ nt, state_interp σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
          wpr s ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ _ v, ⌜φr v⌝))) →
    recv_adequate (CS := nvm_crash_lang) s e r (σ, PV) g (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, φinv σ).
  Proof.
    intros val Hwp.
    eapply (wp_recv_adequacy_inv _ _ _ _ _ _ _ _ _ _ _ _ _).
    (* eapply (wp_recv_adequacy_inv _ _ _ nvmBaseDeltaGO _ _ _ _ _ _ _ _ _ _). *)
    iIntros (? [crIn γcrash] ?) "".

    iMod (credit_name_init (n * 4 + crash_borrow_ginv_number)) as
        (name_credit) "(Hcred_auth & Hcred & Htok)".
    iDestruct (cred_frag_split with "Hcred") as "(Hpre & Hcred)".
    iAssert (|={⊤}=> crash_borrow_ginv)%I with "[Hcred]" as ">#Hinv".
    { rewrite /crash_borrow_ginv. iApply (inv_alloc _). iNext. eauto. }

    set (crashPre := {| crash_inPreG := crIn |}).
    iMod (allocate_state_interp Hinv crashPre γcrash σ PV name_credit)
      as (hGD) "(%cEq & interp & pts & validV & crashedAt & pers)"; first done.

    (* Build an nvmBaseFixedG. *)
    set (hG := nvm_build_base _ hPre Hinv crashPre name_credit).

    iExists state_interp, global_state_interp, fork_post.
    iExists _, _.
    iExists (
      λ inv gen, ∃ nD', ⌜gen = nvmBase_generationGS (hGD := nD') ⌝ ∗ Φinv nD'
    )%I.
    
    iDestruct (@cred_frag_to_pre_borrowN _ hG _ _ n with "Hpre") as "Hpre".
    iDestruct (Hwp hG hGD with "Hpre pts validV pers") as "(#H1 & #H2 & Hwp)".

    iModIntro.
    iSplitR.
    { iModIntro. simpl. rewrite cEq. iApply "H1". }
    iSplitR.
    { iModIntro. iIntros (Hg') "(%nD' & -> & inv)".
      iDestruct ("H2" with "inv") as "$". }
    iFrame.
    iFrame "Hinv".
    iSplit. { iPureIntro. done. }
    rewrite /wpr.
    rewrite /nvmBase_generationGS. rewrite cEq.
    iApply (recovery_weakestpre.wpr_strong_mono with "Hwp").
    iSplit; first by auto.
    iSplit; first by auto.
    by iIntros (??) "(% & _ & $)".
  Qed.

  (* Similar to the [recv_adequate] in Perennial except that:
    1. The invariant is removed.
    2. We ignore the global state (which is [unit] for nvm_lang). *)
  Record recv_adequate (s : stuckness) (e1 r1: thread_state) (σ1 : state nvm_lang)
        (φ φr: thread_val → state nvm_lang → Prop) := {
    recv_adequate_result_normal t2 σ2 v2 :
      erased_rsteps (CS := nvm_crash_lang) r1 ([e1], (σ1,()))
                    (thread_of_val v2 :: t2, (σ2,())) Normal →
    φ v2 σ2;
    recv_adequate_result_crashed t2 σ2 v2 :
      erased_rsteps (CS := nvm_crash_lang) r1 ([e1], (σ1,()))
                    (thread_of_val v2 :: t2, (σ2,())) Crashed →
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
  Corollary base_recv_adequacy_simpl Σ `{hPre : !nvmBaseGpreS Σ} s e r σ PV φ φr n :
    valid_heap σ →
    (∀ `{Hheap : !nvmBaseFixedG Σ, hD : !nvmBaseDeltaG},
      ⊢ pre_borrowN n -∗
        ([∗ map] l ↦ v ∈ σ, l ↦h v) -∗
        persisted PV -∗
        wpr s ⊤ e r (λ v, ⌜φ v⌝) (λ _, True) (λ _ v, ⌜φr v⌝)) →
    recv_adequate s e r (σ, PV) (λ v _, φ v) (λ v _, φr v).
  Proof.
    intros val hyp.
    apply adequacy_impl.
    eapply (base_recv_adequacy Σ); first apply val.
    intros nB nBD.
    specialize (hyp nB nBD).
    iIntros "borrow ptsMap crashedAt pers".
    iDestruct (hyp with "borrow ptsMap pers") as "wpr".
    iSplit.
    { iIntros "!>" (? ?) "_". iApply ncfupd_mask_intro; naive_solver. }
    iSplit.
    { iIntros "!>" (?) "? !>". iIntros (? ?) "?".
      iApply ncfupd_mask_intro; naive_solver. }
    iFrame.
  Qed.

End base_adequacy.
