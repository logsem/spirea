(* In this file we show adequacy of the recovery weakest precondition in the
base logic. *)

From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map.
(* From Perennial.goose_lang Require Import proofmode notation. *)
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
From Perennial.Helpers Require Import ipm.
(* From Perennial.goose_lang Require Export wpr_lifting. *)
(* From Perennial.goose_lang Require Import typing adequacy lang. *)

From self.base Require Export wpr_lifting primitive_laws.

Set Default Proof Using "Type".

Class nvmBaseGpreS Σ := NvmBasePreG {
  nvmBase_preG_iris :> invGpreS Σ;
  nvmBase_preG_gen_heapGS :> gen_heapGpreS loc history Σ;
  nvmBase_preG_crash :> crashPreG Σ;
  nvmBase_preG_view_inG :> view_preG Σ;
  nvmBase_preG_crashed_at :> inG Σ (agreeR viewO);
}.

Definition nvm_build_base Σ (hpreG : nvmBaseGpreS Σ) (Hinv : invGS Σ) : nvmBaseFixedG Σ :=
  {|
    nvmBaseG_invGS := Hinv;
    nvmBaseG_gen_heapGS := nvmBase_preG_gen_heapGS;
    view_inG := nvmBase_preG_view_inG;
    crashed_at_inG := nvmBase_preG_crashed_at;
  |}.

Definition nvm_build_delta Σ Hc (names : nvm_base_names) : nvmBaseDeltaG Σ :=
  {|
    nvm_base_crashG := Hc;
    nvm_base_names' := names;
  |}.

Lemma allocate_state_interp `{hPre : !nvmBaseGpreS Σ} Hinv Hc σ :
  ⊢ |==> ∃ (names : nvm_base_names),
    let hG := nvm_build_base _ hPre Hinv in
    let hGD := nvm_build_delta _ Hc names in
    nvm_heap_ctx σ.
Proof.
  iMod (gen_heap_init_names σ.1) as (γh γm) "(yo & lo & holo)".
  iMod (own_alloc (● lub_view σ.1)) as (store_view_name) "HIP".
  { apply auth_auth_valid. apply view_valid. }
  iMod (own_alloc (● σ.2)) as (persist_view_name) "?".
  { apply auth_auth_valid. apply view_valid. }
  iExists ({| heap_names_name := {| name_gen_heap := γh; name_gen_meta := γm |};
              store_view_name := store_view_name;
              persist_view_name := persist_view_name;
              crashed_at_view_name := γh; (* FIXME *)
            |}).
  iModIntro.
  iFrame.
  rewrite /valid_heap.
  rewrite /hist_inv.
Admitted.
(* Qed. *)

(* Adequacy theorem. *)
Theorem heap_recv_adequacy Σ `{hPre : !nvmBaseGpreS Σ} s k e r σ g φ φr φinv Φinv :
  (∀ `{Hheap : !nvmBaseFixedG Σ, hi : !nvmBaseDeltaG Σ},
    ⊢ (
      □ (∀ σ nt, state_interp σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
      □ (∀ hGD, Φinv hGD -∗ □ ∀ σ nt, state_interp σ nt -∗ |NC={⊤, ∅}=> ⌜ φinv σ ⌝) ∗
       wpr s k ⊤ e r (λ v, ⌜φ v⌝) Φinv (λ _ v, ⌜φr v⌝))) →
  recv_adequate (CS := nvm_crash_lang) s e r σ g (λ v _ _, φ v) (λ v _ _, φr v) (λ σ _, φinv σ).
Proof.
  intros Hwp.
  eapply (wp_recv_adequacy_inv _ _ _ nvm_base_namesO _ _ _ _ _ _ _ _ _ (λ n, n)).
  iIntros (???) "".
  iMod (allocate_state_interp Hinv Hc σ) as (hnames) "WOW".
  (* iMod (gen_heap_init_names σ.1) as (γh γm) "(yo & lo & holo)". *)
  (* set (hnames := {| heap_names_name := {| name_gen_heap := γh; *)
  (*                                         name_gen_meta := γm |}; *)
  (*                   store_view_name := γh; (* FIXME *) *)
  (*                   persist_view_name := γh; (* FIXME *) *)
  (*                   crashed_at_view_name := γh; (* FIXME *) *)
  (*                |}). *)

  iExists ({| pbundleT := hnames |}).
  (* Build an nvmBaseFixedG. *)
  set (hG := nvm_build_base _ hPre Hinv).
  set (hGD := nvm_build_delta _ Hc hnames).
  iExists
    (λ t σ nt, let _ := nvm_base_delta_update_names hGD (@pbundleT _ _ t) in
               state_interp σ nt)%I,
    (λ t g ns κs, let _ := nvm_base_delta_update_names hGD (@pbundleT _ _ t) in
                  global_state_interp g ns κs).
  iExists _. 
  iExists _.
  iExists _.
  iExists _.
  iExists _.
  iExists (λ names0 _Hinv Hc names, Φinv ({| nvm_base_crashG := Hc;
                                             nvm_base_names' := (@pbundleT _ _ names) |} )).
  iDestruct (Hwp hG hGD) as "(#H1 & #H2 & Hwp)".
  iModIntro.
  iSplitR.
  { iModIntro. iIntros (??) "Hσ".
    iApply ("H1" with "[Hσ]").
    iExactEq "Hσ". do 2 f_equal. }
  (*   rewrite /heap_update_local/hG/heap_update_pre//=. f_equal. *)
  (*   rewrite ?ffi_update_pre_update. *)
  (*   rewrite ffi_update_pre_get_local //=. *)
  (* } *)
  iSplitR.
  { iModIntro. iIntros (Hc' names') "H".
    iDestruct ("H2" $! _ with "[H]") as "#H3".
    { iExactEq "H". f_equal. }
    iModIntro. iIntros (??) "H". iSpecialize ("H3" with "[H]"); eauto. }
  iFrame. rewrite /hG //=.
  (* rewrite ffi_update_pre_update //=. iFrame. *)
  rewrite /wpr. rewrite /hG //=.
  iFrame.
  iFrame "Hwp".
  Unshelve.
  - eauto.
  (* - exact O. *)
Qed.
