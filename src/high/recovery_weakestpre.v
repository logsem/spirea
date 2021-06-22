(* Implementation of the recovery weakest precondition for NVMLang. *)

From Coq Require Import QArith Qcanon.

From stdpp Require Import sets.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gset.
From iris.base_logic Require Import ghost_map.
From iris_named_props Require Import named_props.
From Perennial.program_logic Require Import crash_weakestpre.
From Perennial.program_logic Require Import recovery_weakestpre.
From Perennial.program_logic Require Import recovery_adequacy.

From self Require Import view.
From self.base Require Import primitive_laws wpr_lifting.
From self.high Require Import dprop.
From self.high Require Import resources weakestpre crash_weakestpre post_crash_modality.

Set Default Proof Using "Type".

Notation pbundleG := recovery_weakestpre.pbundleG.

Notation perennialG := recovery_weakestpre.perennialG.

(* The recovery WP is parameterized by two predicates: [Φ] is the postcondition
   for normal non-crashing execution and [Φr] is the postcondition satisfied in
   case of a crash. *)
Definition wpr_pre `{nvmFixedG Σ} (s : stuckness) (k : nat)
    (wpr : nvmDeltaG Σ -d> coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
                     (nvmDeltaG Σ -d> val -d> dPropO Σ) -d> dPropO Σ) :
  nvmDeltaG Σ -d> coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
  (nvmDeltaG Σ -d> val -d> dPropO Σ) -d> dPropO Σ :=
  λ hGD E e e_rec Φ Φr,
  (WPC e @ s ; k; E
     {{ Φ }}
     {{ ∀ σ σ' (HC : crash_prim_step nvm_crash_lang σ σ') n,
        ⎡ interp -∗ state_interp σ n ={E}=∗ ▷ ∀ (Hc1 : crashG Σ) q, NC q ={E}=∗
          ∃ (hGD' : nvmDeltaG Σ), (* Maybe state that [hGD'] contains [Hc1] *)
            (* let hG := (nvm_update Σ hG _ Hc1 names) in *)
              state_interp σ' 0 ∗
              (monPred_at (wpr hGD' E e_rec e_rec (λ v, Φr hGD' v) Φr) (∅, ∅, ∅)) ∗
              NC q ⎤
     }})%I.

Local Instance wpr_pre_contractive `{nvmFixedG Σ} s k: Contractive (wpr_pre s k).
Proof.
  rewrite /wpr_pre. intros ??? Hwp ??????.
  apply wpc_ne; eauto;
  repeat (f_contractive || f_equiv). apply Hwp.
Qed.

Definition wpr_def `{nvmFixedG Σ} (s : stuckness) k := fixpoint (wpr_pre s k).
Definition wpr_aux `{nvmFixedG Σ} : seal (@wpr_def Σ). by eexists. Qed.
Definition wpr' `{nvmFixedG Σ} := (wpr_aux).(unseal).
Definition wpr_eq `{nvmFixedG Σ} : wpr' = @wpr_def _ := wpr_aux.(seal_eq).
(* Lemma wpr_eq `{nvmFixedG Σ} : @wpr' Σ = @wpr_def Σ. *)
(* Proof. rewrite /wpr'. rewrite wpr_aux.(seal_eq). done. Qed. *)

Lemma wpr_unfold `{nvmFixedG Σ, hGD : nvmDeltaG Σ} st k E e rec Φ Φc :
  wpr' _ st k hGD E e rec Φ Φc ⊣⊢ wpr_pre st k (wpr' _ st k) hGD E e rec Φ Φc.
Proof.
  rewrite wpr_eq. rewrite /wpr_def.
  apply (fixpoint_unfold (wpr_pre st k)).
Qed.

(* For each location in [p] pick the message in the store that it specifies. *)
Definition slice_of_hist {A} (p : view) (σ : gmap loc (gmap time A)) :
  gmap loc (gmap time A) :=
  map_zip_with
    (λ '(MaxNat t) hist,
      match hist !! t with
        Some s => {[ 0 := s ]}
      | None => ∅ (* The None branch here is never taken. *)
      end)
    p σ.

Section slice_of_hist_props.
  Context {A : Type}.
  Implicit Types (hists : gmap loc (gmap time A)).

  Lemma slice_of_hist_dom_subset p hists :
    dom (gset loc) (slice_of_hist p hists) ⊆ dom (gset loc) hists.
  Proof.
    rewrite /slice_of_hist.
    intros l.
    rewrite !elem_of_dom.
    intros [? look].
    apply map_lookup_zip_with_Some in look.
    destruct look as (? & ? & ? & ? & ?).
    eexists _. done.
  Qed.

  (* Lemma slice_of_hist_dom_eq p store hists : *)
  (*   consistent_cut p store → *)
  (*   dom (gset loc) (slice_of_hist p hists) = dom _ p. *)
  (* Proof. *)
  (*   rewrite set_eq. *)
  (*   (* rewrite /consistent_cut /slice_of_hist. *) *)
  (*   intros ?%consistent_cut_subseteq_dom ℓ. *)
  (*   rewrite map_zip_with_dom. *)
  (*   set_solver. *)
  (*   apply consistent_cut_subseteq_dom. *)

End slice_of_hist_props.

(** If we have a map of points-to predicates prior to a crash and know what we
we crashed at, then we can get a map of points-to predicates for the new
heap. *)
Lemma map_points_to_to_new `{nvmBaseFixedG Σ} logHists store p' (hG hG' : nvmBaseDeltaG Σ) :
  consistent_cut p' store →
  own (@crashed_at_view_name (@nvm_base_names' _ hG')) (to_agree p') -∗
  base.post_crash_modality.post_crash_map store hG hG' -∗
  ([∗ map] ℓ ↦ hist ∈ logHists, let hG := hG in ℓ ↦h hist) -∗
  ([∗ map] ℓ ↦ hist ∈ (slice_of_store p' logHists), let hG := hG' in ℓ ↦h hist).
Proof.
  iIntros (cut) "#rec [impl map] pts".
  iAssert (⌜logHists ⊆ store⌝)%I as %sub.
  { rewrite map_subseteq_spec.
    iIntros (ℓ msg look).
    iApply "impl".
    iApply (big_sepM_lookup with "pts"); first done. }
  iAssert (⌜dom (gset _) logHists ⊆ dom _ store⌝)%I as %histSubStore.
  { rewrite elem_of_subseteq. iIntros (ℓ).
    rewrite !elem_of_dom. iIntros ([hist look]).
    iDestruct (big_sepM_lookup with "pts") as "pts"; first apply look.
    iExists _. iApply "impl"; done. }
  (* Throw away the points-to predicates that did not survive the crash. *)
  iDestruct (big_sepM_subseteq with "pts") as "pts".
  { apply (restrict_subseteq (dom _ p')). }
  iDestruct (big_sepM_subseteq with "map") as "map".
  { apply (restrict_subseteq (dom _ (restrict (dom (gset _) p') logHists))). }
  iDestruct (big_sepM_sepM2_2 with "pts map") as "map".
  { setoid_rewrite <- elem_of_dom.
    setoid_rewrite restrict_dom_subset at 2; first done.
    etrans; last apply histSubStore.
    apply subseteq_dom.
    apply restrict_subseteq. }
  iDestruct (big_sepM2_alt with "map") as "[%fall map]".
  iDestruct (big_sepM_impl_sub _ _ _ (slice_of_store _ _) with "map []") as "[$ _]".
  { rewrite /slice_of_store.
    rewrite !map_zip_with_dom.
    rewrite (restrict_dom_subset _ store).
    2: { rewrite restrict_dom. set_solver. }
    rewrite restrict_dom.
    set_solver. }
  iIntros "!>" (ℓ [? hist] hy look look') "[pts disj]".
  iDestruct "disj" as (qc pc) "(left & right & %sum)".
  simpl.
  rewrite /post_crash_modality.if_non_zero.
  destruct (decide (0 < qc)%Qc).
  { by iDestruct (mapsto_ne with "pts left") as %Hi. }
  iDestruct "left" as %->.
  rewrite Qcplus_0_l in sum.
  rewrite sum.
  simpl.
  rewrite /post_crash_modality.mapsto_post_crash.
  iDestruct "right" as "[right | left]".
  2: {
    iExFalso.
    rewrite /slice_of_store in look'.
    apply elem_of_dom_2 in look'.
    setoid_rewrite map_zip_with_dom in look'.
    setoid_rewrite elem_of_intersection in look'.
    destruct look' as [look' _].
    apply elem_of_dom in look'.
    destruct look' as [[t] ?].
    iDestruct ("left" $! p' with "rec") as %hv.
    simplify_eq. }
  iDestruct "right" as (t msg look'') "(newPts & crash)".
  iDestruct "crash" as (? incl p'Look) "crash'".
  iDestruct (crashed_at_agree with "crash' rec") as %->.

  rewrite post_crash_modality.mk_Qp_1.
  apply map_lookup_zip_with_Some in look.
  destruct look as (? & ? & [= <- <-] & ? & lookStore).
  apply restrict_lookup_Some in lookStore.
  destruct lookStore as [lookStore ?].
  rewrite /slice_of_store in look'.
  apply map_lookup_zip_with_Some in look'.
  destruct look' as ([t'] & physHist & eq & ?look & ?look).

  setoid_rewrite map_subseteq_spec in sub.
  specialize (sub _ _ look0).
  simplify_eq.
  rewrite look''.
  iFrame"newPts".
Qed.

Definition wpr `{nvmFixedG Σ, nvmDeltaG Σ} s k := wpr' _ s k _.

Section wpr.
  Context `{nvmFixedG Σ}.

  (* Given the state interpretations _before_ a crash we reestablish the
  interpretations _after_ a crash. *)
  Lemma nvm_reinit (hGD : nvmDeltaG Σ) n Pg tv σ σ' (Hinv : invG Σ) (Hcrash : crashG Σ) :
    crash_step σ σ' →
    ⊢ interp -∗
      state_interp σ n -∗
      (post_crash Pg) tv ==∗
      ∃ (hGD' : nvmDeltaG Σ),
        (* let hG := nvm_update Σ hG' Hinv Hcrash names in *)
          interp (hGD := hGD') ∗
          nvm_heap_ctx (hG := _) σ' ∗
          Pg hGD' (∅, ∅, ∅).
  Proof.
    iIntros ([store p p' pIncl cut]).
    iIntros "H".
    iNamed "H".
    iIntros "(heap & authStor & inv & pers & recov) Pg".

    (* We need to first re-create the ghost state for the base interpretation. *)
    iMod (nvm_heap_reinit _ _ _ _ _ Hcrash with "heap inv pers")
      as (baseNames) "(map' & interp' & #persImpl & #newCrashedAt)"; try done.

    iDestruct (big_sepM2_dom with "ordered") as %domHistsEqOrders.

    (* Allocate new ghost state for the logical histories. *)
    rewrite /interp.
    set newAbsHists := slice_of_hist p' abs_hists.
    iMod (own_full_history_gname_alloc newAbsHists)
      as (new_abs_history_name new_know_abs_history_name) "(hists' & #histFrags & knowHistories)".

    iMod (own_all_preorders_discard with "allOrders") as "#allOrders".
    (* Some locations may be lost after a crash. For these we need to
    forget/throw away the predicate and preorder that was choosen for the
    location. *)
    set newOrders := restrict (dom (gset _) newAbsHists) orders.
    iMod (own_all_preorders_gname_alloc newOrders)
      as (new_orders_name) "[newOrders #fragOrders]".


    set newPreds := restrict (dom (gset _) newAbsHists) preds.
    iMod (know_predicates_alloc newPreds) as (new_predicates_name) "newPreds".

    set newSharedLocs := (dom (gset _) newAbsHists) ∩ shared_locs.
    iMod (own_alloc (● (newSharedLocs : gsetUR _))) as (new_shared_locs_name) "newSharedLocs".
    { apply auth_auth_valid. done. }

    (* We are done allocating ghost state and can now present a new bundle of
    ghost names. *)
    iModIntro.
    iExists (
        NvmDeltaG _
                  (MkNvmBaseDeltaG _ Hcrash baseNames)
                  ({| abs_history_name := new_abs_history_name;
                      know_abs_history_name := new_know_abs_history_name;
                      predicates_name := new_predicates_name;
                      recovery_predicates_name := _;
                      preorders_name := new_orders_name;
                      shared_locs_name := new_shared_locs_name;
                      exclusive_locs_name := _;
                   |})
      ).
    iFrame "interp'".
    rewrite /nvm_heap_ctx.
    rewrite /post_crash. simpl.
    rewrite /base_post_crash. simpl.
    iDestruct ("Pg" $! _ (abs_hists) (store, _) _ with "persImpl map'") as "(map' & Pg)".
    simpl.
    iDestruct
      (map_points_to_to_new _ _ _ _ (MkNvmBaseDeltaG Σ Hcrash baseNames)
         with "newCrashedAt map' ptsMap") as "ptsMap"; first done.
    rewrite /post_crash_map.
    (* We show the assumption for the post crash modality. *)
    iDestruct ("Pg" with "[history knowHistories]") as "[$ WHAT]".
    { simpl.
      (* We show that fragments of the histories may survive a crash. *)
      rewrite /post_crash_resource.
      (* History implication. *)
      iSplit.
      { iModIntro.
        iIntros (? ? ℓ t s) "frag".
        iExists p'.
        iFrame "newCrashedAt".
        (* Was [ℓ] recovered or not? *)
        destruct (p' !! ℓ) eqn:lookP'; last naive_solver.
        - iLeft. admit.
          }
      (* The preorder implication. We show that the preorders may survive a
      crash. *)
      iSplit. {
        iModIntro.
        iIntros (? ? ?) "order".
        iExists _. iFrame "newCrashedAt".
        destruct (p' !! ℓ) eqn:lookP'; last naive_solver.
        iLeft.
        rewrite /own_preorder_loc /preorders_name. simpl.
        iDestruct (own_all_preorders_singleton_frag with "allOrders order")
          as %(? & ? & ?).
        iApply (orders_frag_lookup with "fragOrders").
        rewrite /newOrders.
        apply restrict_lookup_Some.
        split; first (simplify_eq; done).
        rewrite /newAbsHists.
        rewrite /slice_of_hist.
        rewrite map_zip_with_dom.
        apply elem_of_intersection.
        split.
        - rewrite elem_of_dom. naive_solver.
        - rewrite domHistsEqOrders. rewrite elem_of_dom. naive_solver. }
      iIntros.
      rewrite /know_full_encoded_history_loc.
      rewrite /own_full_history /own_full_history_gname.
      iDestruct "history" as "[left right]".
      admit.
    }
    (* We show the state interpretation for the high-level logic. *)
    repeat iExists _.
    rewrite /own_full_history.
    iFrame "newOrders newPreds hists' newSharedLocs newCrashedAt recPreds".
    iFrameNamed.
    iSplitR.
    { iApply big_sepM2_intuitionistically_forall.
      - setoid_rewrite <- elem_of_dom.
        apply set_eq. (* elem_of_equiv_L *)
        rewrite restrict_dom_subset_L; first done.
        rewrite -domHistsEqOrders.
        apply slice_of_hist_dom_subset.
      - iModIntro.
        rewrite /newAbsHists.
        iIntros (??? slice ?).
        iPureIntro.
        apply map_lookup_zip_with_Some in slice.
        destruct slice as ([t] & hist & -> & more).
        destruct (hist !! t) as [s|]; simpl.
        { apply strictly_increasing_map_singleton. }
        { apply strictly_increasing_map_empty. } }
    admit.
  Admitted.

  (*
  Lemma nvm_reinit' (hG' : nvmFixedG Σ, nvmDeltaG Σ) n σ σ' (Hinv : invG Σ) (Hcrash : crashG Σ) Pg :
    crash_step σ σ' →
    ⊢ ⎡interp⎤ -∗
      ⎡state_interp σ n⎤ -∗
      post_crash Pg ==∗
      ∃ names : nvm_names,
        let hG := nvm_update Σ hG' Hinv Hcrash names in
          ⎡interp (hG := hG)⎤ ∗
          ⎡nvm_heap_ctx (hG := _) σ'⎤ ∗
          Pg hG.
  Proof.
    iIntros (step) "interp baseInterp".
    iMod (nvm_heap_reinit_alt _ _ _ _ Hcrash _ step with "baseInterp []") as (hnames) "(map & baseInterp & idemp)".
  Admitted.
  *)

  (* _The_ lemma for showing a recovery weakest precondition. *)
  Lemma idempotence_wpr `{hGD : nvmDeltaG Σ} s k E1 e rec Φ Φr Φc `{∀ hG, Objective (Φc hG)} :
    ⊢ WPC e @ s ; k ; E1 {{ Φ }} {{ Φc _ }} -∗
      (<obj> □ ∀ (hG' : nvmDeltaG Σ),
            Φc hG' -∗ ▷ post_crash (λ hG', (WPC rec @ s ; k; E1 {{ Φr hG' }} {{ Φc hG' }}))) -∗
      wpr s k E1 e rec Φ Φr.
  Proof.
    iStartProof (iProp _).
    iLöb as "IH" forall (e Φ hGD).

    iIntros (?). monPred_simpl.
    iIntros "wpc".
    iIntros (? ?).
    iIntros "#Hidemp".
    rewrite /wpr.
    rewrite wpr_unfold.
    rewrite /wpr_pre.
    iApply (wpc_strong_mono' with  "wpc"); try reflexivity.
    iSplit. { iIntros (?). monPred_simpl. setoid_rewrite monPred_at_fupd. auto. }
    rewrite disc_unfold_at. monPred_simpl.
    iIntros "!>".
    iIntros (??).
    iIntros "phiC".
    rewrite fupd_level_unfold_at.
    iModIntro.
    iIntros (?? step ?).
    iDestruct ("Hidemp" with "phiC") as "idemp'".
    iIntros "interp state".
    iModIntro (|={E1}=> _)%I.
    iNext.
    iIntros (??) "NC".

    (* Allocate the new ghost state. *)
    iMod (nvm_reinit _ _ _ _ _ _ _ _ with "interp state idemp'") as (names) "(interp & stateInterp & idemp)".
    { apply step. }

    iModIntro (|={E1}=> _)%I.
    iExists names.
    iFrame.
    monPred_simpl.
    iSpecialize ("IH" $! _ _ names (∅, ∅, ∅) with "[idemp] [Hidemp]").
    { done. }
    { monPred_simpl. done. }
    iApply "IH".
  Qed.

End wpr.
