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

From self Require Import view extra ipm_tactics.
From self.base Require Import primitive_laws wpr_lifting.
From self.high Require Import dprop.
From self.high Require Import resources crash_weakestpre post_crash_modality.

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
Definition slice_of_hist {A} (V : view) (σ : gmap loc (gmap time A)) :
  gmap loc (gmap time A) :=
  map_zip_with
    (λ '(MaxNat t) hist,
      match hist !! t with
        Some s => {[ 0 := s ]}
      | None => ∅ (* The None branch here is never taken. *)
      end)
    V σ.

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

(** If we have a map of points-to predicates prior to a crash and know what view
we crashed at, then we can get a map of points-to predicates for the new
heap. *)
Lemma map_points_to_to_new `{nvmBaseFixedG Σ} logHists store CV (hG hG' : nvmBaseDeltaG Σ) :
  consistent_cut CV store →
  own (@crashed_at_view_name (@nvm_base_names' _ hG')) (to_agree CV) -∗
  base.post_crash_modality.post_crash_map store hG hG' -∗
  ([∗ map] ℓ ↦ hist ∈ logHists, let hG := hG in ℓ ↦h hist) -∗
  ([∗ map] ℓ ↦ hist ∈ (slice_of_store CV logHists), let hG := hG' in ℓ ↦h hist).
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
  { apply (restrict_subseteq (dom _ CV)). }
  iDestruct (big_sepM_subseteq with "map") as "map".
  { apply (restrict_subseteq (dom _ (restrict (dom (gset _) CV) logHists))). }
  iDestruct (big_sepM2_sepM_2 with "pts map") as "map".
  { setoid_rewrite <- elem_of_dom.
    setoid_rewrite restrict_dom_subset at 2; first done.
    etrans; last apply histSubStore.
    apply subseteq_dom.
    apply restrict_subseteq. }
  iDestruct (big_sepM2_alt with "map") as "[%fall map]".
  iDestruct (big_sepM_impl_dom_subseteq _ _ _ (slice_of_store _ _) with "map []") as "[$ _]".
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
  iDestruct "right" as (CV') "[crashed [right | %left]]";
    iDestruct (crashed_at_agree with "crashed rec") as %->.
  2: {
    iExFalso.
    rewrite /slice_of_store in look'.
    apply elem_of_dom_2 in look'.
    setoid_rewrite map_zip_with_dom in look'.
    setoid_rewrite elem_of_intersection in look'.
    destruct look' as [look' _].
    apply elem_of_dom in look'.
    destruct look' as [[t] ?].
    simplify_eq. }
  iDestruct "right" as (t msg look'' lookm ?) "newPts".

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
  rewrite lookm.
  iFrame "newPts".
Qed.

Definition wpr `{nvmFixedG Σ, nvmDeltaG Σ} s k := wpr' _ s k _.

Lemma or_lost_post_crash_ts `{nvmBaseFixedG Σ, hG : nvmBaseDeltaG Σ} CV ℓ P :
  crashed_at CV -∗
  (∀ t, ⌜CV !! ℓ = Some (MaxNat t)⌝ -∗ P t) -∗
  or_lost_post_crash ℓ P.
Proof.
  iIntros "crash impl".
  iExists _. iFrame "crash".
  destruct (CV !! ℓ) as [[m]|] eqn:lookP'; last naive_solver.
  iLeft.
  iExists _. iSplit; first done.
  by iApply "impl".
Qed.

Section wpr.
  Context `{nvmFixedG Σ}.

  (* Computes the new abstract history based on the old history, the crash
  view, and the bumpers. *)
  Definition new_abs_hist (abs_hists : gmap loc (gmap time positive))
             (CV : view) (bumpers : gmap loc (positive → option positive))
    : gmap loc (gmap time positive) :=
    map_zip_with
      (λ (hist : gmap time positive) bumper,
        (default (1%positive) ∘ bumper) <$> hist)
      (slice_of_hist CV abs_hists)
      bumpers.

  Lemma new_abs_hist_dom abs_hists CV bumpers :
    dom (gset loc) (new_abs_hist abs_hists CV bumpers) ≡
    (dom _ abs_hists ∩ dom _ CV ∩ dom _ bumpers).
  Proof. rewrite 2!map_zip_with_dom. set_solver. Qed.

  Lemma new_abs_hist_lookup abs_hists CV bumpers ℓ hist :
    (new_abs_hist abs_hists CV bumpers) !! ℓ = Some hist →
    hist = ∅ ∨ ∃ s, hist = {[ 0 := s ]}.
  Proof.
    rewrite /new_abs_hist /slice_of_hist.
    do 2 setoid_rewrite map_lookup_zip_with_Some.
    intros ([?] & ? & -> & ([t] & hist' & -> & ? & ?) & ?).
    destruct (hist' !! t).
    - right. eexists _. apply map_fmap_singleton.
    - left. apply fmap_empty.
  Qed.

  Lemma holo (CV : view) ℓ t (σ : store) :
    CV !! ℓ = Some $ MaxNat t →
    consistent_cut CV σ →
    ∃ (msg : message) (hist : history),
      σ !! ℓ = Some hist ∧
      hist !! t = Some msg ∧
      slice_of_store CV σ !! ℓ = Some {[ 0 := discard_msg_views msg ]}.
  Proof.
  Admitted.

  (* FIXME: This lemmas needs more assumptions. *)
  Lemma new_abs_hist_lookup_inv abs_hists CV bumpers ℓ hist :
    (new_abs_hist abs_hists CV bumpers) !! ℓ = Some hist →
    ∃ t s s' bumper abs_hist,
      CV !! ℓ = Some (MaxNat t) ∧
      abs_hists !! ℓ = Some abs_hist ∧
      abs_hist !! t = Some s ∧
      bumpers !! ℓ = Some bumper ∧
      bumper s = Some s' ∧
      hist = {[ 0 := s' ]}.
  Proof.
  Admitted.

  (* TODO: Could maybe be upstreamed. *)
  Lemma map_subseteq_lookup_eq (m1 m2 : store) v1 v2 k :
    m1 ⊆ m2 → m1 !! k = Some v1 → m2 !! k = Some v2 → v1 = v2.
  Proof. rewrite map_subseteq_spec. naive_solver. Qed.

  (* TODO: Could maybe be upstreamed. *)
  Lemma map_Forall_subseteq P (n m : gmap loc (positive → option positive)) :
    m ⊆ n →
    map_Forall P n →
    map_Forall P m.
  Proof. rewrite map_subseteq_spec. rewrite /map_Forall. naive_solver. Qed.

  (* Given the state interpretations _before_ a crash we reestablish the
  interpretations _after_ a crash. *)
  Lemma nvm_reinit (hGD : nvmDeltaG Σ) n Pg tv σ σ' (Hinv : invGS Σ) (Hcrash : crashG Σ) :
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
    iIntros ([store p CV pIncl cut]).
    iIntros "H".
    iNamed "H".
    iIntros "(heap & authStor & %inv & pers & recov) Pg".

    (* Our [phys_hist] may contain only a subset of all the locations in
    [store]. But, those that are in [phys_hist] agree with what is in
    [store]. *)
    iAssert (⌜phys_hists ⊆ store⌝)%I as %physHistsSubStore.
    { rewrite map_subseteq_spec.
      iIntros (ℓ hist look).
      iDestruct (big_sepM_lookup with "ptsMap") as "pts"; first eassumption.
      iApply (gen_heap_valid with "heap pts"). }

    (* We need to first re-create the ghost state for the base interpretation. *)
    iMod (nvm_heap_reinit _ _ _ _ _ Hcrash with "heap pers")
      as (baseNames) "(map' & baseInterp & #persImpl & #newCrashedAt)"; try done.

    iDestruct (big_sepM2_dom with "ordered") as %domHistsEqOrders.
    iDestruct (big_sepM2_dom with "bumpMono") as %domOrdersEqBumpers.
    iDestruct (big_sepM2_dom with "bumperSome") as %domHistsEqBumpers.
    iDestruct (big_sepM2_dom with "predPostCrash") as %domPredsEqBumpers.

    (* Allocate new ghost state for the logical histories. *)
    rewrite /interp.
    set (newAbsHists := new_abs_hist abs_hists CV bumpers).
    iMod (own_full_history_gname_alloc newAbsHists)
      as (new_abs_history_name new_know_abs_history_name) "(hists' & #histFrags & knowHistories)".

    (* We freeze/persist the old authorative resource algebra. *)
    iMod (own_all_preorders_persist with "allOrders") as "#allOrders".
    iMod (own_all_bumpers_persist with "allBumpers") as "#allBumpers".
    iMod (own_update with "predicates") as "allPredicates".
    { apply auth_update_auth_persist. }
    iDestruct "allPredicates" as "#allPredicates".

    (* Some locations may be lost after a crash. For these we need to
    forget/throw away the predicate and preorder that was choosen for the
    location. *)
    set newOrders := restrict (dom (gset _) newAbsHists) orders.
    iMod (own_all_preorders_gname_alloc newOrders)
      as (new_orders_name) "[newOrders #fragOrders]".

    set newPreds := restrict (dom (gset _) newAbsHists) predicates.
    iMod (know_predicates_alloc newPreds) as
      (new_predicates_name) "[newPreds #newPredsFrag]".

    set newSharedLocs := (dom (gset _) newAbsHists) ∩ shared_locs.
    iMod (own_alloc (● (newSharedLocs : gsetUR _))) as (new_shared_locs_name) "newSharedLocs".
    { apply auth_auth_valid. done. }

    (* Allocate the new map of bumpers. *)
    set newBumpers := restrict (dom (gset _) newAbsHists) bumpers.
    iMod (own_all_bumpers_gname_alloc newBumpers)
         as (new_bumpers_name) "[newBumpers #bumpersFrag]".

    (* We are done allocating ghost state and can now present a new bundle of
    ghost names. *)
    iModIntro.
    iExists (
        NvmDeltaG _
                  (MkNvmBaseDeltaG _ Hcrash baseNames)
                  ({| abs_history_name := new_abs_history_name;
                      know_abs_history_name := new_know_abs_history_name;
                      predicates_name := _;
                      preorders_name := new_orders_name;
                      shared_locs_name := new_shared_locs_name;
                      (* exclusive_locs_name := _; *)
                      bumpers_name := new_bumpers_name;
                   |})
      ).
    iFrame "baseInterp".
    rewrite /nvm_heap_ctx.
    (* rewrite /post_crash. simpl. *)
    (* rewrite /base_post_crash. simpl. *)
    iDestruct ("Pg" $! _ (abs_hists) (store, _) _ with "persImpl map'") as "(map' & Pg)".
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
        iIntros (? ? ? ? ℓ t s) "frag".
        iApply (@or_lost_post_crash_ts with "[newCrashedAt] [frag]").
        { iFrame "newCrashedAt". }
        iIntros (? look).
        admit. }
      (* The preorder implication. We show that the preorders may survive a
      crash. *)
      iSplit. {
        iModIntro.
        iIntros (? ? ? ? ?) "order".
        iApply (@or_lost_post_crash_ts with "[newCrashedAt] [order]").
        { iFrame "newCrashedAt". }
        iIntros (? look).
        rewrite /know_preorder_loc /preorders_name. simpl.
        iDestruct (own_all_preorders_singleton_frag with "allOrders order")
          as %ordersLook.
        iApply (orders_frag_lookup with "fragOrders").
        rewrite /newOrders.
        apply restrict_lookup_Some.
        split; first (simplify_eq; done).
        rewrite /newAbsHists.
        rewrite new_abs_hist_dom.
        rewrite !elem_of_intersection.
        apply elem_of_dom_2 in look.
        apply elem_of_dom_2 in ordersLook.
        rewrite -domHistsEqBumpers domHistsEqOrders.
        set_solver. }
      iIntros.
      rewrite /know_full_encoded_history_loc.
      rewrite /own_full_history /own_full_history_gname.
      iDestruct "history" as "[left right]".
      (* We show that the predicates survives a crash. *)
      iSplit. {
        rewrite /post_crash_pred_impl.
        iModIntro. iIntros (??? ℓ ϕ) "knowPred".
        iApply (@or_lost_post_crash_ts with "[newCrashedAt] [knowPred]").
        { iFrame "newCrashedAt". }
        iIntros (t look).
        iDestruct (own_all_preds_pred with "allPredicates knowPred") as (? predsLook) "H".
        iApply (predicates_frag_lookup with "newPredsFrag").
        rewrite /newPreds.
        (* FIXME: There is a later in the way. *)
        admit. }
      (* We show that the bumpers survive a crash. *)
      iSplit. {
        rewrite /post_crash_bumper_impl.
        iIntros "!>" (???? ℓ bumper) "knowBumper".
        iApply (@or_lost_post_crash_ts with "[newCrashedAt] [knowBumper]").
        { iFrame "newCrashedAt". }
        iIntros (t look).
        rewrite /know_bumper.
        iDestruct "knowBumper" as "[$ knowBumper]".

        iDestruct (own_valid_2 with "allBumpers knowBumper") as %V.
        eapply auth_valid_to_agree_singleton_l in V.

        iApply (bumpers_frag_lookup with "bumpersFrag").
        rewrite /newBumpers.
        apply restrict_lookup_Some.
        split; first (simplify_eq; done).
        rewrite /newAbsHists.
        rewrite new_abs_hist_dom.
        rewrite domHistsEqOrders domOrdersEqBumpers.
        apply elem_of_dom_2 in look.
        apply elem_of_dom_2 in V.
        set_solver. }
      admit.
    }
    (* We show the state interpretation for the high-level logic. *)
    repeat iExists _.
    rewrite /own_full_history.
    iFrame "newOrders newPreds hists' newSharedLocs newCrashedAt".
    iFrame "ptsMap".
    iFrame "newBumpers".
    (* We show that the abstract states are still ordered. *)
    iSplitR.
    { iApply big_sepM2_intro.
      - setoid_rewrite <- elem_of_dom.
        apply set_eq.
        rewrite restrict_dom_subset_L; first done.
        rewrite -domHistsEqOrders.
        rewrite new_abs_hist_dom.
        set_solver.
      - iModIntro.
        iIntros (ℓ hist order [->|[? ->]]%new_abs_hist_lookup slice) "!%".
        * apply increasing_map_empty.
        * apply increasing_map_singleton. }
    (* We show that the encoded predicates still hold for the new abstract
    history. *)
    iSplitR "". {
      (* We use the old predsHold to show the new predsHold. There are more
      locations in the old abstract state so the new predsHold is over a subset
      of locations. *)
      iDestruct (big_sepM_impl_dom_subseteq with "predsHold []") as "[$ temp]".
      { rewrite new_abs_hist_dom. set_solver. }
      iModIntro.
      iIntros (ℓ encHist newEncHist absHistLook newAbsHistLook).

      pose proof (new_abs_hist_lookup_inv _ _ _ _ _ newAbsHistLook)
        as (t & s & s' & bumper & hist & CVLook & absHistsLook & histLook &
            bumpersLook & bumperAp & histEq).
      (* Can we avoid introducing [encHist] altogether? *)
      assert (encHist = hist) as -> by congruence.

      iIntros "(%pred & %physHist & %physHistLook & %predsLook & encs)".
      (* assert (is_Some (CV !! ℓ)) as [[t] CVLook]. *)
      (* { apply elem_of_dom_2 in newAbsHistLook. *)
      (*   rewrite /newAbsHists in newAbsHistLook. *)
      (*   setoid_rewrite new_abs_hist_dom in newAbsHistLook. *)
      (*   apply elem_of_dom. *)
      (*   set_solver. } *)
      epose proof (holo _ _ _ _ CVLook cut) as (msg & physHist' & storeLook & hi & ho).
      (* FIXME: Can we avoid introducting [physHist] altogether? *)
      assert (physHist = physHist') as <- by eauto using map_subseteq_lookup_eq.
      iExists pred, {[ 0 := discard_msg_views msg]}.
      iPureGoal. {
        rewrite /slice_of_store.
        apply slice_of_store_lookup_Some_singleton in ho.
        destruct ho as (tt & ?tempHist & eq & ? & ?).
        assert (physHist = tempHist) as <- by eauto using map_subseteq_lookup_eq.
        apply map_lookup_zip_with_Some.
        exists (MaxNat tt), physHist.
        rewrite -lookup_fmap in H1.
        apply lookup_fmap_Some in H1.
        destruct H1 as (msg' & eq' & ->).
        split_and!; [| done | done].
        destruct msg, msg'. rewrite /discard_msg_views. simpl.
        simpl in eq'.
        congruence. }
      iPureGoal. {
        rewrite /newPreds.
        apply restrict_lookup_Some_2; first done.
        apply elem_of_dom. done. }
      rewrite histEq.
      rewrite big_sepM2_singleton.

      (* We look up the relevant predicate in [encs]. *)
      iDestruct (big_sepM2_lookup with "encs") as "flip"; [done | done | ].

      (* We now looks up in [predPostCrash]. *)
      iDestruct (big_sepM2_lookup with "predPostCrash") as "#hi";
        [apply predsLook | apply bumpersLook | ].
      iSpecialize ("hi" $! s (msg_val msg)).

      rewrite /encoded_predicate_holds.
      iDestruct "flip" as (P eq) "PHolds".

      admit. }

    (* Show that the bumpers are still monotone. *)
    iSplitR "".
    { iApply (big_sepM2_impl_subseteq with "bumpMono").
      { apply restrict_subseteq. }
      { apply restrict_subseteq. }
      { rewrite /newOrders /newBumpers.
        rewrite 2!restrict_dom.
        rewrite -domOrdersEqBumpers.
        set_solver. } }
    iSplitR "". {
      iApply (big_sepM2_impl_subseteq with "predPostCrash").
      { apply restrict_subseteq. }
      { apply restrict_subseteq. }
      { rewrite /newOrders /newBumpers.
        rewrite 2!restrict_dom.
        rewrite -domPredsEqBumpers.
        set_solver. } }
    iSplitR "". {
      iPureIntro.
      eapply map_Forall_subseteq; last apply bumperBumpToValid.
      apply restrict_subseteq. }
    (* bumperSome *)
    iSplitR "". {
      iApply big_sepM2_forall.
      iSplit.
      { iPureIntro.
        setoid_rewrite <- elem_of_dom.
        apply set_eq.
        rewrite restrict_dom_subset_L; first done.
        rewrite new_abs_hist_dom.
        set_solver. }
      (* iIntros (ℓ hist bumper [empty | (s' & histEq)]%new_abs_hist_lookup look2). *)
      iIntros (ℓ hist bumper look look2).
      apply new_abs_hist_lookup_inv in look.
      destruct look as (? & ? & ? & ? & hist' & ? & ? & ? & ? & ? & histEq).
      (* We handle the empty case here, but we should be able to rule it out. *)
      (* { rewrite empty. iPureIntro. apply map_Forall_empty. } *)
      rewrite histEq.
      rewrite map_Forall_singleton.
      assert (bumpers !! ℓ = Some bumper). { admit. }
      iDestruct (big_sepM2_lookup with "bumperSome") as %i; [done|done|].
      (* Note: We probably have to use [bumpMono] as well. *)

      admit.
    }
    (* We show that the shared location still satisfy that heir two persist
    views are equial. *)
    { iPureIntro.
      intros ℓ hist [look roflcopter]%restrict_lookup_Some.
      intros t msg histLook.
      epose proof (slice_of_store_lookup_Some _ _ _ _ _ _ look histLook)
        as (? & ? & [????] & ? & ? & ? & ? & -> & ?).
      reflexivity. }
  Admitted.


  (*
  Lemma nvm_reinit' (hG' : nvmFixedG Σ, nvmDeltaG Σ) n σ σ' (Hinv : invGS Σ) (Hcrash : crashG Σ) Pg :
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
    monPred_simpl.
    iIntros (??).
    iIntros "phiC".
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
