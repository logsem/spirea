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

Record nvm_high_names := {
  name_abs_history : gname;
  name_know_abs_history : gname;
  name_predicates : gname;
  name_preorders : gname;
  name_shared_locs : gname;
}.

Definition nvm_high_get_names Σ (hG : nvmHighG Σ) : nvm_high_names :=
  {| name_abs_history := abs_history_name;
     name_know_abs_history := know_abs_history_name;
     name_predicates := predicates_name;
     name_preorders := preorders_name;
     name_shared_locs := shared_locs_name;
  |}.

Canonical Structure nvm_high_namesO := leibnizO nvm_high_names.

(** Given an [hG : nvmG Σ], update the fields per the information in the rest of
the arguments. In particular, all the gnames in [names] replaces the
corresponding gnames in [hG]. *)
Definition nvm_high_update Σ (hG : nvmHighG Σ) (names : nvm_high_names) :=
  {| (* Ghost names *)
     abs_history_name := names.(name_abs_history);
     know_abs_history_name := names.(name_know_abs_history);
     predicates_name := names.(name_predicates);
     preorders_name := names.(name_preorders);
     shared_locs_name := names.(name_shared_locs);
     (* Functors *)
     ra_inG := hG.(@ra_inG _);
     ra_inG' := hG.(@ra_inG' _);
     abs_histories := hG.(@abs_histories _);
     preordersG := hG.(@preordersG _);
     shared_locsG := hG.(@shared_locsG _);
  |}.

Record nvm_names := {
  name_base_names : nvm_base_names; (* Names used by the base logic. *)
  name_high_names : nvm_high_names; (* Names used by the high-level logic. *)
}.

Definition nvm_get_names Σ (hG : nvmG Σ) : nvm_names :=
  {| name_base_names := nvm_base_get_names _ nvmG_baseG;
     name_high_names := nvm_high_get_names _ nvmG_highG |}.

Canonical Structure nvm_namesO := leibnizO nvm_names.

(** Given an [hG : nvmG Σ], update the fields per the information in the rest of
the arguments. In particular, all the gnames in [names] replaces the
corresponding gnames in [hG]. *)
Definition nvm_update Σ (hG : nvmG Σ) (Hinv : invG Σ) (Hcrash : crashG Σ) (names : nvm_names) :=
  {| nvmG_baseG := nvm_base_update _ hG.(@nvmG_baseG _) Hinv Hcrash names.(name_base_names);
     nvmG_highG := nvm_high_update _ hG.(@nvmG_highG _) names.(name_high_names) |}.

(* The recovery WP is parameterized by two predicates: [Φ] is the postcondition
   for normal non-crashing execution and [Φr] is the postcondition satisfied in
   case of a crash. *)
Definition wpr_pre Σ (s : stuckness) (k : nat)
    (wpr : nvmG Σ -d> coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
                     (nvmG Σ -d> val -d> dPropO Σ) -d> dPropO Σ) :
  nvmG Σ -d> coPset -d> expr -d> expr -d> (val -d> dPropO Σ) -d>
  (nvmG Σ -d> val -d> dPropO Σ) -d> dPropO Σ :=
  λ hG E e e_rec Φ Φr,
  (WPC e @ s ; k; E
     {{ Φ }}
     {{ ∀ σ σ' (HC : crash_prim_step nvm_crash_lang σ σ') n,
        ⎡ interp -∗ state_interp σ n ={E}=∗ ▷ ∀ (Hc1 : crashG Σ) q, NC q ={E}=∗
          ∃ (names : nvm_names),
            let hG := (nvm_update Σ hG _ Hc1 names) in
              state_interp σ' 0 ∗
              (monPred_at (wpr hG E e_rec e_rec (λ v, Φr hG v) Φr) (∅, ∅, ∅)) ∗
              NC q ⎤
     }})%I.

Local Instance wpr_pre_contractive {Σ} s k: Contractive (wpr_pre Σ s k).
Proof.
  rewrite /wpr_pre. intros ??? Hwp ??????.
  apply wpc_ne; eauto;
  repeat (f_contractive || f_equiv). apply Hwp.
Qed.

Definition wpr_def {Σ} (s : stuckness) k := fixpoint (wpr_pre Σ s k).
Definition wpr_aux {Σ} : seal (@wpr_def Σ). by eexists. Qed.
Definition wpr' {Σ} := (@wpr_aux Σ).(unseal).
Lemma wpr_eq {Σ} : @wpr' Σ = @wpr_def Σ.
Proof. rewrite /wpr'. rewrite wpr_aux.(seal_eq). done. Qed.

Lemma wpr_unfold `{hG : nvmG Σ} st k E e rec Φ Φc :
  wpr' st k hG E e rec Φ Φc ⊣⊢ wpr_pre Σ st k (wpr' st k) hG E e rec Φ Φc.
Proof.
  rewrite wpr_eq. rewrite /wpr_def.
  apply (fixpoint_unfold (wpr_pre Σ st k)).
Qed.

(* For each location in [p] pick the message in the store that it specifies. *)
Definition slice_of_hist (p : view) (σ : gmap loc (gmap time (message * positive))) : gmap loc (gmap time (message * positive)) :=
  map_zip_with
    (λ '(MaxNat t) hist,
      match hist !! t with
        Some (msg, s) => {[ 0 := (discard_msg_views msg, s) ]}
      | None => ∅ (* The None branch here should never be taken. *)
      end)
    p σ.

Lemma map_points_to_to_new {Σ} hists store p' (hG hG' : nvmBaseG Σ) :
  consistent_cut p' store →
  own (@recovered_view_name _ hG') (to_agree p') -∗
  base.post_crash_modality.post_crash_map store hG hG' -∗
  ([∗ map] ℓ ↦ hist ∈ hists, let hG := hG in ℓ ↦h (fst <$> hist)) -∗
  ([∗ map] ℓ ↦ hist ∈ (slice_of_hist p' hists), let hG := hG' in ℓ ↦h (fst <$> hist)).
Proof.
  iIntros (cut) "#rec [impl map] pts".
  iAssert (⌜((λ (hist : gmap _ _), fst <$> hist) <$> hists) ⊆ store⌝)%I as %foo.
  {
    (* We need to prove this. *)
    admit. }
  iAssert (⌜dom (gset _) hists ⊆ dom _ store⌝)%I as %histSubStore.
  { rewrite elem_of_subseteq. iIntros (ℓ).
    rewrite !elem_of_dom. iIntros ([hist look]).
    iDestruct (big_sepM_lookup with "pts") as "pts"; first apply look.
    iExists _. iApply "impl"; done. }
  (* Throw away the points-to predicates that did not survive the crash. *)
  iDestruct (big_sepM_subseteq with "pts") as "pts".
  { apply (restrict_subseteq (dom _ p')). }
  iDestruct (big_sepM_subseteq with "map") as "map".
  { apply (restrict_subseteq (dom _ (restrict (dom (gset _) p') hists))). }
  iDestruct (big_sepM_sepM2_2 with "pts map") as "map".
  { setoid_rewrite <- elem_of_dom.
    setoid_rewrite restrict_dom_subset at 2; first done.
    etrans; last apply histSubStore.
    apply subseteq_dom.
    apply restrict_subseteq. }
  iDestruct (big_sepM2_alt with "map") as "[%fall map]".
  iApply (big_sepM_impl_sub with "map").
  { (* apply map_zip_with_dom_fst *)
    (* rewrite /map_zip. *)
    admit. (* We need lemmas about dom of map_zip *) }
    (* etrans. last eapply map_zip_with_dom last eapply map_zip_with_dom_fst. } *)
  iIntros "!>" (ℓ [? msg] hy look look') "[pts disj]".
  iDestruct "disj" as (qc pc) "(left & right & %sum)".
  simpl.
  rewrite /post_crash_modality.if_non_zero.
  destruct (decide (0 < qc)%Qc).
  { iDestruct (mapsto_ne with "pts left") as %H. exfalso. by apply H. }
  iDestruct "left" as %->.
  rewrite Qcplus_0_l in sum.
  rewrite sum.
  simpl.
  rewrite /post_crash_modality.mapsto_post_crash.
  iDestruct "right" as "[right | left]".
  2: {
    iExFalso.
    rewrite /slice_of_hist in look'.
    apply elem_of_dom_2 in look'.
    apply map_zip_with_dom_fst in look'.
    apply elem_of_dom in look'.
    destruct look' as [[t] ?].
    iApply "left". iExists _. iFrame "rec".
    rewrite -map_Forall_singleton.
    done. }
  iDestruct "right" as (t msg' look'') "H".
  apply map_lookup_zip_with_Some in look'.
  destruct look' as ([?t] & hist & eq & ?look & ?look).
  (* FIXME: Use consistent_cut and the foo hypothesis that relates store to hists. *)
Admitted.

(* Lemma slice_of_hist_lookup_Some *)
(*   consistent_cut p' store *)
(*   slice_of_hist p hists !! ℓ = Some hist *)

Definition wpr `{nvmG Σ} s k := wpr' s k _.

Section wpr.
  Context `{hG : nvmG Σ}.

  Lemma slice_of_hist_dom_subset p hists :
    dom (gset loc) (slice_of_hist p hists) ⊆ dom (gset loc) hists.
  Proof.
    rewrite /slice_of_hist.
    intros l.
    rewrite !elem_of_dom.
    intros [??].
    apply map_lookup_zip_with_Some in H.
    destruct H as (? & ? & ? & ? & ?).
    eexists _. done.
  Qed.

  (* Given the state interpretations _before_ a crash we reestablish the
  interpretations _after_ a crash. *)
  Lemma nvm_reinit (hG' : nvmG Σ) n Pg tv σ σ' (Hinv : invG Σ) (Hcrash : crashG Σ) :
    crash_step σ σ' →
    ⊢ interp -∗
      state_interp σ n -∗
      (post_crash Pg) tv ==∗
      ∃ names : nvm_names,
        let hG := nvm_update Σ hG' Hinv Hcrash names in
          interp (hG := hG) ∗
          nvm_heap_ctx (hG := _) σ' ∗
          Pg hG (∅, ∅, ∅).
  Proof.
    (* iIntros (step). *)
    iIntros ([store p p' pIncl cut]).
    (* iNamed 1. *)
    iIntros "H".
    iNamed "H".
    iIntros "(heap & authStor & inv & pers & recov) Pg".

    (* We need to first re-create the ghost state for the base interpretation. *)
    iMod (nvm_heap_reinit _ _ _ _ _ Hcrash with "heap inv pers")
      as (baseNames) "(map' & interp' & #persImpl & #rec)"; try done.

    iDestruct (big_sepM2_dom with "ordered") as %domHistsEqOrders.

    (* Allocate new ghost state for the logical histories. *)
    rewrite /interp.
    set newHists := slice_of_hist p' hists.
    iMod (own_full_history_gname_alloc ((λ h : abs_history (message * positive), snd <$> h) <$> newHists)) as (new_abs_history_name new_know_abs_history_name) "[hists' knowHistories]".

    (* Some locations may be lost after a crash. For these we need to
    forget/throw away the predicate and preorder that was choosen for the
    location. *)
    set newOrders := restrict (dom (gset _) newHists) orders.
    iMod (own_all_preorders_gname_alloc newOrders) as (new_orders_name) "newOrders".

    set newPreds := restrict (dom (gset _) newHists) preds.
    iMod (know_predicates_alloc newPreds) as (new_predicates_name) "newPreds".

    set newSharedLocs := (dom (gset _) newHists) ∩ shared_locs.
    iMod (own_alloc (● (newSharedLocs : gsetUR _))) as (new_shared_locs_name) "newSharedLocs".
    { apply auth_auth_valid. done. }

    (* We are done allocating ghost state and can now present a new bundle of
    ghost names. *)
    iModIntro.
    iExists
      ({| name_base_names := baseNames;
          name_high_names := {| name_abs_history := new_abs_history_name;
                                name_know_abs_history := new_know_abs_history_name;
                                name_predicates := new_predicates_name;
                                name_preorders := new_orders_name;
                                name_shared_locs := new_shared_locs_name;
                             |} |}).
    iFrame "interp'".
    rewrite /nvm_heap_ctx.
    (* iFrame. *)
    rewrite /post_crash. simpl.
    rewrite /base_post_crash. simpl.
    iDestruct ("Pg" $! _ (((λ h : abs_history (message * positive), snd <$> h) <$> hists)) (store, _) _ with "persImpl map'") as "(map' & Pg)".
    simpl.
    iDestruct
      (map_points_to_to_new hists _ _ _ (nvm_base_update Σ nvmG_baseG Hinv Hcrash baseNames)
         with "rec map' ptsMap") as "ptsMap"; first done.
    rewrite /post_crash_map.
    iDestruct ("Pg" with "[history knowHistories]") as "[$ WHAT]".
    { simpl.
      iSplit.
      { admit. }
      iSplitL "history".
      (* rewrite /know_full_encoded_history_loc. *)
      (* rewrite /own_full_history /own_full_history_gname. *)
      (* iDestruct "history" as "[left right]". *)
      (* iDestruct (ghost_map_lookup with "left [$]") as "HY". *)
      { iIntros.
        rewrite /know_full_encoded_history_loc.
        rewrite /own_full_history /own_full_history_gname.
        iDestruct "history" as "[left right]".
        iDestruct (ghost_map_lookup with "left [$]") as "HY".
        iApply "HY". }
      admit.
    }
    (* We show the state interpretation for the high-level logic. *)
    iExists _, _, _, _.
    rewrite /own_full_history.
    iFrame "newOrders".
    iFrame "newPreds".
    iFrame "hists'".
    iSplitL "ptsMap".
    { rewrite /newHists. iFrame. }
    iSplitR.
    { iApply big_sepM2_intuitionistically_forall.
      - setoid_rewrite <- elem_of_dom.
        apply set_eq. (* elem_of_equiv_L *)
        rewrite restrict_dom_subset_L; first done.
        rewrite -domHistsEqOrders.
        apply slice_of_hist_dom_subset.
      - iModIntro.
        rewrite /newHists.
        iIntros (??? slice ?).
        iPureIntro.
        apply map_lookup_zip_with_Some in slice.
        destruct slice as ([t] & hist & -> & more).
        destruct (hist !! t) as [[??]|]; simpl.
        { rewrite map_fmap_singleton. simpl. apply increasing_map_singleton. }
        { rewrite fmap_empty. apply increasing_map_empty. } }

    admit.
  Admitted.

  (*
  Lemma nvm_reinit' (hG' : nvmG Σ) n σ σ' (Hinv : invG Σ) (Hcrash : crashG Σ) Pg :
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
  Lemma idempotence_wpr s k E1 e rec Φ Φr Φc `{∀ hG, Objective (Φc hG)} :
    ⊢ WPC e @ s ; k ; E1 {{ Φ }} {{ Φc hG }} -∗
      (<obj> □ ∀ (hG' : nvmG Σ),
            Φc hG' -∗ ▷ post_crash (λ hG', (WPC rec @ s ; k; E1 {{ Φr hG' }} {{ Φc hG' }}))) -∗
      wpr s k E1 e rec Φ Φr.
  Proof.
    iStartProof (iProp _).
    iLöb as "IH" forall (e Φ hG).

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
    iSpecialize ("IH" $! _ _ (nvm_update Σ hG iris_invG Hc1 names) (∅, ∅, ∅) with "[idemp] [Hidemp]").
    { done. }
    { monPred_simpl. done. }
    iApply "IH".
  Qed.

End wpr.
