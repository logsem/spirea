From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import gset.
From iris_named_props Require Import named_props.

From self Require Import extra solve_view_le encode_relation map_extra view_slice ipm_tactics.

From self.lang Require Import syntax tactics lemmas.

From self.base Require Import generational_resources primitive_laws.

From self.high Require Import monpred_simpl protocol locations crash_weakestpre weakestpre.
From self.high.modalities Require Import fence_sync_atomic.
From self.high.lib Require Import abstract_state increasing_map.

From self Require Export lang.
From self.high Require Export dprop.

Set Default Proof Using "Type*".

Section wp_na.
  Context `{AbstractState ST}.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, PerennialG Σ}.

  Implicit Types (ℓ : loc) (σ : ST) (prot : LocationProtocol ST).
  
  Lemma wp_load_na ℓ q ss s Q prot positive E :
    last ss = Some s →
    {{{ mapsto_na ℓ prot q ss ∗
        (<obj> (∀ v, prot.(p_full) s v -∗ Q v ∗ prot.(p_full) s v)) }}}
      !_NA (Val $ LitV $ LitLoc ℓ) @ positive; E
    {{{ v, RET v; mapsto_na ℓ prot q ss ∗ Q v }}}.
  Proof.
    intros sLast Φ.
    iModel.
    (* We destruct the exclusive points-to predicate. *)
    iIntros "(pts & pToQ)".
    rewrite /mapsto_na.
    iDestruct "pts" as (?tP ?tS offset SV absHist msg ?) "pts". iNamed "pts".
    iNamed "locationProtocol".
    iDestruct "inThreadView" as %inThreadView.
    rewrite monPred_at_wand. simpl.
    iIntros (TV' incl) "Φpost".
    rewrite monPred_at_later.
    iApply wp_unfold_at.
    iIntros ([[SV' PV] BV] incl2) "#val".

    (* We need to get the points-to predicate for [ℓ]. This is inside [interp]. *)
    iApply wp_extra_state_interp.
    { done. }
    { by apply prim_step_load_no_fork. }
    iNamed 1.
    iDestruct (own_all_preds_pred with "full_predicates knowFullPred") as
      (pred predsLook) "#predsEquiv".
    simpl.
    iDestruct (full_map_full_entry with "history [$]") as %absHistlook.

    iDestruct (big_sepM2_dom with "predsFullReadHold") as %domPhysHistEqAbsHist.
    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
    { rewrite -elem_of_dom domPhysHistEqAbsHist elem_of_dom. done. }

    iDestruct (offset_loc_offset_auth_agree with "offset offsets") as %?.

    iDestruct (big_sepM2_lookup_acc with "predsFullReadHold") as "[predMap predsFullReadHold]".
    { done. } { done. }
    iDestruct "predMap" as (pred' offset' ????) "predMap".
    simplify_map_eq.

    iDestruct (big_sepM_lookup_acc with "ptsMap") as "[pts ptsMap]"; first done.

    iAssert (∃ OCV, crashed_at_offset OCV ∗ ⌜ OCV !!0 ℓ = offset ⌝)%I as (OCV) "[#crashed_at_offset <-]".
    { iDestruct "offset" as (?) "(? & ? & %)".
      iExists _.
      by iFrame "#". }
    
    iApply (wp_load_alt (extra := {| extra_state_interp := True |}) with "[$pts $crashed_at_offset $val]").
    iNext. iIntros (tT msg') "[pts (%look & %gt)]".
    simpl.
    iDestruct ("ptsMap" with "pts") as "ptsMap".
    iFrame "val".

    assert (SV ⊑ SV') as svInclSv'. (* This will come in handy. *)
    { destruct TV as [[??]?]. destruct TV' as [[??]?].
      etrans; first apply inThreadView.
      etrans; first apply incl; apply incl2. }

    (* We need to conclude that the only write we could read is [tS]. I.e., that
    [tT + offset = tS]. *)
    assert (tS - (OCV !!0 ℓ) ≤ SV' !!0 ℓ) as tSle.
    { etrans; first done. by f_equiv. }
    assert (tS ≤ tT) as lte by lia.
    iDestruct (big_sepM2_dom with "predMap") as %domEq.
    assert (is_Some (absHist !! tT)) as HI.
    { apply elem_of_dom.
      erewrite <- dom_fmap_L.
      erewrite <- domEq.
      apply elem_of_dom.
      naive_solver. }
    assert (tT = tS) as ->.
    { apply Nat.lt_eq_cases in lte. destruct lte as [lt|]; last done.
      eassert _ as eq. { apply (nolater (tT)). lia. }
      (* pose proof (nolater tT lt) as eq. *)
      rewrite eq in HI. inversion HI as [? [=]]. }
    clear lte HI.

    iDestruct (auth_map_map_lookup_agree with "[$] physMsg") as %eq.
    { done. } { done. }
    subst.

    iDestruct (big_sepM2_lookup_acc with "predMap") as "[predHolds predMap]";
      first done.
    { rewrite lookup_fmap. rewrite lookupV. done. }
    iDestruct (ghost_map_lookup with "naView knowSV") as %naViewLook.
    rewrite naViewLook.
    simpl.
    rewrite decide_True.
    2: { split; first lia.
         rewrite -not_elem_of_dom domEq not_elem_of_dom lookup_fmap fmap_None.
         apply nolater.
         lia. }
    iDestruct (predicate_holds_phi with "predsEquiv predHolds") as "phi";
      first done.
    rewrite monPred_at_objectively.
    iSpecialize ("pToQ" $! (SV, msg_persisted_after_view msg, ∅) (msg_val msg)).
    rewrite monPred_at_wand.
    iDestruct ("pToQ" with "[] phi") as "[Q phi]".
    { iPureIntro. reflexivity. }
    (* Reinsert into the predicate map. *)
    iDestruct ("predMap" with "[phi]") as "predMap".
    { iApply (predicate_holds_phi with "predsEquiv phi"). done. }
    (* Reinsert into the map. *)
    iDestruct ("predsFullReadHold" with "[predMap]") as "predsFullReadHold".
    { iExistsN.
      rewrite naViewLook.
      by iFrame. }
    iSplitL "Q hist knowSV Φpost"; last first.
    { iExistsN.
      iFrame.
      (* TODO: when we eventually upgrade iris version, maybe [iFrame] will be usable again *)
      repeat (iSplit;
              first solve [
                  iPureIntro; done |
                  iAssumption ]).
      iAssumption. }
    iSplit; first done.
    simpl.
    iApply monPred_mono.
    2: {
      iApply "Φpost".
      iSplitR "Q".
      2: {
        simplify_eq.
        rewrite /msg_to_tv.
        iApply monPred_mono; last iApply "Q".
        etrans; last done.
        done. }
      iExistsN.
      (* iPureGoal; first done. *)
      iSplitPure; first apply sLast.
      simpl.
      iSplit. { rewrite /know_protocol. iFrameNamed. }
      iFrameNamed.
      iPureIntro. etrans; eassumption. }
    done.
  Qed.
End wp_na.
