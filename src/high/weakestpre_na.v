(* Weakest precondition rules for non-atomic locations. *)

From stdpp Require Import gmap.
From iris.program_logic Require weakestpre.

From stdpp Require Import countable numbers gmap.
From iris Require Import invariants.
From iris.proofmode Require Import tactics monpred.
From iris.algebra Require Import gmap gset excl auth.
From iris.program_logic Require weakestpre.
From iris.heap_lang Require Import locations.
From iris_named_props Require Import named_props.

From self.algebra Require Import ghost_map.
From self Require Export extra ipm_tactics encode_relation view.
From self.lang Require Export lang lemmas tactics syntax.
From self.base Require Import primitive_laws.
From self.high Require Import dprop resources crash_weakestpre lifted_modalities
     monpred_simpl modalities protocol.

Section wp_na_rules.
  Context `{AbstractState ST}.
  Context `{!nvmFixedG Σ, hG : nvmDeltaG Σ}.

  Implicit Types (ℓ : loc) (s : ST) (ϕ : ST → val → nvmDeltaG Σ → dProp Σ).

  Lemma wp_load_na ℓ (b : bool) q ss s Q ϕ `{!LocationProtocol ϕ} positive E :
    last ss = Some s →
    {{{ mapsto_na b ℓ q ss ∗
        know_protocol ℓ ϕ ∗
        (<obj> (∀ v, ϕ s v _ -∗ Q v ∗ ϕ s v _)) }}}
      Load (Val $ LitV $ LitLoc ℓ) @ positive; E
    {{{ v, RET v; mapsto_na b ℓ q ss ∗ Q v }}}.
  Proof.
    intros sLast Φ.
    iStartProof (iProp _). iIntros (TV).
    (* We destruct the exclusive points-to predicate. *)
    iIntros "(pts & temp & pToQ)".
    iNamed "temp".
    iDestruct "pts" as (?tP ?tS SV absHist msg) "pts". iNamed "pts".
    iDestruct "inThreadView" as %inThreadView.
    rewrite monPred_at_wand. simpl.
    iIntros (TV' incl) "Φpost".
    rewrite monPred_at_later.
    rewrite wp_eq /wp_def.
    rewrite wpc_eq. simpl.
    iIntros ([[SV' PV] BV] incl2) "#val".
    rewrite monPred_at_pure.
    iApply program_logic.crash_weakestpre.wp_wpc.

    (* We need to get the points-to predicate for [ℓ]. This is inside [interp]. *)
    iApply wp_extra_state_interp.
    { done. }
    { by apply prim_step_load_no_fork. }
    iNamed 1.
    iDestruct (own_all_preds_pred with "predicates knowPred") as
      (pred predsLook) "#predsEquiv".
    iDestruct (own_full_history_agree with "[$] [$]") as %absHistlook.

    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistEqAbsHist.
    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
    { rewrite -elem_of_dom domPhysHistEqAbsHist elem_of_dom. done. }

    iDestruct (big_sepM2_lookup_acc with "predsHold") as "[predMap predsHold]".
    { done. } { done. }
    iDestruct "predMap" as (pred' predsLook') "predMap".
    assert (pred = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
    clear predsLook'.

    iDestruct (big_sepM_lookup_acc with "ptsMap") as "[pts ptsMap]"; first done.
    iApply (wp_load (extra := {| extra_state_interp := True |}) with "[$pts $val]").
    iNext. iIntros (tT v' msg') "[pts (%look & %msgVal & %gt)]".
    simpl.
    iDestruct ("ptsMap" with "pts") as "ptsMap".
    iFrame "val".

    assert (SV ⊑ SV') as svInclSv'. (* This will come in handy. *)
    { destruct TV as [[??]?]. destruct TV' as [[??]?].
      etrans; first apply inThreadView.
      etrans; first apply incl; apply incl2. }

    (* We need to conclude that the only write we could read is [tS]. I.e., that
    [tT = tS]. *)
    assert (tS ≤ SV' !!0 ℓ) as tSle.
    { etrans; first done. f_equiv. done. }
    assert (tS ≤ tT) as lte.
    { etrans; first done. apply gt. }
    iDestruct (big_sepM2_dom with "predMap") as %domEq.
    assert (is_Some (absHist !! tT)) as HI.
    { apply elem_of_dom.
      erewrite <- dom_fmap_L.
      erewrite <- domEq.
      apply elem_of_dom.
      naive_solver. }
    assert (tT = tS) as ->.
    { apply Nat.lt_eq_cases in lte. destruct lte as [lt|]; last done.
      pose proof (nolater tT lt) as eq.
      rewrite eq in HI. inversion HI as [? [=]]. }
    assert (absHist !! tS = Some s) as lookS.
    { rewrite -sLast.
      apply map_slice_lookup_hi in slice.
      rewrite slice.
      done. }
    clear lte HI.

    iDestruct (auth_map_map_lookup_agree with "[$] [$]") as %eq.
    { done. } { done. }
    subst.

    iDestruct (big_sepM2_lookup_acc with "predMap") as "[predHolds predMap]";
      first done.
    { rewrite lookup_fmap. rewrite lookS. done. }
    iDestruct (ghost_map_lookup with "naView knowSV") as %->.
    simpl.
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
    iDestruct ("predsHold" with "[predMap]") as "predsHold". { naive_solver. }

    iSplitR "ptsMap physHist allOrders ordered predsHold history predicates
             sharedLocs exclusiveLocs crashedAt allBumpers bumpMono predPostCrash
             sharedLocsHistories naView"; last first.
    { repeat iExists _. iFrameNamed. done. }
    iSplit; first done.
    iApply "Φpost".
    iSplitR "Q".
    2: {
      simplify_eq.
      rewrite /msg_to_tv.
      iApply monPred_mono; last iApply "Q".
      repeat split.
      - done.
      - destruct TV as [[??]?]. destruct TV' as [[??]?].
        etrans; first apply inThreadView.
        etrans; first apply incl.
        apply incl2.
      - apply view_empty_least. }
    iExists _, _, _, _, _.
    iFrameNamed.
    iSplit.
    { iPureIntro. etrans. eassumption. etrans. eassumption. eassumption. }
    iApply monPred_mono; last iApply "pers".
    by etrans.
  Qed.

  Lemma wp_store_na ℓ b ss v s__last s ϕ `{!LocationProtocol ϕ} st E :
    last ss = Some s__last →
    s__last ⊑ s →
    {{{ mapsto_na b ℓ 1 ss ∗ know_protocol ℓ ϕ ∗ ϕ s v _ }}}
      #ℓ <- v @ st; E
    {{{ RET #(); mapsto_na b ℓ 1 (ss ++ [s]) }}}.
  Proof.
    intros last stateGt Φ.
    iStartProof (iProp _). iIntros (TV).
    iIntros "(pts & temp & phi)".
    iNamed "temp".
    iDestruct "pts" as (?tP ?tS SV absHist msg) "pts". iNamed "pts".
    iDestruct "inThreadView" as %inThreadView.

    rewrite monPred_at_wand. simpl.
    iIntros (TV' incl) "Φpost".
    rewrite monPred_at_later.
    rewrite wp_eq /wp_def.
    rewrite wpc_eq. simpl.
    iIntros ([[SV' PV] BV] incl2) "#val".
    rewrite monPred_at_pure.
    iApply program_logic.crash_weakestpre.wp_wpc.

    (* We need to get the points-to predicate for [ℓ]. This is inside [interp]. *)
    iApply wp_extra_state_interp.
    { done. } { by apply prim_step_store_no_fork. }
    iNamed 1.
    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    assert (SV ⊑ SV') as svInclSv'.
    { destruct TV as [[??]?]. destruct TV' as [[??]?].
      etrans; first apply inThreadView.
      etrans; first apply incl.
      apply incl2. }

    (* _Before_ we load the points-to predicate we deal with the predicate ϕ. We
    do this before such that the later that arrises is stripped off when we take
    the step. *)
    iDestruct (own_all_preds_pred with "predicates knowPred")
      as (pred predsLook) "#predsEquiv".

    iDestruct (ghost_map_lookup with "allOrders knowPreorder")
      as %ordersLook.

    iDestruct (own_full_history_agree with "history hist") as %absHistsLook.

    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistEqAbsHist.

    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook]
      by by eapply map_dom_eq_lookup_Some.
    iDestruct (bumpers_lookup with "allBumpers knowBumper") as %bumpersLook.

    iDestruct (big_sepM_delete with "ptsMap") as "[pts ptsMap]"; first done.

    iApply (wp_store (extra := {| extra_state_interp := True |})
             with "[$pts $val]").
    iIntros "!>" (tT) "(%look & %gt & #valNew & pts)".
    simpl in gt.

    iDestruct (big_sepM_insert_delete with "[$ptsMap $pts]") as "ptsMap".

    iAssert (⌜ absHist !! tT = None ⌝)%I as %absHistLook.
    { iDestruct (big_sepM2_lookup_acc with "predsHold") as "[predMap predsHold]".
      { done. } { done. }
      iDestruct "predMap" as (pred' predsLook') "predMap".

      iDestruct (big_sepM2_dom with "predMap") as %domEq.
      iPureIntro. move: look.
      rewrite -!not_elem_of_dom. rewrite domEq. rewrite dom_fmap. done. }

    iDestruct (
        location_sets_singleton_included with "exclusiveLocs isExclusiveLoc"
      ) as %ℓEx.
    assert (ℓ ∉ at_locs) as ℓnotSh by set_solver.
    (* Update the ghost state for the abstract history. *)
    iMod (own_full_history_insert _ _ _ _ _ _ s with "history hist")
      as "(history & hist & histFrag)"; first done.

    (* Update ghost state. *)
    set (newMsg := Msg v ∅ ∅ PV).
    iMod (auth_map_map_insert _ _ _ _ _ newMsg with "physHist") as "[physHist #physHistFrag]".
    { done. } { done. }

    iDestruct (ghost_map_lookup with "naView knowSV") as %ℓnaView.

    iMod (ghost_map_update (<[ℓ:=MaxNat tT]>SV') with "naView knowSV") as "[naView knowSV]".
    (* iMod (ghost_map.ghost_map_update (SV ⊔ SV') with "naView knowSV") as "[naView knowSV]". *)

    rewrite /validV.
    iModIntro.
    iFrame "valNew".
    rewrite -assoc.
    iSplit.
    { iPureIntro. repeat split; [|done|done]. apply view_insert_le. simpl. lia. }
    simpl.
    iSplitL "Φpost isExclusiveLoc pers hist knowSV".
    { iEval (monPred_simpl) in "Φpost".
      iApply "Φpost".
      { iPureIntro. etrans; first done.
        repeat split; try done.
        apply view_insert_le. lia. }
      iExists _, _, _, _, _.
      iFrame "∗#".
      (* [incrList] *)
      iSplit. { iPureIntro. eapply increasing_list_snoc; eauto. }
      (* [lookupV] *)
      iSplit. { iPureIntro. by rewrite lookup_insert last_snoc. }
      (* [nolater] *)
      iSplit. {
        iPureIntro. eapply map_no_later_insert; last done.
        etrans; first apply haveTStore.
        apply Nat.lt_le_incl. eapply Nat.le_lt_trans; last apply gt.
        f_equiv.
        apply svInclSv'. }
      (* [slice] *)
      iSplit. {
        iPureIntro. eapply map_slice_insert_snoc; [|done|done].
        eapply Nat.le_lt_trans; last apply gt.
        etrans; first done.
        f_equiv.
        apply svInclSv'. }
      (* [inThreadView] *)
      iSplit. {
        iPureIntro. repeat split.
        - done.
          (* etrans. *)
          (* { apply view_lub_le; last reflexivity. done. } *)
          (* apply view_insert_le. *)
          (* lia. *)
        - done.
        - apply view_empty_least. }
      (* [haveTSore] *)
      iSplit. { iPureIntro. by rewrite lookup_zero_insert. }
      (* "pers" *)
      iApply monPred_mono; last iApply "pers".
      etrans; first done.
      etrans; first done.
      repeat split; [|done|done].
      apply view_insert_le. lia. }
    repeat iExists _.
    iFrame "history". iFrame "ptsMap". iFrame "#". iFrame"naView". iFrameNamed.
    iSplit. { iPureIntro. set_solver. }
    (* [naViewsDom] *)
    iSplit.
    { iPureIntro. rewrite dom_insert_lookup_L; naive_solver. }
    (* [mapShared] *)
    iSplit.
    { iPureIntro. setoid_rewrite restrict_insert_not_elem; done. }

    (* [sharedLocsHistories] *)
    iSplitL "sharedLocsHistories".
    { setoid_rewrite restrict_insert_not_elem. done. done. }

    iSplit.
    (* [ordered] *)
    { iApply (big_sepM2_update_left with "ordered"); eauto.
      iIntros (orderedForall).
      iPureIntro.
      rewrite fmap_insert.
      apply: increasing_map_insert_last.
      - eauto.
      - apply map_no_later_fmap. done.
      - eapply Nat.le_lt_trans; last apply gt.
        etrans; first apply haveTStore.
        f_equiv. done.
      - rewrite lookup_fmap. rewrite lookupV. rewrite last. done.
      - eapply encode_relation_decode_iff; eauto using decode_encode. }
    iSplit.
    (* [predsHold] *)
    { iApply (big_sepM2_update with "[predsHold]"); [done|done| |].
      { iApply (big_sepM2_impl with "predsHold").
        iIntros "!>" (ℓ' physHist' absHist' physHist2 absHist2).
        (* We consider two cases, either [ℓ] is the location where we've inserted
        an element or it is a different location. The latter case is trivial. *)
        destruct (decide (ℓ = ℓ')) as [<-|neq]; last first.
        { rewrite !lookup_insert_ne; naive_solver. }
        rewrite !lookup_insert.
        iDestruct 1 as (pred' predLook') "H".
        simplify_eq.
        assert (pred = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
        clear predLook'.
        iExists _; iSplit; first done.
        iApply (big_sepM2_impl with "H").
        iIntros "!>" (?????).
        iApply encoded_predicate_holds_mono.
        repeat split; eauto.
        rewrite ℓnaView. simpl.
        etrans; first done.
        apply view_insert_le. lia. }
      iDestruct 1 as (pred' predLook') "H".
      simplify_eq.
      assert (pred = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
      clear predLook'.
      iExists _; iSplit; first done.
      rewrite fmap_insert.
      iApply big_sepM2_insert.
      { done. } { rewrite lookup_fmap absHistLook. done. }
      simpl. iFrame.
      iApply predicate_holds_phi; auto.
      rewrite lookup_insert /=.
      iDestruct (phi_nobuf with "phi") as "phi".
      simpl.
      iApply (monPred_mono with "phi").
      destruct TV as [[??]?]. destruct TV' as [[??]?].
      repeat split; last done.
      - simpl. etrans; first apply incl. etrans; first apply incl2.
        apply view_insert_le. lia.
      - simpl. etrans; first apply incl. apply incl2. }
    (* [bumperSome] *)
    iApply (big_sepM2_update_left with "bumperSome"); eauto.
    iPureIntro. intros bumperSome.
    rewrite fmap_insert.
    apply map_Forall_insert_2; eauto.
    rewrite /encode_bumper decode_encode. done.
  Qed.

End wp_na_rules.
