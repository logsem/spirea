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

From self.algebra Require Import ghost_map ghost_map_map.
From self Require Export extra ipm_tactics encode_relation view view_slice.
From self.lang Require Export lang lemmas tactics syntax.
From self.base Require Import primitive_laws.
From self.high Require Import dprop resources weakestpre crash_weakestpre
     lifted_modalities monpred_simpl modalities locations protocol.
From self.high.modalities Require Import no_buffer.

Section wp_na_rules.
  Context `{AbstractState ST}.
  Context `{!nvmG Σ, hG : nvmDeltaG}.

  Implicit Types (ℓ : loc) (s : ST) (prot : LocationProtocol ST).

  Lemma wp_alloc_na v s prot `{!ProtocolConditions prot} st E :
    {{{ prot.(p_full) s v ∗ prot.(p_pers) s v }}}
      ref_NA v @ st; E
    {{{ ℓ, RET #ℓ; ℓ ↦_{prot} ([] ++ [s]) }}}.
  Proof.
    intros Φ.
    iModel.
    iIntros "[φ_full φ_pers]". introsIndex TV' incl. iIntros "Φpost".

    (* Unfold the wp *)
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".

    iApply wp_extra_state_interp. { done. } { by apply prim_step_ref_no_fork. }
    (* We open [interp]. *)
    iNamed 1.

    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    iApply (wp_alloc (extra := {| extra_state_interp := True |})); first done.
    iNext.
    iIntros (ℓ CV') "(crashedAt' & % & % & pts)".
    simpl.
    iFrame "val".

    iDestruct (big_sepM2_dom with "oldViewsDiscarded") as %offsetsDom.
    (* The new location is not in the existing [phys_hist]. *)
    destruct (phys_hists !! ℓ) eqn:physHistsLook.
    { assert (is_Some (offsets !! ℓ)) as (? & ?).
      { apply elem_of_dom. rewrite -offsetsDom. apply elem_of_dom. done. }
      iDestruct (big_sepM_lookup with "ptsMap") as "pts'".
      { apply map_lookup_zip_with_Some. naive_solver. }
      iDestruct (mapsto_valid_2 with "pts pts'") as (?) "_".
      done. }

    iDestruct (big_sepM2_dom with "predsFullHold") as %domEq.
    iDestruct (big_sepM2_dom with "bumperSome") as %domEq2.
    iDestruct (big_sepM2_dom with "bumpMono") as %domEq4.

    (* We update ghost state. *)

    (* Update ghost state for physical history. *)
    iMod (auth_map_map_insert_top with "physHist") as "[physHist ownPhysHist]".
    { done. }

    (* Add the predicate to the ghost state of predicates. *)
    iMod (own_all_preds_insert with "full_predicates") as "[full_predicates knowFullPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    iMod (own_all_preds_insert with "read_predicates") as "[read_predicates knowReadPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    iMod (own_all_preds_insert with "pers_predicates") as "[pers_predicates knowPersPred]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }
    (* Add a new offset to the ghost state of offfsets. *)
    iMod (ghost_map_insert_persist ℓ 0 with "offsets") as "[offsets #offset]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }

    (* Allocate the abstract history for the location. *)
    iMod (full_map_insert _ _ _ {[0 := encode s]} with "history")
      as "(history & ownHist & #fragHist)".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }

    (* Add the bumper to the ghost state of bumper. *)
    iMod (own_all_bumpers_insert _ _ _ (prot.(p_bumper)) with "allBumpers") as "[allBumpers knowBumper]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook. congruence. }

    (* Add the preorder to the ghost state of bumper. *)
    iMod (ghost_map_insert_persist with "allOrders") as "[allOrders #knowOrder]".
    { eapply map_dom_eq_lookup_None; last apply physHistsLook.
      rewrite /relation2. congruence. }

    assert (abs_hists !! ℓ = None) as absHistsLook.
    { apply not_elem_of_dom. rewrite -domEq. apply not_elem_of_dom.
      assumption. }
    assert (ℓ ∉ dom abs_hists) as absHistsDomElem.
    { apply not_elem_of_dom. done. }
    assert (ℓ ∉ at_locs).
    { set_solver+ locsDisjoint histDomLocs absHistsDomElem. }
    assert (ℓ ∉ na_locs).
    { set_solver+ locsDisjoint histDomLocs absHistsDomElem. }

    (* Add the allocated location to the set of non-atomic locations. *)
    iMod (own_update with "naLocs") as "[naLocs fragExclusiveLoc]".
    { apply auth_update_alloc. apply gset_local_update.
      apply (union_subseteq_r {[ ℓ ]}). }
    iEval (rewrite -gset_op) in "fragExclusiveLoc".
    iDestruct "fragExclusiveLoc" as "[#isExclusive _]".
    (* Insert in na views *)
    iMod (ghost_map_insert _ SV with "naView") as "[naView ownNaView]".
    { rewrite -not_elem_of_dom. rewrite naViewsDom. done. }
      (* set_solver. *)
      (* setoid_rewrite <- not_elem_of_dom in physHistsLook. *)
      (* eapply not_elem_of_weaken; first apply physHistsLook. *)
      (* rewrite domEq. set_solver. } *)

    iModIntro.
    rewrite -assoc. iSplit; first done.
    iSplitL "Φpost knowFullPred knowReadPred knowPersPred knowBumper knowOrder ownHist ownNaView ownPhysHist".
    { setoid_rewrite monPred_at_wand.
      iApply "Φpost"; first done.
      rewrite /mapsto_na.
      iExists _, _, _, _, _, (Msg v ∅ ∅ PV), _.
      iSplitPure; first done.
      simpl.
      iEval (rewrite !monPred_at_embed).
      iSplit.
      { iFrame "knowFullPred knowReadPred knowPersPred knowOrder knowBumper". }
      iFrame "isExclusive".
      repeat iExists _.
      rewrite -map_fmap_singleton. iFrame "ownHist".
      iFrame "ownNaView".
      iFrame "ownPhysHist".
      iFrame "offset".
      simpl.
      iSplitPure; first apply increasing_map_singleton.
      iSplitPure; first apply lookup_singleton.
      iSplitPure; first apply map_no_later_singleton.
      iSplit.
      { iExists _.
        iDestruct (big_sepM_lookup with "fragHist") as "$".
        { rewrite map_fmap_singleton. apply lookup_singleton. }
        rewrite decode_encode. done. }
      iSplitPure; first (split; [apply lookup_singleton | reflexivity]).
      iSplitPure; first repeat split; auto using view_empty_least.
      iSplitPure; first lia.
      iSplitPure; first lia.
      iRight. done. }
    repeat iExists _.
    (* attempts to frame conjunctions that can decide evars. *)
    iFrame "physHist offsets naView crashedAt history
            full_predicates read_predicates pers_predicates
            allOrders naLocs atLocs allBumpers globalPViewPersisted".
    (* We split up some of the big seps s.t. we can frame things away
     * immediately. *)
    rewrite -!map_insert_zip_with.
    rewrite !(restrict_insert_not_elem ℓ at_locs); try done.
    rewrite !dom_insert_L.
    rewrite !big_sepM_insert; try (done || rewrite -not_elem_of_dom dom_map_zip_with; set_solver ).
    (* 13 seconds, maybe improve later *)
    rewrite !big_sepM2_insert; try solve [ rewrite -not_elem_of_dom; set_solver ].

    (* solve most pure conjuncts *)
    rewrite -[ {[ℓ]} ∪ _ ∪ _ ]union_assoc_L.
    rewrite map_Forall_insert; last (rewrite -not_elem_of_dom; set_solver).
    rewrite disjoint_union_l disjoint_singleton_l 2!bi.pure_and.
    repeat lazymatch goal with
           | |- context[ ?c ∪ ?a = ?c ∪ ?b ] =>
               setoid_replace (c ∪ a = c ∪ b) with (a = b) using relation (flip impl); last by congruence
           | |- context [ ?a ⊆ ?c ∪ ?b ] =>
               setoid_replace (a ⊆ c ∪ b) with (a ⊆ b) using relation (flip impl); last by (intro; set_solver)
           end.
    repeat lazymatch goal with
      | [H: ?P |- context[ ⌜ ?P ⌝%I ] ] =>
          iFrame (H)
    end.
    (* some more spacial and persistent hypothesis to frame *)
    iFrame "pts ptsMap bumperSome ordered bumpMono oldViewsDiscarded historyFragments fragHist atLocsHistories".
    iSplitPure; first (intros; lia).
    (* increasingMap *)
    iSplitPure; first apply increasing_map_singleton.
    (* predsFullHold *)
    iSplitL "predsFullHold φ_full".
    { iSplitL "φ_full".
      - iExists _, _. rewrite !lookup_insert.
        repeat (iSplitPure; first done).
        rewrite /initial_history.
        simpl.
        rewrite big_sepM2_singleton /=.
        simpl.
        iDestruct (predicate_holds_phi with "[]") as "HH".
        { done. }
        { done. }
        iIntros (?) "_".
        iApply "HH".
        destruct TV as [[??]?]. destruct TV' as [[??]?].
        iDestruct (into_no_buffer_at with "φ_full") as "phi".
        iApply (monPred_mono with "phi").
        repeat split; last done.
        * etrans; first apply incl. apply incl2.
        * etrans; first apply incl. apply incl2.
      - iApply (big_sepM2_impl with "predsFullHold").
        iModIntro. iIntros (ℓ' ????) "(%pred & %offset & %predLook & %offsetLook & ?)".
        iExists pred, offset.
        assert (ℓ ≠ ℓ') by congruence.
        repeat (rewrite lookup_insert_ne; last done).
        repeat (iSplit; first done).
        iFrame. }
    iSplitL "predsReadHold".
    { iSplitL "".
      - iExists _, _. rewrite !lookup_insert.
        repeat (iSplitPure; first done).
        rewrite /initial_history.
        simpl.
        rewrite big_sepM2_singleton /= lookup_singleton_ne; last done.
        iIntros ([ ? | [] ]); [ lia | done ].
      - iApply (big_sepM2_impl with "predsReadHold").
        iModIntro. iIntros (ℓ' ????) "(%pred & %offset & %predLook & %offsetLook & ?)".
        iExists pred, offset.
        assert (ℓ ≠ ℓ') by congruence.
        repeat (rewrite lookup_insert_ne; last done).
        repeat (iSplit; first done).
        iFrame. }
    iSplitL "predsPersHold φ_pers".
    { iSplitL "φ_pers".
      - iExists _, _, _, _. rewrite !lookup_insert //=.
        iSplitPure; first done.
        iSplitPure.
        { right. split; last done. rewrite -not_elem_of_dom. set_solver. }
        repeat (iSplitPure; first rewrite lookup_singleton //).
        iDestruct (predicate_holds_phi with "[]") as "HH".
        { done. }
        { done. }
        iApply "HH".
        destruct TV as [[??]?]. destruct TV' as [[??]?].
        iDestruct (into_no_buffer_at with "φ_pers") as "phi".
        iApply (monPred_mono with "phi").
        repeat split; last done.
        * etrans; first apply incl. apply incl2.
        * etrans; first apply incl. apply incl2.
      - iApply (big_sepM2_impl with "predsPersHold").
        iModIntro. iIntros (ℓ' ????) "(%pred & %t & %encS & %msg & % & %pview & % & % & ?)".
        iExists pred, t, encS, msg.
        assert (ℓ ≠ ℓ') by congruence.
        rewrite map_lookup_zip_with in pview.
        rewrite map_lookup_zip_with.
        repeat (rewrite lookup_insert_ne; last done).
        iFrame "%∗". }

    (* bumpMono *)
    iSplitL.
    { iPureIntro. simpl. apply encode_bumper_bump_mono. apply bumper_mono. }
    (* predFullPostCrash *)
    iSplit.
    { iSplit.
      - iExistsN.
        rewrite ?lookup_insert.
        do 3 (iSplitPure; first done).
        iModIntro. iIntros (????) "(%P_pers & #eqPers & persHolds)".
        iSplit.
        + iIntros (???) "(%P_full & #eqFull & fullHolds) %bumperEq".
          apply encode_bumper_Some_decode in bumperEq.
          destruct bumperEq as (s3 & bumperEq & bumperEq').
          iEval (rewrite /encode_predicate).
          rewrite -bumperEq'.
          rewrite decode_encode.
          iExists _, _.
          iSplit. { iPureIntro. simpl. reflexivity. }
          iSplit. { iPureIntro. simpl. reflexivity. }
          iDestruct (encode_predicate_decode with "eqPers") as (s4) "%s5DecodeEq".
          iPoseProof (encode_predicate_extract with "eqPers persHolds") as "predPers".
          { done. }
          iPoseProof (encode_predicate_extract with "eqFull fullHolds") as "predFull".
          { done. }
          iPoseProof (pred_full_post_crash with "predPers") as "[PostCrash _]".
          by iApply "PostCrash".
        + iIntros (??????) "#eqFull".
          iDestruct (encode_predicate_decode with "eqPers") as (s4) "%s4DecodeEq".
          iPoseProof (encode_predicate_extract with "eqPers persHolds") as "predPers".
          { done. }
          iDestruct (encode_predicate_decode with "eqFull") as (s5) "%s5DecodeEq".
          iPoseProof (pred_full_post_crash with "predPers") as "[_ PostCrash]".
          (* we need to instantiate the universal, but we cannot find the
             instance for [s_c], because we don't know whether [decode e_c]
             yields anything, not until after we instantiate [s_c]. but we can
             get around it by case distinction. *)
          destruct (@decode ST _ _ e_c) as [s3 | ] eqn:Heqn.
          * iDestruct ("PostCrash" $! s5 v_f s3 v_c) as (P_obj) "[objImpl PostCrash]".
            iExists P_obj.
            iSplitL "objImpl". {
              (* monPred_simpl. *)
              iIntros (?).
              rewrite monPred_at_wand.
              iIntros (view') "% fullHolds".
              iPoseProof (encode_predicate_extract with "eqFull fullHolds") as "predFull".
              { done. }
              iSpecialize ("objImpl" $! view' with "predFull").
              iFrame.
            }
            iIntros "objHolds %bumperEq %order1 %order2 (%P_read & #eqRead & readHolds)".
            iSpecialize ("PostCrash" with "objHolds").
            apply encode_bumper_Some_decode in bumperEq.
            destruct bumperEq as (s3' & bumperEq & bumperEq').
            iEval (rewrite /encode_predicate).
            rewrite -bumperEq'.
            rewrite decode_encode.
            simplify_eq.
            iPoseProof (encode_predicate_extract with "eqRead readHolds") as "predRead".
            { done. }
            iPoseProof (monPred_wand_force with "PostCrash") as "PostCrash".
            iSpecialize ("PostCrash" with "predRead").
            iExists _, _.
            iSplit. { iPureIntro. simpl. reflexivity. }
            iSplit. { iPureIntro. simpl. reflexivity. }
            rewrite encode_relation_decode_iff in order1; [ | done | done ].
            rewrite encode_relation_decode_iff in order2; [ | done | done ].
            iApply "PostCrash"; iPureIntro; destruct order1; simplify_eq; done.
          * (* this is the spurious case, we will see that once we get hold of
               [encode_bumper], we will just feed some random [ST] *)
            iDestruct ("PostCrash" $! s5 v_f s4 v_c) as (P_obj) "[objImpl PostCrash]".
            iExists P_obj.
            iSplitL "objImpl". {
              (* monPred_simpl. *)
              iIntros (?).
              rewrite monPred_at_wand.
              iIntros (view') "% fullHolds".
              iPoseProof (encode_predicate_extract with "eqFull fullHolds") as "predFull".
              { done. }
              iSpecialize ("objImpl" $! view' with "predFull").
              iFrame.
            }
            iIntros "_ %bumperEq".
            apply encode_bumper_Some_decode in bumperEq.
            destruct bumperEq as (s3' & bumperEq & bumperEq').
            rewrite Heqn in bumperEq.
            discriminate.
      - iApply (big_sepM2_impl with "predFullPostCrash").
        iModIntro. iIntros (ℓ' ????) "(% & % & % & % & % & % & H)".
        assert (ℓ' ∈ dom predicates_read) by (rewrite elem_of_dom //).
        assert (ℓ ≠ ℓ') by congruence.
        repeat (rewrite lookup_insert_ne; last done).
        iExistsN.
        repeat (iSplitPure; first done).
        iApply "H". }
    (* [predReadPostCrash] *)
    iSplit.
    { iSplitL; last iAssumption.
      iIntros (?????) "!> %bumperEq (%Pread & #eqRead & ReadHolds)".
      apply encode_bumper_Some_decode in bumperEq.
      destruct bumperEq as (s3 & bumperEq & bumperEq').
      iEval (rewrite /encode_predicate).
      rewrite -bumperEq'.
      rewrite decode_encode.
      iExists _.
      iSplit. { iPureIntro. simpl. reflexivity. }
      iPoseProof (encode_predicate_extract with "eqRead ReadHolds") as "predRead".
      { done. }
      iPoseProof (pred_read_post_crash with "predRead") as "PostCrash".
      iApply "PostCrash". }
    (* [predFullReadSplit] *)
    iSplit.
    { iSplitL; last iAssumption.
      iIntros (???) "!> (%P_full & #eqFull & fullHolds)".
      iDestruct (encode_predicate_decode with "eqFull") as (s4) "%s4DecodeEq".
      iPoseProof (encode_predicate_extract with "eqFull fullHolds") as "predFull".
      { done. }
      iPoseProof (full_read_split with "predFull") as "[predRead _]".
      iExists _.
      iEval (rewrite /encode_predicate s4DecodeEq).
      iSplit; done. }
    (* bumperBumpToValid *)
    iSplitPure.
    { apply encode_bumper_bump_to_valid. }
    (* bumperSome *)
    iPureIntro.
    apply map_Forall_singleton.
    rewrite encode_bumper_encode.
    done.
  Qed.

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
    introsIndex TV' incl.
    iIntros "Φpost".
    rewrite monPred_at_later.
    iApply wp_unfold_at.
    iIntros ([[SV' PV] BV] incl2) "#val".

    (* We need to get the points-to predicate for [ℓ]. This is inside [interp]. *)
    iApply wp_extra_state_interp.
    { done. }
    { by apply prim_step_load_no_fork. }
    iNamed 1.
    iDestruct (own_all_full_preds_pred with "full_predicates knowFullPred") as
      (pred predsLook) "#predsEquiv".
    simpl. rewrite !monPred_at_embed.
    iDestruct (full_map_full_entry with "history [$]") as %absHistlook.

    iDestruct (big_sepM2_dom with "predsFullHold") as %domPhysHistEqAbsHist.
    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
    { rewrite -elem_of_dom domPhysHistEqAbsHist elem_of_dom. done. }

    iDestruct (ghost_map_lookup with "offsets offset") as %?.

    iDestruct (big_sepM2_lookup_acc with "predsFullHold") as "[predMap predsFullHold]".
    { done. } { done. }
    iDestruct "predMap" as (pred' offset' ??) "predMap".
    simplify_map_eq.

    iDestruct (big_sepM_lookup_acc with "ptsMap") as "[pts ptsMap]".
    { apply map_lookup_zip_with_Some. naive_solver. }
    iApply (wp_load (extra := {| extra_state_interp := True |}) with "[$pts $val]").
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
    assert (tS - offset ≤ SV' !!0 ℓ) as tSle.
    { etrans; first done. f_equiv. done. }
    assert (tS - offset ≤ tT) as lte.
    { etrans; first done. apply gt. }
    iDestruct (big_sepM2_dom with "predMap") as %domEq.
    apply drop_prefix_lookup_Some in look.
    assert (is_Some (absHist !! (tT + offset))) as HI.
    { apply elem_of_dom.
      erewrite <- dom_fmap_L.
      erewrite <- domEq.
      apply elem_of_dom.
      naive_solver. }
    assert (tT = tS - offset).
    { apply Nat.lt_eq_cases in lte. destruct lte as [lt|]; last done.
      eassert _ as eq. { apply (nolater (tT + offset)). lia. }
      (* pose proof (nolater tT lt) as eq. *)
      rewrite eq in HI. inversion HI as [? [=]]. }
    assert (tS = tT + offset) as -> by lia.
    clear lte HI.

    iDestruct (auth_map_map_lookup_agree with "[$] [$]") as %eq.
    { done. } { done. }
    subst.

    iDestruct (big_sepM2_lookup_acc with "predMap") as "[predHolds predMap]";
      first done.
    { rewrite lookup_fmap. rewrite lookupV. done. }
    iDestruct (ghost_map_lookup with "naView knowSV") as %->.
    simpl.
    iSpecialize ("predHolds" with "[%] [%]").
    { lia. }
    { rewrite -not_elem_of_dom domEq not_elem_of_dom lookup_fmap fmap_None.
      apply nolater.
      lia. }
    iDestruct (predicate_holds_phi with "predsEquiv predHolds") as "phi";
      first done.
    rewrite monPred_at_objectively.
    iSpecialize ("pToQ" $! (SV, msg_persisted_after_view msg, ∅, _) (msg_val msg)).
    rewrite monPred_at_wand.
    iDestruct ("pToQ" with "[] phi") as "[Q phi]".
    { iPureIntro. reflexivity. }
    (* Reinsert into the predicate map. *)
    iDestruct ("predMap" with "[phi]") as "predMap".
    { iIntros "_ _". iApply (predicate_holds_phi with "predsEquiv phi"). done. }
    (* Reinsert into the map. *)
    iDestruct ("predsFullHold" with "[predMap]") as "predsHold". { naive_solver. }

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
        split; last done.
        etrans; last done.
        done. }
      iExistsN.
      (* iPureGoal; first done. *)
      iSplitPure; first apply sLast.
      simpl. rewrite !monPred_at_embed.
      iSplit. { iFrameNamed. }
      iFrameNamed.
      iPureIntro. etrans; eassumption. }
    split; done.
  Qed.

  Lemma wp_store_na ℓ prot ss v s__last s st E `{!ProtocolConditions prot} :
    last ss = Some s__last →
    s__last ⊑ s →
    {{{ mapsto_na ℓ prot 1 ss ∗ prot.(p_full) s v }}}
      #ℓ <-_NA v @ st; E
    {{{ RET #(); mapsto_na ℓ prot 1 (ss ++ [s]) }}}.
  Proof.
    intros last stateGt Φ.
    iModel.
    iIntros "(pts & phi)".
    rewrite /mapsto_na.
    iDestruct "pts" as (?tP ?tS offset SV absHist msg) "pts". iNamed "pts".
    assert (a = s__last) as -> by congruence.
    iNamed "locationProtocol".
    iDestruct "inThreadView" as %inThreadView.

    rewrite monPred_at_wand. simpl.
    introsIndex TV' incl.
    iIntros "Φpost".
    iApply wp_unfold_at.
    iIntros ([[SV' PV] BV] incl2) "#val".

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
    iDestruct (own_all_preds_pred with "full_predicates knowFullPred")
      as (pred predsLook) "#predsEquiv".

    iDestruct (ghost_map_lookup with "allOrders knowPreorder")
      as %ordersLook.

    iDestruct (full_map_full_entry with "history hist") as %absHistsLook.

    iDestruct (big_sepM2_dom with "predsFullHold") as %domPhysHistEqAbsHist.

    iDestruct (ghost_map_lookup with "offsets offset") as %?.

    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook]
      by by eapply map_dom_eq_lookup_Some.
    iDestruct (bumpers_lookup with "allBumpers knowBumper") as %bumpersLook.

    iDestruct (big_sepM_delete with "ptsMap") as "[pts ptsMap]".
    { apply map_lookup_zip_with_Some. naive_solver. }

    iApply (wp_store (extra := {| extra_state_interp := True |})
             with "[$pts $val]").
    iIntros "!>" (tT) "(%look & %gt & #valNew & pts)".
    simpl in gt.
    rewrite drop_prefix_lookup in look.

    iDestruct (big_sepM_insert_delete with "[$ptsMap $pts]") as "ptsMap".

    iAssert (⌜ absHist !! (tT + offset)%nat = None ⌝)%I as %absHistLook.
    { iDestruct (big_sepM2_lookup_acc with "predsFullHold") as "[predMap predsHold]".
      { done. } { done. }
      iDestruct "predMap" as (pred' offset' ??) "predMap".

      iDestruct (big_sepM2_dom with "predMap") as %domEq.
      iPureIntro. move: look.
      rewrite -!not_elem_of_dom. rewrite domEq. rewrite dom_fmap. done. }

    iDestruct (
        location_sets_singleton_included with "naLocs isNaLoc"
      ) as %ℓEx.
    assert (ℓ ∉ at_locs) as ℓnotSh by set_solver.
    (* Update the ghost state for the abstract history. *)
    iMod (full_map_full_entry_insert _ _ _ _ (encode s) with "history hist")
      as "(history & hist & #newHistFrag)".
    { rewrite lookup_fmap. erewrite absHistLook. done. }

    (* Update ghost state. *)
    set (newMsg := Msg v ∅ ∅ PV).
    iMod (auth_map_map_insert _ _ _ _ _ newMsg with "physHist")
      as "(physHist & _ & #physHistFrag)".
    { done. } { done. }

    iDestruct (ghost_map_lookup with "naView knowSV") as %ℓnaView.

    iMod (ghost_map_update (<[ℓ:=MaxNat tT]>SV') with "naView knowSV")
      as "[naView knowSV]".

    assert (tS - offset < tT) as tSLttT.
    { eapply Nat.le_lt_trans; first apply haveTStore.
      eapply Nat.le_lt_trans; last apply gt.
      f_equiv. apply svInclSv'. }
    assert (tS < tT + offset) as ? by lia.

    rewrite /validV.
    iModIntro.
    iFrame "valNew".
    rewrite -assoc.
    iSplit.
    { iPureIntro. repeat split; [|done|done]. apply view_insert_le. simpl. lia. }
    simpl.
    iSplitL "Φpost isNaLoc hist knowSV".
    { iEval (monPred_simpl) in "Φpost".
      iApply "Φpost".
      { iPureIntro. etrans; first done.
        split; last done.
        solve_view_le. }
      iExists _, (tT + offset), offset, _, _, _, _.
      iSplitPure. { rewrite last_snoc. reflexivity. }
      simpl. rewrite !monPred_at_embed.
      iSplit. { iFrameNamed. }
      iFrame "physHistFrag".
      rewrite /know_full_history_loc.
      rewrite /full_entry_unenc.
      rewrite /history_full_entry_encoded.
      iEval (rewrite -fmap_insert) in "hist".
      iFrame "hist".
      iFrame "∗#".
      (* [incrMap] *)
      iSplitPure. { apply: increasing_map_insert_last; eauto. }
      (* [lookupV] *)
      iSplitPure. { rewrite lookup_insert. done. }
      (* [nolater] *)
      iSplitPure.
      { eapply map_no_later_insert; last done.
        lia. }
        (* etrans; first apply haveTStore. *)
        (* apply Nat.lt_le_incl. eapply Nat.le_lt_trans; last apply gt. *)
        (* f_equiv. *)
        (* apply svInclSv'. } *)
      (* [histFrag] *)
      iSplit.
      { iExists _. iFrame "newHistFrag". by rewrite decode_encode. }
      (* [slice] *)
      iSplit. {
        iPureIntro. eapply map_sequence_insert_snoc; [|done|done].
        lia. }
        (* eapply Nat.le_lt_trans; last apply gt. *)
        (* etrans; first done. *)
        (* f_equiv. *)
        (* apply svInclSv'. } *)
      (* [inThreadView] *)
      iSplit. {
        iPureIntro. repeat split.
        - done.
        - done.
        - apply view_empty_least. }
      (* [haveTSore] *)
      iPureIntro. rewrite lookup_zero_insert. split; lia. }
    iExistsN.
    iFrame "physHist naView crashedAt history
            full_predicates read_predicates pers_predicates
            allOrders naLocs atLocs allBumpers globalPViewPersisted".
    rewrite drop_prefix_insert.
    iEval (rewrite map_insert_zip_with) in "ptsMap".
    iFrame "ptsMap".
    iFrame.
    (* [offsets] *)
    iSplitL "offsets".
    { rewrite (insert_id offsets ℓ offset) //. }
    (* repeat (iSplitL ""; *)
    (*           first solve [ *)
    (*               iPureIntro; done | *)
    (*               iAssumption ]). *)
    (* [oldViewsDiscarded] *)
    iSplit.
    { iApply (big_sepM2_insert_2 with "[] oldViewsDiscarded").
      iIntros (t2 ?).
      iDestruct (big_sepM2_lookup _ _ _ ℓ with "oldViewsDiscarded") as %hi;
        [done|done|].
      destruct (decide (tT + offset = t2)) as [<-|neq].
      - iIntros (?). lia.
      - rewrite lookup_insert_ne; last done.
        iPureIntro. apply hi. }
    (* [historyFragments] *)
    iSplit.
    { erewrite <- (insert_id offsets); last done.
      iApply (big_sepM_insert_2 with "[] historyFragments").
      iDestruct (big_sepM_lookup with "historyFragments") as "F"; first done.
      iApply (big_sepM_insert_2 with "newHistFrag F"). }
    repeat (rewrite dom_insert_lookup_L; last (rewrite -elem_of_dom; set_solver)).
    rewrite -map_insert_zip_with.
    rewrite !restrict_insert_not_elem; [ | set_solver | set_solver ].
    iFrame "atLocsHistories".
    repeat (iSplitL "";
              first solve [
                  iPureIntro; done |
                  iAssumption ]).
    iSplit.
    (* [ordered] *)
    { iApply (big_sepM2_update_left with "ordered"); eauto.
      iIntros (orderedForall).
      iPureIntro.
      apply: increasing_map_insert_last.
      - eauto.
      - apply map_no_later_fmap. done.
      - lia.
        (* eapply Nat.le_lt_trans; last apply gt. *)
        (* etrans; first apply haveTStore. *)
        (* f_equiv. done. *)
      - rewrite lookup_fmap. rewrite lookupV. done.
      - eapply encode_relation_decode_iff; eauto using decode_encode. }
    iSplitPure; first done.
    (* deal with the case analysis part last *)
    rewrite (comm bi_sep ("predsFullHold" ∷ _)) -!(assoc bi_sep).
    rewrite (comm bi_sep ("predsReadHold" ∷ _)) -!(assoc bi_sep).
    iSplitL "predsPersHold".
    { rewrite !(insert_id offsets); last done.
      iApply (big_sepM2_impl with "[predsPersHold]").
      - iApply (big_sepM2_update with "predsPersHold"); [ done | done | ].
        repeat (iApply bi.exist_mono; intros).
        f_equiv. f_equiv.
        iIntros "(%absLook & %physLook & $)".
        pose proof absLook.
        apply elem_of_dom_2 in absLook.
        rewrite dom_fmap in absLook.
        assert (tT + offset ∉ dom absHist) by rewrite not_elem_of_dom //.
        assert (a0 ≠ tT + offset) by set_solver.
        repeat (rewrite lookup_insert_ne; last done).
        iFrame "%".
      - iModIntro. iIntros (ℓ' phys_hist abs_hist ??).
        repeat (iApply bi.exist_mono; intros).
        rewrite encoded_predicate_holds_mono; first repeat try (reflexivity || f_equiv).
        repeat (split; last done).
        destruct (decide (ℓ = ℓ')) as [ <- | ? ].
        + rewrite lookup_insert.
          rewrite ℓnaView.
          simpl.
          trans SV'; first done.
          apply view_insert_le.
          lia.
        + rewrite lookup_insert_ne; last done.
          done. }
    repeat (iSplitL "";
              first solve [
                  iPureIntro; done |
                  iAssumption ]).
    (* [bumperSome] *)
    iSplit.
    { iEval (erewrite <- (insert_id bumpers ℓ); last done).
      iApply (big_sepM2_update with "bumperSome"); [ done | done | ].
      iPureIntro.
      apply map_Forall_insert_2.
      rewrite encode_bumper_encode //. }
    iPoseProof (big_sepM2_sep with "[$predsFullHold $predsReadHold]") as "predsHold".
    iDestruct (big_sepM2_delete with "predsHold") as "[predHolds predsRest]";
      [ exact physHistsLook | done | ].
    iEval (rewrite -big_sepM2_sep).
    iEval (rewrite big_sepM2_insert_delete).
    iSplitL "predHolds phi".
    - iDestruct "predHolds" as "[(%pred' & %offset' & % & % & predFullHolds)
                                 (%predRead & %offset'' & % & % & predReadHolds)]".
      simplify_map_eq.
      iApply bi.sep_exist_l. iExists predRead.
      iApply bi.sep_exist_l. iExists offset.
      iApply bi.sep_exist_r. iExists pred.
      iApply bi.sep_exist_r. iExists offset.
      rewrite -!(assoc bi_sep).
      repeat lazymatch goal with
             | [H: ?P |- context[ ⌜ ?e = ?e ⌝%I ] ] =>
                 let eq := fresh in
                 assert (eq: e = e) by done;
                 iFrame (eq);
                 clear eq
             end.
      iPoseProof (big_sepM2_sep with "[$]") as "predHolds".
      iEval (rewrite -big_sepM2_sep big_sepM2_insert_delete).
      iEval (rewrite -(delete_notin _ _ look) -(delete_notin _ _ absHistLook)).
      iDestruct (big_sepM2_dom with "[$]") as "%domEq".
      rewrite dom_fmap_L in domEq.
      iSplitL "phi"; first iSplitL "phi".
      { iIntros.
        iDestruct (predicate_holds_phi with "predsEquiv") as "HH".
        { done. }
        iApply "HH".
        destruct TV as [[??]?]. destruct TV' as [[??]?].
        iDestruct (into_no_buffer_at with "phi") as "phi".
        iApply (monPred_mono with "phi").
        repeat split; last done.
        solve_view_le.
        * etrans; first apply incl. apply incl2. }
      { rewrite -elem_of_dom (delete_notin _ _ look) dom_insert elem_of_union domEq elem_of_dom nolater; last lia.
        iIntros ([ | [ contra | [] ] ]); [ lia | | done ].
        apply elem_of_singleton_1 in contra.
        lia. }
      (* depends on whether [tS +1 =? tT], we might need to move around the predicates *)
      destruct (decide (tS + 1 = tT)) as [ <- | ? ].
      +
    - iApply (big_sepM2_impl with "predsRest").
      iModIntro. iIntros (ℓ' phys_hist abs_hist physHistsLook' ?).
      assert (ℓ ≠ ℓ') by (apply lookup_delete_Some in physHistsLook' as []; done).
      repeat (rewrite lookup_insert_ne; last done).
      iApply bi.wand_refl.
  Qed.

End wp_na_rules.
