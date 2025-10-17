From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import gset.
From iris_named_props Require Import named_props.

From self Require Import extra solve_view_le encode_relation map_extra view_slice.

From self.lang Require Import syntax tactics lemmas.

From self.base Require Import generational_resources primitive_laws.

From self.high Require Import wrappers monpred_simpl protocol locations crash_weakestpre weakestpre.
From self.high.modalities Require Import post_fence_sync_advanced.
From self.high.lib Require Import abstract_state increasing_map.
From self.high.weakestpre.at Require Import prelude.

From self Require Export lang.
From self.high Require Export dprop.

Set Default Proof Using "Type*".

Section wp_at.
  Lemma wp_store_at ℓ prot ss s_i s_t v_t st E `{!ProtocolConditions prot} :
    {{{
      ℓ ↦_AT^{prot} (ss ++ [s_i]) ∗
      prot.(p_full) s_t v_t ∗
      (* NOTE: This does _not_ work. *)
      (* "phi" ∷ (∀ v_i, ϕ s_i v_i _ -∗ ϕ s_t v_t _ ∗ ϕ s_i v_i _) ∗ *)
      (* NOTE: This should work and be more general. *)
      (* "phi" ∷ (∀ v_i, (<obj> (ϕ s_i v_i -∗ ϕ s_i_v ∗ R)) ∗ (R -∗ ϕ s_t v_t)) ∗ *)
      ⌜ s_i ⊑ s_t ⌝ ∗
      (* The new state must be concurrent with possible other states. *)
      (∀ v_i s_c v_c, ⌜ s_i ⊑ s_c ⌝ -∗
        (* NOTE: We could give predicates for all states in ss here. *)
        prot.(p_read) s_i v_i ∗ prot.(p_full) s_t v_t ∗ prot.(p_read) s_c v_c -∗
          ⌜ s_t ⊑ s_c ∧ s_c ⊑ s_t ⌝)
    }}}
      #ℓ <-_AT v_t @ st; E
    {{{ RET #(); ℓ ↦_AT^{prot} ((ss ++ [s_i]) ++ [s_t]) }}}.
  Proof.
    intros Φ.
    iModel.
    iIntros "(pts & phi & %targetGt & greater)".
    iDestruct "pts" as (abs_hist phys_hist tLo t_i offset s' ms) "H". iNamed "H".
    iDestruct "tSLe" as %tSLe.
    (* iDestruct (store_lb_protocol with "storeLb") as "#knowProt". *)
    iDestruct (know_protocol_extract with "locationProtocol")
      as "(#knowPred & #knowPreorder & #knowBumper)".
    rewrite -know_protocol_unfold.

    rewrite /store_lb.
    (* iDestruct "storeLb" as (t_i offset) "(#prot & #hist & #offset & %tSLe)". *)
    (* We unfold the WP. *)
    iIntros ([TV' ?] [incl [= <-]]) "Φpost".
    (* iIntros (TV' incl) "Φpost". *)
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".

    iApply wp_extra_state_interp. { done. }
    { apply prim_step_store_rel_no_fork. }

    iIntros "interp".
    rewrite /is_at_loc /offset_loc 2!lift_d_at.
    iDestruct (interp_get_at_loc with "interp isAtLoc locationProtocol offset")
      as (physHists physHist absHist predFull predRead predPers tP) "(R & [reins _])".
    iNamed "R".

    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply wp_fupd.

    iApply (wp_store_release with "[$pts $val]").
    iIntros "!>" (t_t) "(%look & %gt & #valNew & pts)".
    simpl in gt.
    simpl in tSLe.
    rewrite drop_prefix_lookup in look.

    (* We can conclude that [t_t] is strictly greater than [t_i]. *)
    assert (t_i - offset < t_t) as tILtTt.
    { destruct TV as [[??]?].
      destruct TV' as [[??]?].
      destruct incl as [[??]?].
      destruct incl2 as [[??]?].
      eapply Nat.le_lt_trans; last done.
      etrans; first done.
      f_equiv.
      etrans; done. }
    assert (t_i < t_t + offset) as ? by lia.

    iFrame "valNew".

    assert (abs_hist !! t_i = Some s_i).
    { eapply map_sequence_lookup_hi in slice.
      rewrite last_snoc in slice.
      apply slice. }
    rewrite monPred_at_big_sepM.
    iDestruct (big_sepM_lookup with "absHist") as "hist"; first done.

    rewrite /know_frag_history_loc_d lift_d_at.
    iDestruct (history_full_entry_frag_lookup with "fullHist hist") as %look'.
    destruct look' as (e_i & absHistLook' & hip).
    assert (is_Some (physHist !! t_i)) as [vI physHistLook].
    { rewrite -elem_of_dom domEq elem_of_dom. done. }

    (* We must extract the phi for the initial state from "phi". *)

    iPoseProof (big_sepM2_sep_2 with "predFullHolds predReadHolds") as "predHolds".
    iDestruct (big_sepM2_delete with "predHolds") as "[phiI predHolds]";
      [apply physHistLook | done | ].

    iAssert (
      ⌜increasing_map (encode_relation sqsubseteq) (<[(t_t+offset)%nat:=encode s_t]> absHist)⌝
                      )%I as %incri.
    { iApply (bi.pure_mono).
      { apply
         (increasing_map_insert_after _ _ _ _ _ (encode s_t) increasing
                                      absHistLook'); last done.
        eapply encode_relation_decode_iff; eauto using decode_encode. }
      iIntros (t_c e_c ? iLeC).

      iAssert (p_read prot s_i (memory.msg_val vI)
                 (memory.msg_store_view vI,
                    memory.msg_persisted_after_view vI,
                      ∅, gnames))%I with "[phiI]" as "phiI". {
        destruct (decide (offset ≤ t_i ∧ physHist !! S t_i = None)) as [ [] | no ].
        - iDestruct ("phiI") as "[phiI _]".
          iSpecialize ("phiI" with "[%] [//]"); first lia.
          iDestruct (predicate_holds_phi_decode with "predFullEquiv phiI") as "phiI";
            first done.
          iPoseProof (full_read_split with "phiI") as "[phiI _]".
          iFrame.
        - iDestruct ("phiI") as "[_ phiI]".
          rewrite not_and_l in no.
          iSpecialize ("phiI" with "[%]").
          { destruct no; [ left; lia | right; by destruct (_ !! S t_i) ]. }
          iDestruct (predicate_holds_phi_decode with "predReadEquiv phiI") as "phiI";
            first done.
          iFrame.
      }

      assert (is_Some (physHist !! t_c)) as [[????] look2].
      { rewrite -elem_of_dom domEq elem_of_dom. done. }

      eassert _ as  temp. { eapply (read_atomic_location_no_inv t_i t_c); done || lia. }
      destruct temp as (s_c & encSC & ? & decodeS' & orderRelated).
      simplify_eq.
      rewrite /encode_relation. rewrite decode_encode. rewrite decodeS'.

      iDestruct (big_sepM2_delete with "predHolds") as "[phiC predHolds]";
        [ rewrite lookup_delete_ne; [ apply look2 | lia ] |
          rewrite lookup_delete_ne; [ done | lia ] | ].

      iAssert (p_read prot s_c msg_val
                 (msg_store_view, msg_persisted_after_view, ∅, gnames))%I
        with "[phiC]" as "phiC". {
        destruct (decide (offset ≤ t_c ∧ physHist !! S t_c = None)) as [ [] | no ].
        - iDestruct ("phiC") as "[phiC _]".
          iSpecialize ("phiC" with "[%] [//]"); first by lia.
          iDestruct (predicate_holds_phi_decode with "predFullEquiv phiC") as "phiC";
            first done.
          iPoseProof (full_read_split with "phiC") as "[phiC _]".
          iFrame.
        - iDestruct ("phiC") as "[_ phiC]".
          rewrite not_and_l in no.
          iSpecialize ("phiC" with "[%]").
          { destruct no; [ left; lia | right; by destruct (_ !! S t_c) ]. }
          iDestruct (predicate_holds_phi_decode with "predReadEquiv phiC") as "phiC";
            first done.
          iFrame.

     }

      iSpecialize ("greater" $! _ s_c _).
      iEval (monPred_simpl) in "greater".

      iSpecialize ("greater" $! (TV, _) with "[%] [%]"); [done|done|].
      iEval (monPred_simpl) in "greater".
      iEval (setoid_rewrite monPred_at_pure) in "greater".

      iApply ("greater" $! (TV' ⊔ (_) ⊔ (msg_to_tv vI), _)).
      { iPureIntro. split; last done. etrans; first apply incl.
        rewrite -assoc.
        apply thread_view_le_l. }
      monPred_simpl.
      iFrame.
      iSplitL "phiI".
      { iApply monPred_mono; last iApply "phiI".
        split; last done. apply thread_view_le_r. }
      iSplitL "phi".
      { iApply monPred_mono; last iApply "phi".
        split; last done.
        rewrite -assoc.
        etrans; last apply thread_view_le_l. done. }

      iApply monPred_mono; last iApply "phiC".
      split; last done.
      rewrite (comm _ TV').
      rewrite -assoc.
      apply thread_view_le_l. }

    iDestruct (big_sepM2_insert_delete with "[phiI $predHolds]") as "predHolds";
      first iFrame.
    rewrite (insert_id physHist t_i); last done.
    rewrite (insert_id absHist t_i); last done.

    rewrite drop_prefix_insert.

    iEval (rewrite big_sepM2_sep) in "predHolds".
    iDestruct "predHolds" as "[predFullHolds predReadHolds]".
    rewrite /insert_impl.

    iMod ("reins" $! (t_t + offset) s_t
      with "[%] [//] [//] [] [] [$] [predFullHolds phi predReadHolds] [predPersHolds] fullHist [//] pts")
        as "(#frag & #physHistFrag & $)".
    { lia. }
    { iPureIntro. simpl.
      replace (t_t + offset - offset) with t_t by lia.
      apply lookup_zero_insert. }
    { done. }
    { rewrite -big_sepM2_sep.
      iPoseProof (big_sepM2_sep_2 with "[$] [$]") as "predHolds".
      iApply (big_sepM2_insert_2 with "[phi] [predHolds]").
      { simpl.
        iIntros.
        rewrite lookup_insert_ne; last lia.
        destruct (physHist !! S(t_t + offset)).
        - iSplitL ""; first by iIntros.
          iIntros.
          iPoseProof (full_read_split with "phi") as "[phi _]".
          rewrite /encoded_predicate_holds.
          iExists (prot.(p_read) s_t v_t).
          iSplit.
          { iApply pred_encode_Some. done. }
          destruct TV as [[??]?].
          iDestruct (into_no_buffer_at with "phi") as "phi".
          iApply monPred_mono; last iFrame.
          destruct TV' as [[??]?].
          repeat split; last done.
          + simpl. etrans; first apply incl. etrans; first apply incl2.
            apply view_insert_le'; [done|lia].
          + simpl.
            etrans; first apply incl.
            apply incl2.
        - iSplitR ""; last (iIntros ([ | contra ]);
                            [lia | apply is_Some_None in contra; done]).
          iIntros.
          rewrite /encoded_predicate_holds.
          iExists (prot.(p_full) s_t v_t).
          iSplit.
          { iApply pred_encode_Some. done. }
          destruct TV as [[??]?].
          iDestruct (into_no_buffer_at with "phi") as "phi".
          iApply monPred_mono; last iFrame.
          destruct TV' as [[??]?].
          repeat split; last done.
          + simpl. etrans; first apply incl. etrans; first apply incl2.
            apply view_insert_le'; [done|lia].
          + simpl.
            etrans; first apply incl.
            apply incl2.
      }
      { iApply (big_sepM2_impl with "predHolds").
        simpl.
        iIntros (t msg encS physHistLook'' absHistLook'') "!> H".
        destruct (decide (offset ≤ t ∧ physHist !! S t = None)) as [ [] | no ].
        - iDestruct "H" as "[_ H]".
          destruct (decide (S t = t_t + offset)) as [-> | ?].
          + rewrite lookup_insert.
            iSplitL ""; first by iIntros.
            iIntros.
            iSpecialize ("H" with "[%] [//]"); first lia.
            iSpecialize ("predFullReadSplit" with "H").
            iFrame.
          + rewrite lookup_insert_ne; last lia.
            iSplitR ""; last (iIntros ([ | []]); [ lia | congruence ]).
            iIntros.
            iSpecialize ("H" with "[%] [//]"); first lia.
            iFrame.
        - iDestruct "H" as "[H _]".
          rewrite not_and_l in no.
          iSpecialize ("H" with "[%]").
          { destruct no; [ left; lia | right; by destruct (_ !! S t) ]. }
          iSplitL "".
          + rewrite lookup_insert_None.
            iIntros (? []).
            destruct no; [ lia | congruence].
          + iIntros.
            iApply "H".
    } }
    { rewrite /encoded_pers_predicate_hold.
      iDestruct "predPersHolds" as (encSP msgP) "(% & % & predPersHolds)".
      assert (tP ≠ t_t + offset) by by simplify_map_eq.
      iExists encSP, msgP.
      do ? (rewrite lookup_insert_ne; last done).
      iFrame.
      done. }
    (* We are done updating ghost state. *)
    iModIntro.
    iSplit. { iPureIntro. simpl. solve_view_le. }

    iEval (rewrite monPred_at_wand) in "Φpost".
    iApply "Φpost".
    - iPureIntro. split; last done. solve_view_le.
    - iExistsN.

      iSplitPure. { rewrite last_snoc. reflexivity. }
      iSplitPure. { eapply map_sequence_insert_snoc; done. }
      iSplitPure.
      { eapply map_sequence_insert_snoc; last done; first lia.
        eapply map_no_later_dom; last apply nolater.
        done. }
      iSplitPure.
      { eapply map_no_later_insert; last done. lia. }
      iSplitPure.
      { rewrite 2!dom_insert_L. rewrite absPhysHistDomEq. done. }
      simpl.
      iFrameF "isAtLoc".
      rewrite big_sepM_insert. 2: { apply nolater. lia. }
      rewrite big_sepM_insert.
      2: {
        eapply map_dom_eq_lookup_None; first done.
        apply nolater. lia. }
      rewrite -know_protocol_unfold.
      iSplitL "locationProtocol".
      { iApply view_objective_at. iFrame "locationProtocol". }
      iSplitPure.
      { apply: increasing_map_insert_last; done. }
      iSplit.
      { simpl. rewrite monPred_at_sep. simpl. iFrame "frag".
        rewrite -monPred_at_big_sepM.
        iApply view_objective_at.
        rewrite monPred_at_big_sepM.
        iEval (rewrite monPred_at_big_sepM).
        simpl.
        iFrame "absHist". }
        rewrite monPred_at_big_sepM.
      iFrame "offset".
      iSplit; last first.
      { simpl. iPureIntro.
        rewrite lookup_zero_insert.
        lia. }
      simpl.
      iSplit.
      { simpl. iFrame "physHistFrag". solve_view_le. }
      iEval (rewrite -monPred_at_big_sepM) in "physHist".
      iApply monPred_mono; last iApply "physHist".
      split; last done.
      etrans; first apply incl.
      etrans; first apply incl2.
      repeat split; solve_view_le.
  Qed.

  (* Rule for store on an atomic. *)
  (* Lemma wp_store_at_strong R Q ℓ ss s_i s_t v_t (prot : LocationProtocol ST) st E : *)
  (*   {{{ *)
  (*     ℓ ↦_AT^{prot} (ss ++ [s_i]) ∗ *)
  (*     (* [s_l] is the state of the store that ours end up just after in the *)
  (*     history. *) *)
  (*     (∀ s_l v_l, ⌜ s_i ⊑ s_l ⌝ -∗ ∃ s_t, *)
  (*       (* The state we picked fits in the history. *) *)
  (*       (∀ v_i s_n v_n, ⌜ s_l ⊑ s_n ⌝ -∗ *)
  (*         prot.(p_inv) s_i v_i -∗ *)
  (*         prot.(p_inv) s_l v_l -∗ *)
  (*         prot.(p_inv) s_n v_n -∗ *)
  (*         ⌜ s_l ⊑ s_t ⌝ ∗ ⌜ s_t ⊑ s_n ⌝) ∧ *)
  (*       (* Extract from the location we load. *) *)
  (*       (<obj> (prot.(p_inv) s_l v_l -∗ prot.(p_inv) s_l v_l ∗ R s_l)) ∗ *)
  (*       (* Establish the invariant for the value we store. *) *)
  (*       (R s_l -∗ prot.(p_inv) s_t v_t ∗ Q s_t)) *)
  (*   }}} *)
  (*     #ℓ <-_AT v_t @ st; E *)
  (*   {{{ RET #(); store_lb ℓ prot s_t ∗ Q s_t }}}. *)
  (* Proof. *)
  (* Abort. *)
End wp_at.
