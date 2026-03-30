From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import gset.
From iris_named_props Require Import named_props.

From self Require Import extra solve_view_le encode_relation map_extra view_slice.

From self.lang Require Import syntax tactics lemmas.

From self.base Require Import generational_resources primitive_laws.

From self.high Require Import monpred_simpl protocol locations crash_weakestpre weakestpre.
From self.high.modalities Require Import post_fence_sync_advanced.
From self.high.lib Require Import abstract_state increasing_map.
From self.high.weakestpre.at Require Import prelude.

From self Require Export lang.
From self.high Require Export dprop.

Set Default Proof Using "Type*".

Section wp_at.
  Context `{AbstractState ST}.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, PerennialG Σ}.

  Implicit Types (ℓ : loc) (σ : ST) (prot : LocationProtocol ST).

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
    iNamed "locationProtocol".

    rewrite /store_lb.
    (* iDestruct "storeLb" as (t_i offset) "(#prot & #hist & #offset & %tSLe)". *)
    (* We unfold the WP. *)
    iIntros (TV' incl) "Φpost".
    (* iIntros (TV' incl) "Φpost". *)
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".

    iApply wp_extra_state_interp. { done. }
    { apply prim_step_store_rel_no_fork. }

    iIntros "interp".
    iAssert (∃ OCV, crashed_at_offset OCV ∗ ⌜ OCV !!0 ℓ = offset ⌝)%I as (OCV) "[#offsets <-]".
    { iDestruct "offset" as (?) "(? & ? & %)".
      iExists _.
      by iFrame "#". }
    rewrite /is_at_loc /offset_loc.
    iDestruct (interp_get_at_loc with "interp isAtLoc [] offset")
      as (physHists physHist absHist predFull predRead predPers tP) "(R & [reins _])".
    { rewrite /know_protocol. iFrameNamed. }
    iNamed "R".

    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply (@program_logic.crash_weakestpre.wpc_wp).
    iApply @wpc_fupd.
    iApply @program_logic.crash_weakestpre.wp_wpc.

    iApply (wp_store_release_alt with "[$offsets $pts $val]").
    iIntros "!>" (t_t) "(%look & %gt & #valNew & pts)".
    simpl in gt.
    simpl in tSLe.
    (* rewrite drop_prefix_lookup in look. *)

    (* We can conclude that [t_t] is strictly greater than [t_i]. *)
    assert (t_i ≤ store_view TV !!0 ℓ + (OCV !!0 ℓ)) by lia.
    assert (t_i < t_t) as tILtTt.
    { destruct TV as [[??]?].
      destruct TV' as [[??]?].
      destruct incl as [[??]?].
      destruct incl2 as [[??]?].
      eapply Nat.le_lt_trans; last done.
      etrans; first done.
      apply Nat.add_le_mono_r.
      simpl in *.
      f_equiv.
      etrans; done. }

    iFrame "valNew".

    assert (abs_hist !! t_i = Some s_i).
    { eapply map_sequence_lookup_hi in slice.
      rewrite last_snoc in slice.
      apply slice. }
    rewrite monPred_at_big_sepM.
    iDestruct (big_sepM_lookup with "absHist") as "hist"; first done.

    (* rewrite /know_frag_history_loc_d lift_d_at. *)
    iDestruct (know_full_encoded_history_lookup with "fullHist hist") as %look'.
    destruct look' as (e_i & absHistLook' & hip).
    assert (is_Some (physHist !! t_i)) as [vI physHistLook].
    { rewrite -elem_of_dom domEq elem_of_dom. done. }

    (* We must extract the phi for the initial state from "phi". *)

    iDestruct (big_sepM2_delete with "predFullReadHolds") as "[phiI predHolds]";
      [apply physHistLook | done | ].

    iAssert (
      ⌜increasing_map (encode_relation sqsubseteq) (<[(t_t)%nat:=encode s_t]> absHist)⌝
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
                      ∅))%I with "[phiI]" as "phiI". {
        destruct (decide (OCV !!0 ℓ ≤ t_i ∧ physHist !! S t_i = None)) as [ [] | no ].
        - iDestruct (predicate_holds_phi_decode with "predFullEquiv phiI") as "phiI";
            first done.
          iPoseProof (full_read_split with "phiI") as "[phiI _]".
          iFrame.
        - iDestruct (predicate_holds_phi_decode with "predReadEquiv phiI") as "phiI";
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
                 (msg_store_view, msg_persisted_after_view, ∅))%I
        with "[phiC]" as "phiC". {
        destruct (decide (OCV !!0 ℓ ≤ t_c ∧ physHist !! S t_c = None)) as [ [] | no ].
        - iDestruct (predicate_holds_phi_decode with "predFullEquiv phiC") as "phiC";
            first done.
          iPoseProof (full_read_split with "phiC") as "[phiC _]".
          iFrame.
        - iDestruct (predicate_holds_phi_decode with "predReadEquiv phiC") as "phiC";
            first done.
          iFrame.

     }

      iSpecialize ("greater" $! _ s_c _).
      iEval (monPred_simpl) in "greater".

      iSpecialize ("greater" $! TV with "[%] [%]"); [done|done|].
      iEval (monPred_simpl) in "greater".
      iEval (setoid_rewrite monPred_at_pure) in "greater".

      iApply ("greater" $! (TV' ⊔ (_) ⊔ (msg_to_tv vI))).
      { iPureIntro. etrans; first apply incl.
        rewrite -assoc.
        apply thread_view_le_l. }
      monPred_simpl.
      iFrame.
      iSplitL "phiI".
      { iApply monPred_mono; last iApply "phiI".
        apply thread_view_le_r. }
      iSplitL "phi".
      { iApply monPred_mono; last iApply "phi".
        rewrite -assoc.
        etrans; last apply thread_view_le_l. done. }

      iApply monPred_mono; last iApply "phiC".
      rewrite (comm _ TV').
      rewrite -assoc.
      apply thread_view_le_l. }

    iDestruct (big_sepM2_insert_delete with "[phiI $predHolds]") as "predHolds";
      first iFrame.
    rewrite (insert_id physHist t_i); last done.
    rewrite (insert_id absHist t_i); last done.

    (* rewrite drop_prefix_insert. *)

    iMod ("reins" $! (t_t) s_t
      with "[%] [//] [//] [] [] [$] [predHolds phi] [predPersHolds] fullHist [//] pts")
        as "(#frag & #physHistFrag & $)".
    { lia. }
    { iPureIntro. simpl.
      apply lookup_zero_insert. }
    { done. }
    { iApply (big_sepM2_insert_2 with "[phi] [predHolds]").
      { simpl.
        iIntros.
        rewrite lookup_insert_ne; last lia.
        destruct (physHist !! S(t_t)).
        - rewrite decide_False; last naive_solver.
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
        - rewrite decide_True; last (split; [lia | done]).
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
        destruct (decide (OCV !!0 ℓ ≤ t ∧ physHist !! S t = None)) as [ [] | no ].
        - destruct (decide (S t = t_t)) as [ <- | ?].
          + rewrite lookup_insert_eq.
            rewrite decide_False; last naive_solver.
            iSpecialize ("predFullReadSplit" with "H").
            iFrame.
          + rewrite lookup_insert_ne; last lia.
            rewrite decide_True; last done.
            iFrame.
        - rewrite not_and_l in no.
          rewrite decide_False.
          2: {
            rewrite lookup_insert_None.
            intros (? & ? & ?).
            destruct no; [ lia | congruence]. }
          done. } }
    { iDestruct "predPersHolds" as (t_p encσ_p msg_p ? ? ?) "[pview predP]".
      assert (t_p ≠ t_t) by by simplify_map_eq.
      iExists t_p, encσ_p, msg_p.
      do ? (rewrite lookup_insert_ne; last done).
      iFrame.
      done. }
    (* We are done updating ghost state. *)
    iModIntro.
    iSplit. { iPureIntro. simpl. solve_view_le. }

    iEval (rewrite monPred_at_wand) in "Φpost".
    iApply "Φpost".
    - iPureIntro.  solve_view_le.
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
      iSplitL "".
      { rewrite /know_protocol. iFrameNamed. }
      iSplitPure.
      { apply: increasing_map_insert_last; done. }
      iSplit.
      { simpl. rewrite monPred_at_sep. simpl. iFrame "frag".
        rewrite -monPred_at_big_sepM.
        iApply objective_at.
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
      etrans; first apply incl.
      etrans; first apply incl2.
      repeat split; solve_view_le.
      (* missing some thread_view? *)
      Unshelve. all: done.
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
