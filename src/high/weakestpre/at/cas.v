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
  Context `{AbstractState ST}.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, PerennialG Σ}.

  Implicit Types (ℓ : loc) (σ : ST) (prot : LocationProtocol ST).
  
  (** Variables:
   * [σ_i] and [v_i]: the state and value we read last time.
   * [σ_l] and [v_l]: the state and value we read this time.
   * [σ_t] and [v_t]: the state and value we write if successful.
   * [σ_n] and [v_n]: any other "dangling" state not on the main timeline (through write-only operations).
   * [σ_p] and [v_p]: the pview state and value.
   * [Q1]: the success postcondition.
   * [Q2]: the failure postcondition.
   * [Q3]: the failure postcondition outside of fence.
   * [abs_hist'], [phys_hist']: observed history form the [mapsto_at] assertion.
   * [abs_hist], [phys_hist]: complete history from [interp]. *)
  Lemma wp_cmpxchg_at Q1 Q2 Q3 (P R: ST → dProp Σ) σs σ_i ℓ prot `{!ProtocolConditions prot} v_i v_t st E :
    {{{
      ℓ ↦_AT^{prot} (σs ++ [σ_i]) ∗
      (∀ σ_l v_l σ_p v_p,
        (* we know that we won't read older state than [σ_i] *)
        ⌜ σ_i ⊑ σ_l ⌝ -∗
        ((▷ prot.(p_read) σ_l v_l) -∗ ⌜ vals_compare_safe v_i v_l ⌝) ∗
        (( (* in case of success *)
            ⌜ v_l = v_i ⌝ -∗  
            ∃ σ_t,
            (* The state we write fits in the history. *)
            <obj> (prot.(p_full) σ_l v_l -∗ ⌜ σ_l ⊑ σ_t ⌝) ∗
            (∀ σ_n v_n, ⌜ σ_l ⊑ σ_n ⌝ -∗ prot.(p_full) σ_l v_l -∗
                        prot.(p_full) σ_n v_n ∨
                        (prot.(p_read) σ_n v_n ∧
                        ∃ σ_n' v_n', ⌜ σ_n ⊑ σ_n' ⌝ ∗ prot.(p_full) σ_n' v_n') -∗
                        ⌜ σ_t ⊑ σ_n ⌝) ∗
            (* Extract the objective knowledge from [p_pers] *)
            <obj> (prot.(p_pers) σ_p v_p -∗ <obj> P σ_p ∗ (P σ_p -∗ prot.(p_pers) σ_p v_p)) ∗
            (* Extract from the location we load. *)
            <obj> (prot.(p_full) σ_l v_l ∗ P σ_p -∗ prot.(p_read) σ_l v_l ∗ R σ_l) ∗
            (* Establish the invariant for the value we store. *)
            (seen_state ℓ σ_l -∗ R σ_l ==∗ prot.(p_full) σ_t v_t ∗ <obj> P σ_p ∗ Q1 σ_l σ_t))
         ∧ (* in case of failure *)
           ((<obj> (prot.(p_full) σ_l v_l -∗ prot.(p_full) σ_l v_l ∗ Q2 σ_l)) ∗ Q3)
        ))
    }}}
      CmpXchg #ℓ v_i v_t @ st; E
    {{{ v b σ_l σ_t, RET (v, #b);
      (⌜ b = true ⌝ ∗ <fence> Q1 σ_l σ_t ∗ ℓ ↦_AT^{prot} ((σs ++ [σ_i]) ++ [σ_t])) ∨
      (⌜ b = false ⌝ ∗ ⌜ σ_i ⊑ σ_l ⌝ ∗ ℓ ↦_AT^{prot} (σs ++ [σ_i]) ∗ <fence> (Q2 σ_l) ∗ Q3)
    }}}.
  Proof.
    intros Φ.
    iModel.
    iIntros "(pts & impl)".

    iDestruct "pts" as (abs_hist' phys_hist' tLo t_i offset σ' ms) "H". iNamed "H".
    assert (σ' = σ_i) as -> by (rewrite last_snoc in lastEq; simplify_eq; done).
    iDestruct "tSLe" as %tSLe.

    (* We unfold the WP. *)
    iIntros (TV' incl) "Φpost".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".
    iApply wp_extra_state_interp. { done. }
    { apply prim_step_cmpxchg_no_fork. }

    iIntros "interp".
    iAssert (∃ OCV, crashed_at_offset OCV ∗ ⌜ OCV !!0 ℓ = offset ⌝)%I as (OCV) "[#offsets <-]".
    { iDestruct "offset" as (?) "(? & ? & %)".
      iExists _.
      by iFrame "#". }
    
    iDestruct (interp_get_at_loc with "interp isAtLoc locationProtocol offset")
      as (phys_hists phys_hist abs_hist encp_full encp_read encp_pers pview) "(R & reins)".
    iNamed "R".

    set (extra := (Build_extraStateInterp _ _)).
    iApply (@program_logic.crash_weakestpre.wpc_wp).
    iApply @wpc_fupd.
    iApply @program_logic.crash_weakestpre.wp_wpc.

    assert (abs_hist' !! t_i = Some σ_i).
    { eapply map_sequence_lookup_hi in slice.
      rewrite last_snoc in slice.
      apply slice. }

    rewrite ?monPred_at_big_sepM.
    iDestruct (big_sepM_lookup with "absHist") as "hist"; first done.
    iEval (rewrite monPred_at_embed) in "hist".
    iDestruct (history_full_entry_frag_lookup with "fullHist hist")
      as %(encσ_i & Hlookσ_i & Hdecodeσ_i).

    iApply (wp_cmpxchg_alt with "[#] [$offsets $pts $val]").
    (* [val_safe_compare] proof *)
    { iIntros (t_l [v_l SV_l PV_l BV_l] leT physHistLook).
      simpl in leT.

      assert (store_view TV !!0 ℓ ≤ SV !!0 ℓ).
      { f_equiv. solve_view_le. }
      assert (t_i ≤ t_l) as le by lia.

      eassert _ as  temp. { eapply (read_atomic_location t_i t_l (OCV !!0 ℓ)); (done || lia). }
      destruct temp as (σ_l & encσ_l & ? & ? & ? & <- & orderRelated).
      
      iDestruct ("impl" $! _ v_l _ _ orderRelated) as "(safe & _)".
      iEval (monPred_simpl) in "safe".
      iEval (setoid_rewrite monPred_at_pure) in "safe".
      iApply ("safe" $! (TV ⊔ (SV_l, PV_l, ∅)) with "[%]"); first solve_view_le.

      iDestruct (big_sepM2_lookup _ _ _ t_l with "predFullReadHolds") as "predFR". 
      { done. } { done. }
      simpl.
      iAssert (encoded_predicate_holds encp_read encσ_l v_l (SV_l, PV_l, ∅))%I
        with "[predFR]" as "predR".
      { destruct (decide (_)).
        - iDestruct ("predFullReadSplit" with "predFR") as "$".
        - iApply "predFR". }
      
      iNext.
      iDestruct (predicate_holds_phi_decode with "predReadEquiv predR") as "predR";
        first done.
      iApply monPred_mono; last iApply "predR".
      solve_view_le. }
    iEval (simpl).
    iIntros "!>" (t_l v_l SV_l FV_l PV_l SV_t succ) "(%le & #valT & % & % & disj)".
    iFrame "valT".
    iDestruct "disj" as "[H | H]".
    - (* success *)
      iDestruct "H" as "(-> & <- & -> & pts)".
      iDestruct "reins" as "[reins _]".

      (* The loaded timestamp is greater or equal to the one we know of. *)
      assert (store_view TV !!0 ℓ ≤ SV !!0 ℓ).
      { f_equiv. solve_view_le. }
      assert (t_i ≤ t_l) as lte by lia.

      (* [σ_l] *)
      eassert _ as  temp. { eapply (read_atomic_location t_i t_l (OCV !!0 ℓ)); (done || lia). }
      destruct temp as (σ_l & encσ_l & absHistLook & ? & ? & <- & orderRelated).
      iDestruct (big_sepM2_delete with "predFullReadHolds") as "[predF predFullReadRest]";
        [done|done|].
      simpl.
      destruct (decide (_)) as [ ?H | contra ].
      (* we know [t_l] is an exclusive timestamp. *)
      2: { exfalso. apply contra.
           split; first lia. rewrite -Nat.add_1_r //. }
      iDestruct (predicate_holds_phi_decode with "predFullEquiv predF") as "predF";
        first done.

      (* [σ_p] *)
      iDestruct "predPersHolds" as (t_p encσ_p msg_p ? ? ?) "[pview predP]".
      iAssert (⌜ ∃ σ_p, decode encσ_p = Some σ_p ⌝)%I as (σ_p) "%Hdecodeσ_p". {
        iDestruct "predP" as (pred_pers) "[#eqP _]".
        iEval (rewrite discrete_fun_equivI) in "predPersEquiv".
        iSpecialize ("predPersEquiv" $! encσ_p).
        iEval (rewrite discrete_fun_equivI) in "predPersEquiv".
        iSpecialize ("predPersEquiv" $! (msg_val msg_p)).
        iRewrite "predPersEquiv" in "eqP".
        iPoseProof (encode_predicate_decode (p_pers prot) encσ_p (msg_val msg_p) pred_pers with "eqP") as (σ_p) "%decodeSP".
        iExists _. done. }
      iDestruct (predicate_holds_phi_decode with "predPersEquiv predP") as "predP";
        first done.

      iDestruct ("impl" $! _ _ σ_p (msg_val msg_p)) as "impl".
      iDestruct ("impl" $! orderRelated) as "[_ [impl _]]".

      iDestruct ("impl" with "[//]") as (σ_t) "(above & below & P_acc & impl1 & impl2)".
      rewrite ?monPred_at_objectively.
      iDestruct ("above" with "[$]") as "%above".

      iAssert 
        ⌜increasing_map (encode_relation sqsubseteq) (<[(t_l + 1)%nat := encode σ_t]> abs_hist)⌝%I as %incri.
      {
        iApply (bi.pure_mono).
        { apply
            (increasing_map_insert_succ _ _ _ _ (encode σ_t) increasing
                                          absHistLook).
          eapply encode_relation_decode_iff; eauto using decode_encode. }
        iIntros (t_c encσ_c a ?).
        assert (OCV !!0 ℓ < t_c) by lia.

        assert (is_Some (phys_hist !! t_c)) as [[v_c cSV cFV ?] look2].
        { rewrite -elem_of_dom domEq elem_of_dom. done. }

        eassert _ as  temp. { eapply (read_atomic_location_no_inv (t_l) t_c); done || lia. }
        destruct temp as (s_c & encSC & ? & decodeS' & orderRelated2).
        simplify_eq.
        rewrite /encode_relation. rewrite decode_encode. rewrite decodeS'.
        simpl.

        iSpecialize ("below" $! s_c v_c orderRelated2).
        iEval (monPred_simpl) in "below".
        (* we need to justify precondition for the "below" clause,
         * and we need to distinguish whether [t_c] is the max timestamp.
         * but first, we extract the full predicate at max timestamp for both cases. *)
        set t_max := (max_msg phys_hist).
        assert (t_c ≤ t_max) by (apply max_list_elem_of_le, elem_of_elements, elem_of_dom; done).
        assert (is_Some (phys_hist !! t_max)) as [[v_max maxSV maxFV ?] look_max]. {
          apply elem_of_dom.
          rewrite /max_msg.
          apply elem_of_elements.
          apply max_list_elem_of.
          assert (t_c ∈ dom phys_hist) by (apply elem_of_dom; done).
          rewrite elements_empty_iff.
          set_solver.
        }
        assert (is_Some (abs_hist !! t_max)) as [e_max look_max'].
        { rewrite -elem_of_dom -domEq elem_of_dom. done. }
        eassert _ as  temp. { eapply (read_atomic_location_no_inv t_c t_max); try done || lia. }
        destruct temp as (s_max & encMax & ? & decodeSMax & orderRelated_max).
        simplify_eq.
        iDestruct (big_sepM2_delete with "predFullReadRest") as "[predMax predFullReadRest]".
        { rewrite lookup_delete_ne; [apply look_max | lia ]. }
        { rewrite lookup_delete_ne; [apply look_max' | lia]. }
        simpl.
        destruct (decide (_)) as [ ?H | contra ].
        (* we know [t_max] is an exclusive timestamp. *)
        2: { exfalso. apply contra.
             split; first lia.
             rewrite -Nat.add_1_r. apply lookup_max_msg_succ. }
        iDestruct (predicate_holds_phi_decode with "predFullEquiv predMax") as "predMax";
          first done.
        (* we now case analysis whether [t_c] is the final timestamp *)
        destruct (decide (t_c = t_max)) as [ <- | ].
        - (* in case [t_c] is max timestamp, we do not need to extract further go with the left branch. *)
          simplify_map_eq.
          iApply ("below" $! (TV ⊔ (SV_l, FV_l, ∅) ⊔ (_, _, _)) with "[%] [predF] [predMax]").
          { rewrite -assoc. apply thread_view_le_l. }
          2: { iLeft. iApply monPred_mono; last iApply "predMax".
               apply thread_view_le_r. }
          { iApply monPred_mono; last iApply "predF".
            destruct TV as [[??]?].
            rewrite thread_view_lub.
            solve_view_le. }
        - (* in case [t_c] is not max timestamp, we need to extract [p_read] for it and
           *  go with the right branch. *)
          iDestruct (big_sepM2_lookup _ _ _ t_c with "predFullReadRest") as "predFR". 
          { rewrite 2?lookup_delete_ne; [apply look2 | lia | lia ]. }
          { rewrite 2?lookup_delete_ne; [apply a | lia | lia ]. }
          simpl.
          iAssert (p_read prot s_c v_c (cSV, msg_persisted_after_view, ∅))%I
            with "[predFR]" as "predC".
          { iApply (predicate_holds_phi_decode with "predReadEquiv"); first done.
            destruct (decide (_)).
            - iDestruct ("predFullReadSplit" with "predFR") as "$".
            - iApply "predFR". }
          iAssert (((_ ∗ _): dProp Σ) (_ ⊔ _))%I with "[predC predMax]" as "pred". {
            rewrite monPred_at_sep.
            iSplitL "predC".
            { iApply monPred_mono; [ | iAccu ].
              apply thread_view_le_l. }
            { iSimpl in "predMax". iApply monPred_mono; [ | iAccu ].
              apply thread_view_le_r. }
          }
          iDestruct (monPred_at_sep with "pred") as "[predC predMax]".
          iApply ("below" $! (TV ⊔ (SV_l, FV_l, ∅) ⊔ (_, _, _)) with "[%] [predF] [predC predMax]").
          { rewrite -assoc. apply thread_view_le_l. }
          2: { iRight.
               iSplitL "predC".
               { iApply monPred_mono; last iFrame.
                 apply thread_view_le_r. }
               iExists s_max, v_max.
               iFrame "%".
               iApply monPred_mono; last iFrame.
               apply thread_view_le_r. }
          { iApply monPred_mono; last iApply "predF".
            destruct TV as [[??]?].
            rewrite thread_view_lub.
            solve_view_le. } }
      set view_l := (SV_l, _, _).
      set msg_t := (msg in <[t_l + 1 := msg]> _).

      (* we extract the objective fraction from [p_pers] *)
      iDestruct ("P_acc" with "predP") as "[P P_acc]".
      rewrite monPred_at_objectively.

      iDestruct ("impl1" $! view_l with "[predF P]") as "[predR R]".
      { iSplitL "predF"; last done.
        iApply (monPred_mono with "[$]").
        solve_view_le. }

      iEval (monPred_simpl) in "impl2".
      (* collect information for [seen_state]. *)
      iMod (auth_map_map_lookup _ _ _ _ t_l with "physHists") as "[physHists #know_msg_l]".
      { done. } { done. }
      iAssert (know_frag_history_loc ℓ t_l σ_l)%I as "#know_σ_l".
      { rewrite /know_frag_history_loc /frag_entry_unenc.
        iExists encσ_l.
        iPoseProof (big_sepM_lookup _ _ t_l with "frags") as "$"; done. }
      
      iDestruct ("impl2" $! (view_l ⊔ TV) with "[] [] [R]") as "> (predF & P & Q)".
      { iPureIntro. apply thread_view_le_r. }
      { iExists _, (OCV !!0 ℓ), (Msg v_l SV_l FV_l FV_l).
        destruct (TV) as [[??]?].
        iFrameF "know_σ_l".
        iFrameF "offset".
        iSplitPure.
        { simpl.
          rewrite lookup_zero_lub.
          lia. }
        iFrameF "know_msg_l".
        iPureIntro.
        subst view_l.
        simpl.
        solve_view_le. }
      { iApply monPred_mono; last iApply "R". apply thread_view_le_l. }

      (* we recover [P_pers] from the objective fragment *)
      iEval (rewrite monPred_at_wand) in "P_acc".
      iEval (rewrite monPred_at_objectively) in "P".
      iDestruct ("P_acc" with "[//] P") as "predP".

      iMod ("reins" $! (t_l + 1) σ_t
        with "[%] [//] [//] [] [] physHists [predFullReadRest predR predF] [pview predP] fullHist [//] pts")
          as "(#frag & #physHistFrag & $)".
      { lia. }
      { iPureIntro. simpl. rewrite lookup_zero_insert. lia. }
      { done. }
      { (* We insert [predR] first by temporarily hack the internal lookup of [phys_hist] *)
        iAssert ([∗ map] t ↦ msg;encσ ∈ (delete t_l phys_hist); (delete t_l abs_hist), 
                   if decide (OCV !!0 ℓ ≤ t ∧ phys_hist !! S t = None ∧ t ≠ t_l)
                   then
                     encoded_predicate_holds encp_full encσ (msg_val msg)
                       (msg_store_view msg, msg_persisted_after_view msg, ∅)
                   else
                     encoded_predicate_holds encp_read encσ (msg_val msg)
                       (msg_store_view msg, msg_persisted_after_view msg, ∅))%I
          with "[predFullReadRest]" as "predFullReadHolds".
        { iApply (big_sepM2_impl with "predFullReadRest").
          iIntros "!>" (t msg encσ look1 look2) "H".
          assert (t ≠ t_l). {
            intro eq.
            simplify_eq.
            rewrite lookup_delete // in look1. }
          destruct (decide _); destruct (decide _); naive_solver. }
        
        (* We now insert [predR]. *)
        iPoseProof (big_sepM2_insert_delete _ _ _ _ (Msg _ _ _ _) with "[$predFullReadHolds predR]")
          as "predFullReadHolds".
        { destruct (decide _) as [ [_ [_ []]] | ]; first done.
          iApply (predicate_holds_phi_decode_2 with "predReadEquiv predR"); first done. }
        
        (* We now insert the [predF]. *)
        iPoseProof (big_sepM2_insert _ _ _ (t_l + 1) msg_t with "[$predFullReadHolds predF]")
          as "predFullReadHolds".
        { rewrite lookup_insert_ne //. lia. }
        { rewrite -not_elem_of_dom dom_insert -domEq not_elem_of_union not_elem_of_dom.
          split; last set_solver.
          apply not_elem_of_singleton.
          lia. }
        { destruct TV as [[? ?] ?].
          iDestruct (into_no_buffer_at with "predF") as "predF".
          { apply full_nobuf. }
          destruct (decide _).
          - iApply (predicate_holds_phi with "predFullEquiv"); first reflexivity.
            iApply (monPred_mono with "predF").
            subst msg_t.
            repeat split; last done.
            * eapply view_lub_le; solve_view_le.
            * solve_view_le.
          - iApply (predicate_holds_phi with "predReadEquiv"); first reflexivity.
            iPoseProof (full_read_split with "predF") as "[predR _]".
            iApply (monPred_mono with "predR").
            subst msg_t.
            repeat split; last done.
            * eapply view_lub_le; solve_view_le.
            * solve_view_le. }
        rewrite (insert_id phys_hist) // (insert_id abs_hist) //.
        iApply (big_sepM2_impl with "[$]").
        iIntros (t msg encσ msgLook encSLook) "!> H".
        destruct (decide (t = t_l)) as [ -> | neq ].
        - rewrite ?Nat.add_1_r lookup_insert.
          rewrite ?decide_False; naive_solver.
        - rewrite lookup_insert_ne; last lia.
          destruct (decide _); destruct (decide _); naive_solver. }
      { iExists t_p, encσ_p, msg_p.
        assert (t_p ≠ t_l + 1).
        { intro eq.
          rewrite -> eq in *.
          simplify_map_eq.
          (* TODO: make this hypothesis named. *)
          rewrite H10 // in H4. }
        rewrite ?lookup_insert_ne //.
        iFrame "∗".
        repeat (iSplitPure; first done).
        by iApply (predicate_holds_phi_decode_2 with "[//] predP"). }
      iModIntro.

      iSplitPure. { solve_view_le. }

      Opaque mapsto_at seen_state.
      
      iSpecialize ("Φpost" $! _ true σ_l σ_t).
      iEval (monPred_simpl) in "Φpost".
      iApply "Φpost".
      { iPureIntro. solve_view_le. }
      iLeft.
      iSplitPure; first done.
      iSplitL "Q".
      { subst view_l.
        rewrite /post_fence. simpl.
        iApply monPred_mono; last iApply "Q".
        repeat destruct_thread_view; repeat destruct_thread_view_le.
        rewrite thread_view_lub.
        assert (SV ⊔ SV_l ⊑ <[ℓ:=MaxNat (t_l - (OCV !!0 ℓ) + 1)]> (SV ⊔ SV_l)) as le2.
        { apply view_insert_le. rewrite lookup_zero_lub. lia. }
        apply thread_view_le.
        - etrans; last apply le2. solve_view_le.
        - apply view_lub_le; solve_view_le.
        - simpl_view. solve_view_le. }
      (* [mapsto_at] *)
      iExists _, _, _, (t_l + 1). iExistsN.
      iSplitPure. { rewrite last_snoc. reflexivity. }
      iSplitPure. { eapply map_sequence_insert_snoc; try done. lia. }
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
      iFrameF "locationProtocol".
      iSplitPure.
      { apply: increasing_map_insert_last; try done. lia.
        etrans; done. }
      iSplit.
      (* { iFrame "frag absHist". } *)
      { simpl. rewrite monPred_at_sep. simpl. iFrame "frag".
        rewrite -monPred_at_big_sepM.
        iApply objective_at.
        rewrite monPred_at_big_sepM.
        iEval (rewrite monPred_at_big_sepM).
        simpl.
        iFrame "absHist". }
      iFrame "offset".
      iSplit; last first.
      { simpl. iPureIntro.
        rewrite lookup_zero_insert.
        lia. }
      simpl.

      iSplit.
      { simpl. iFrame "physHistFrag". solve_view_le. }
      rewrite -?monPred_at_big_sepM.
      iApply monPred_mono; last iApply "physHist".
      etrans; first apply incl.
      etrans; first apply incl2.
      repeat split; solve_view_le.
    - (* failure *)
      iDestruct "H" as "(-> & -> & pts)".
      iDestruct "reins" as "[_ reins]".
      iModIntro.

      (* The loaded timestamp is greater or equal to the one we know of. *)
      assert (store_view TV !!0 ℓ ≤ SV !!0 ℓ).
      { f_equiv. solve_view_le. }
      assert (t_i ≤ t_l) as lte by lia.

      eassert _ as  temp. { eapply (read_atomic_location t_i t_l (OCV !!0 ℓ)); (done || lia). }
      destruct temp as (σ_l & encσ_l & ? & ? & ? & <- & orderRelated).

      iDestruct (big_sepM2_lookup_acc with "predFullReadHolds") as "[predFR predFullReadHolds]";
        [done|done|].
      simpl.
      destruct (decide (_)) as [ ?H | contra ].
      (* we know [t_l] is an exclusive timestamp. *)
      2: { exfalso. apply contra.
           split; first lia. rewrite -Nat.add_1_r //. }
      
      iDestruct (predicate_holds_phi_decode with "predFullEquiv predFR") as "predF";
        first done.

      iDestruct ("impl" $! _ _ _ _ orderRelated) as "[_ [_ [impl Q3]]]".
      iEval (rewrite monPred_at_objectively) in "impl".
      iSpecialize ("impl" $! (∅, ∅, ∅)).
      iEval (monPred_simpl) in "impl".
      iDestruct ("impl" $! _ with "[%] predF") as "[predF Q2]"; first solve_view_le.
      
      iSpecialize ("predFullReadHolds" with "[predF]").
      { iApply predicate_holds_phi_decode; done. }

      iDestruct ("reins" with "[$] [$] [$] [$] [$]") as "$".

      iSplitPure. { repeat split; try done; apply view_le_l. }

      iSpecialize ("Φpost" $! _ false σ_l _).
      iEval (monPred_simpl) in "Φpost".
      iApply "Φpost".

      { iPureIntro.
        etrans; first done.
        repeat split; auto using view_le_l. }
      iRight.
      iSplitPure; first done.
      iSplitPure; first done.
      rewrite /post_fence. simpl.
      iSplit.
      { (* We show what is, essentially, the points-to predicate that we started with. *)
        iExistsN.
        iFrameF (lastEq).
        iFrameF (slice).
        iFrameF (slicePhys).
        iFrameF (nolater).
        iFrameF (absPhysHistDomEq).
        iFrameF "isAtLoc".
        iFrameF "locationProtocol".
        iSplitPure; first done.
        iSplit.
        { iApply objective_at.
          iEval (rewrite monPred_at_big_sepM).
          iFrame "absHist". }
        iSplit.
        { iEval (rewrite -monPred_at_big_sepM) in "physHist".
          iApply monPred_mono; last iApply "physHist".
          etrans; first apply incl.
          etrans; first apply incl2.
          solve_view_le. }
        iFrameF "offset".
        iPureIntro.
        etrans; first apply tSLe.
        simpl.
        f_equiv.
        solve_view_le. }
      iSplitL "Q2"; iApply monPred_mono; try iFrame.
      { repeat split; eauto using view_le_r, view_empty_least.
        rewrite assoc. apply view_le_r. }
      { etrans; first done. etrans; first done. repeat split; auto using view_le_l. }
      (* these shelved goals seem to be [s_p] and [v_p] for the safe comparison and failure case
       * it's probably better to rewrite the quantifiers, but not an important problem *)
      Unshelve. all: done.
  Qed.

  (** [Q1] is the resource we want to extract in case of success and and [Q2] is *)
  (** the resource we want to extract in case of failure. *)
  Lemma wp_cas_at Q1 Q2 Q3 (P R: ST → dProp Σ) σs σ_i ℓ prot `{!ProtocolConditions prot} v_i v_t st E :
    {{{
      ℓ ↦_AT^{prot} (σs ++ [σ_i]) ∗
      (∀ σ_l v_l σ_p v_p,
        (* we know that we won't read older state than [σ_i] *)
        ⌜ σ_i ⊑ σ_l ⌝ -∗
        ((▷ prot.(p_read) σ_l v_l) -∗ ⌜ vals_compare_safe v_i v_l ⌝) ∗
        (( (* in case of success *)
            ⌜ v_l = v_i ⌝ -∗
            ∃ σ_t,
            (* The state we write fits in the history. *)
            <obj> (prot.(p_full) σ_l v_l -∗ ⌜ σ_l ⊑ σ_t ⌝) ∗
            (∀ σ_n v_n, ⌜ σ_l ⊑ σ_n ⌝ -∗ prot.(p_full) σ_l v_l -∗
                        prot.(p_full) σ_n v_n ∨
                        (prot.(p_read) σ_n v_n ∧
                        ∃ σ_n' v_n', ⌜ σ_n ⊑ σ_n' ⌝ ∗ prot.(p_full) σ_n' v_n') -∗
                        ⌜ σ_t ⊑ σ_n ⌝) ∗
            (* Extract the objective knowledge from [p_pers] *)
            <obj> (prot.(p_pers) σ_p v_p -∗ <obj> P σ_p ∗ (P σ_p -∗ prot.(p_pers) σ_p v_p)) ∗
            (* Extract from the location we load. *)
            <obj> (prot.(p_full) σ_l v_l ∗ P σ_p -∗ prot.(p_read) σ_l v_l ∗ R σ_l) ∗
            (* Establish the invariant for the value we store. *)
            (seen_state ℓ σ_l -∗ R σ_l ==∗ prot.(p_full) σ_t v_t ∗ <obj> P σ_p ∗ Q1 σ_l σ_t))
         ∧ (* in case of failure *)
           ((<obj> (prot.(p_full) σ_l v_l -∗ prot.(p_full) σ_l v_l ∗ Q2 σ_l)) ∗ Q3)
        ))
    }}}
      CAS #ℓ v_i v_t @ st; E
    {{{ b σ_l σ_t, RET #b;
      (⌜ b = true ⌝ ∗ <fence> Q1 σ_l σ_t ∗ ℓ ↦_AT^{prot} ((σs ++ [σ_i]) ++ [σ_t])) ∨
      (⌜ b = false ⌝ ∗ ⌜ σ_i ⊑ σ_l ⌝ ∗ ℓ ↦_AT^{prot} (σs ++ [σ_i]) ∗ <fence> (Q2 σ_l) ∗ Q3)
    }}}.
  Proof.
    intros Φ.
    iIntros "H Φpost".
    iApply (wp_bind ([SndCtx])).
    iApply (wp_cmpxchg_at with "H").
    iIntros "!>" (v b σ_l σ_t) "disj /=".
    iApply wp_pure_step_later; first done.
    iNext.
    iApply wp_value.
    iApply "Φpost".
    iApply "disj".
  Qed.
End wp_at.
