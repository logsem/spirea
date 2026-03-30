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

  Lemma map_sequence_big_sepM_sepL {A} (m : gmap nat A) lo hi ss (ϕ : A  → iProp Σ) :
    map_sequence m lo hi ss →
    ([∗ map] k ↦ y ∈ m, ϕ y) -∗
    ([∗ list] y ∈ ss, ϕ y) ∗ (([∗ list] y ∈ ss, ϕ y) -∗ [∗ map] k ↦ y ∈ m, ϕ y).
  Proof.
    generalize dependent m.
    generalize dependent lo.
    induction ss as [|x ss' IH]; first done.
    iIntros (lo m seq) "M".
    destruct ss' as [|x2 ss''].
    { destruct seq as [look ->]. rewrite /= right_id.
      iApply (big_sepM_lookup_acc with "M"). done. }
    simpl.
    destruct seq as (look & lo2 & ? & ? & ?).
    iDestruct (big_sepM_delete with "M") as "[$ M]"; first done.
    iDestruct (IH lo2 with "M") as "[horse bing]".
    { apply map_sequence_delete_below; done. }
    simpl.
    iFrame "horse".
    iIntros "[Hx Hx2]".
    iDestruct ("bing" with "Hx2") as "H2".
    iApply big_sepM_delete; first done.
    iFrame.
  Qed.

  Lemma map_sequence_big_sepM2_sepL2 {A B}
    (m1 : gmap nat A) (m2 : gmap nat B) tLo tHi ss ms
    (ϕ : A  → B → iProp Σ) :
    map_sequence m1 tLo tHi ss →
    map_sequence m2 tLo tHi ms →
    ([∗ map] k ↦ y1;y2 ∈ m1;m2, ϕ y1 y2) -∗
    ([∗ list] y1;y2 ∈ ss;ms, ϕ y1 y2) ∗
    (([∗ list] y1;y2 ∈ ss;ms, ϕ y1 y2) -∗ [∗ map] k ↦ y1;y2 ∈ m1;m2, ϕ y1 y2).
  Proof.
    iIntros (seq1 seq2).
    rewrite big_sepM2_alt.
    rewrite big_sepL2_alt.
    iIntros "(%domEq & M)".
    assert (length ss = length ms) as lenEq.
    { eapply map_sequence_dom_length; done. }
    iFrame (lenEq).
    iDestruct (map_sequence_big_sepM_sepL with "M") as "[L Lreins]".
    { apply map_sequence_zip; done. }
    iFrame "L".
    iIntros "[_ L]".
    iDestruct ("Lreins" with "L") as "$".
    iPureIntro. done.
  Qed.

  (* Lemma bingo {A B} (m1 : gmap nat A) (m2 : gmap nat B) tLo tHi ss ms *)
  (*   (ϕ : A  → B → dProp Σ) : *)
  (*   map_sequence m1 tLo tHi ss → *)
  (*   map_sequence m2 tLo tHi ms → *)
  (*   ⊢ ([∗ list] y1;y2 ∈ ss;ms, ϕ y1 y2) ∗-∗ ([∗ map] k ↦ y1;y2 ∈ m1;m2, ϕ y1 y2). *)
  (* Proof. *)
  (*   iIntros (seq1 seq2). *)
  (* Qed. *)

  (* Lemma big_sepM2_union {A B} (Φ : nat → A → B → iProp Σ) (m1 m2 : gmap nat A) *)
  (*     (n1 n2 : gmap nat B) : *)
  (*   m1 ##ₘ m2 → *)
  (*   n1 ##ₘ n2 → *)
  (*   ([∗ map] k↦y1;y2 ∈ (m1 ∪ m2);(n1 ∪ n2), Φ k y1 y2) *)
  (*   ⊣⊢ ([∗ map] k↦y1;y2 ∈ m1;n1, Φ k y1 y2) ∗ ([∗ map] k↦y1;y2 ∈ m2;n2, Φ k y1 y2). *)
  (* Proof. *)
  (*   intros disj1 disj2. *)
  (*   rewrite !big_sepM2_alt. *)
  (*   rewrite big_sepM_union. *)
  (*   apply big_opM_union. *)
  (* Qed. *)

  (* Lemma bingobongo (ϕ : ST → _) (pred : enc_predicateO) physHist absHist *)
  (*     encAbsHist fullEncAbsHist : *)
  (*   absHist = omap decode encAbsHist → *)
  (*   encAbsHist ⊆ fullEncAbsHist → *)
  (*   (pred ≡ encode_predicate ϕ) -∗ *)
  (*   encoded_predicate_hold physHist fullEncAbsHist pred -∗ *)
  (*   ([∗ map] msg;s ∈ physHist;absHist, *)
  (*     ϕ s (msg_val msg) _ (msg_store_view msg, msg_persisted_after_view msg, ∅)). *)

  Definition fold_views (m : history) :=
    map_fold
      (λ _ msg (TV : thread_view),
        (msg_store_view msg, msg_persisted_after_view msg, ∅) ⊔ TV) (∅, ∅, ∅) m.

  Lemma fold_views_in_phys_hist phys_hist t msg :
    phys_hist !! t = Some msg →
    (msg_store_view msg, msg_persisted_after_view msg, ∅) ⊑ fold_views phys_hist.
  Proof.
    rewrite /fold_views. simpl.
    apply (map_fold_ind (λ res phys_hist, phys_hist !! t = Some msg → _ ⊑ res)).
    - inversion 1.
    - intros t2 ???? IH.
      destruct (decide (t = t2)) as [->|ne].
      * rewrite lookup_insert_eq.
        inversion 1.
        apply thread_view_le_l.
      * rewrite lookup_insert_ne; last done.
        rewrite -thread_view_le_r.
        apply IH.
  Qed.

  (* This lemma extracts a list of predicates held over all existing
   * timestamps. This is only true for [read] predicates in the new model.
   * *)
  Lemma extract_list_of_preds abs_hist (phys_hist : history) tLo tS ss ms prot ℓ encAbsHist (predRead : enc_predicateO) :
    abs_hist = omap decode encAbsHist →
    map_sequence abs_hist tLo tS ss →
    map_sequence phys_hist tLo tS ms →
    dom abs_hist = dom phys_hist →
    predRead ≡ encode_predicate (p_read prot) -∗
    ([∗ map] t↦msg;encS ∈ phys_hist; encAbsHist, encoded_predicate_holds predRead encS
                                                   (msg_val msg)
                                                   (msg_store_view msg,
                                                    msg_persisted_after_view msg, ∅)) -∗
    ([∗ list] s;v ∈ ss;(msg_val <$> ms), p_read prot s v) (fold_views phys_hist).
  Proof.
    iIntros (-> seqAbs seqPhys domEq) "#equiv P".
    iDestruct (big_sepM2_impl_dom_subseteq _ _ _ _ phys_hist (omap decode encAbsHist) with "P []") as "P".
    { done. }
    { done. }
    { iIntros "!>" (t m es m2 s ? encLook ? look) "H".
      apply lookup_omap_Some in look as (? & ? & ?).
      assert (m = m2) as <- by congruence.
      assert (es = x) as <- by congruence.
      iDestruct (predicate_holds_phi_decode_1 with "equiv H") as "H"; first done.
      iApply "H". }
    iDestruct (map_sequence_big_sepM2_sepL2 with "P") as "[P Lreins]"; first done.
    { done. }
    rewrite big_sepL2_flip.
    rewrite monPred_at_big_sepL2.
    rewrite big_sepL2_fmap_r.
    iApply (big_sepL2_impl with "P").
    iIntros "!>" (idx s msg ? msLook) "pred".
    iApply monPred_mono; last iApply "pred".
    eapply map_sequence_list_lookup in msLook as (? & ? & look); last apply seqPhys.
    eapply fold_views_in_phys_hist.
    done.
  Qed.

  Lemma wp_load_at ℓ ss s Q1 Q2 prot `{!ProtocolConditions prot} st E :
    {{{
      ℓ ↦_AT^{prot} (ss ++ [s]) ∗
      (* The case where we read an already known write. *)
      ((∀ vs vL, ∃ P (_ : Objective P) (_ : Persistent P),
        ⌜ last vs = Some vL ⌝ -∗
        (* Extract knowledge from all the predicates. *)
        (([∗ list] s; v ∈ ss ++ [s];vs, prot.(p_read) s v) -∗ P) ∗
        (* Using the [P] and the predicate for the loaded location show [Q1]. *)
        (P -∗ <obj> (prot.(p_read) s vL -∗ Q1 vL ∗ prot.(p_read) s vL))) ∧
      (* The case where we read a new write. *)
      (∀ vs vL sL, ∃ P (_ : Objective P) (_ : Persistent P),
        ⌜ s ⊑ sL ⌝ -∗
        (* Extract knowledge from all the predicates. *)
        (([∗ list] s; v ∈ (ss ++ [s]) ++ [sL];vs ++ [vL], prot.(p_read) s v) -∗ P) ∗
        (P -∗ <obj> (prot.(p_read) sL vL -∗ Q2 sL vL ∗ prot.(p_read) sL vL))))
    }}}
      !_AT #ℓ @ st; E
    {{{ vL, RET vL;
      (∃ sL, ℓ ↦_AT^{prot} ((ss ++ [s]) ++ [sL]) ∗ <fence> Q2 sL vL) ∨
      (* We didn't have to give the points-to predicate back here, but doing
       * that is useful for users of the lemma. *)
      (ℓ ↦_AT^{prot} (ss ++ [s]) ∗ <fence> Q1 vL)
    }}}.
  Proof.
    intros Φ.
    iModel.
    iDestruct 1 as "(#pts & pToQ)".
    iAssert (_) as "ptsCopy". { iApply "pts". }
    iDestruct "pts" as (abs_hist phys_hist tLo tS offset s' ms) "H". iNamed "H".
    assert (s' = s) as ->. { apply (inj Some). rewrite -lastEq. apply last_snoc. }
    iDestruct "tSLe" as %tSLe.
    (* iDestruct (store_lb_protocol with "storeLb") as "#knowProt". *)
    iNamed "locationProtocol".
    (* rewrite /store_lb. *)
    (* iDestruct "storeLb" as (tS offset) "(#prot & #hist & #offset & %tSLe)". *)

    (* We unfold the WP. *)
    iIntros (TV' incl) "Φpost".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".

    iApply wp_extra_state_interp. { done. } { by apply prim_step_load_acq_no_fork. }

    (* We open [interp]. *)
    iIntros "interp".
    iAssert (∃ OCV, crashed_at_offset OCV ∗ ⌜ OCV !!0 ℓ = offset ⌝)%I as (OCV) "[#offsets <-]".
    { iDestruct "offset" as (?) "(? & ? & %)".
      iExists _.
      by iFrame "#". }
    simpl.
    iDestruct (interp_get_at_loc with "interp isAtLoc [] offset")
      as (phys_hists phys_hist' abs_hist' encp_full encp_read encp_pers pview) "(R & reins)".
    { rewrite /know_protocol. iFrameNamed. }

    iNamed "R".
    iEval (rewrite monPred_at_big_sepM) in "physHist".
    iEval (rewrite monPred_at_big_sepM) in "absHist".
    iEval (setoid_rewrite monPred_at_sep) in "physHist".
    simpl.
    setoid_rewrite monPred_at_embed.

    iAssert (⌜ phys_hist ⊆ phys_hist' ⌝)%I as %sub.
    { rewrite map_subseteq_spec.
      iIntros (?? physHistLook).

      iDestruct (big_sepM_lookup with "physHist") as "[hi frag]"; first done.
      iDestruct (auth_map_map_auth_frag with "physHists frag") as %(phys_hist'' & ? & ?).
      assert (phys_hist' = phys_hist'') as <-.
      { apply (inj Some). rewrite -physHistsLook. done. }
      done. }

    iDestruct (know_full_encoded_history_lookup_big with "fullHist absHist")
      as %(encAbsHist & subset & domEq2 & eqeq & map).

    (* We add this to prevent Coq from trying to use [highExtraStateInterp]. *)
    set (extra := (Build_extraStateInterp _ _)).
    iApply (@program_logic.crash_weakestpre.wpc_wp).
    iApply @wpc_fupd.
    iApply @program_logic.crash_weakestpre.wp_wpc.

    iApply (wp_load_acquire_alt (extra := {| extra_state_interp := True |})
             with "[$offsets $pts $val]").
    iIntros "!>" (tL vL SV' PV' _PV') "(%look & %gt & #val' & pts)".

    iFrame "val'".

    assert (store_view TV !!0 ℓ ≤ SV !!0 ℓ).
    { f_equiv. solve_view_le. }
    assert (tS ≤ tL) as lte by lia.
    
    assert (abs_hist !! tS = Some s).
    { rewrite -lastEq. eapply map_sequence_lookup_hi; done. }
    iDestruct (big_sepM_lookup with "absHist") as "hist"; first done.
    iDestruct (know_full_encoded_history_lookup with "fullHist hist")
      as %(enc & lookTS & decodeEnc).

    rewrite <- pure_sep_l; last solve_view_le.

    (* The final view under the post fence modality where we will have to show
     * [Q]. *)
    set (TVfinal := (SV ⊔ SV', PV ⊔ (BV ⊔ PV'), BV ⊔ PV')).
    assert (TV ⊑ TVfinal).
    { etrans; first apply incl. etrans; first apply incl2.
      rewrite /TVfinal.
      solve_view_le. }

    (*
    (* All the messages in the physical history are included in [TVfinal]. *)
    iAssert (
      ⌜ map_Forall
        (λ (_ : nat) (msg : message),
           msg_store_view msg ⊑ store_view TVfinal
           ∧ msg_persisted_after_view msg ⊑ flush_view TVfinal) phys_hist ⌝
    )%I as %inTVFinal.
    { iIntros (? msg looki).
      iDestruct (big_sepM_lookup with "physHist") as "[[%have %have2] _]"; first done.
      iPureIntro.
      split.
      - solve_view_le.
      - etrans; first apply have2. rewrite /TVfinal.
        simpl.
        destruct TV as [[??]?].
        destruct TV' as [[??]?].
        simpl.
        apply view_lub_le.
        * solve_view_le.
        * solve_view_le. }
    *)

    destruct (decide (tS = tL)) as [eq|neq].
    - iDestruct "pToQ" as "[pToQ _]".
      subst.

      assert (last (msg_val <$> ms) = Some vL).
      { rewrite fmap_last.
        apply map_sequence_lookup_hi_alt in slicePhys
          as (msg & physHistLook & ->).
        eapply map_subseteq_spec in sub; last done.
        rewrite -sub. rewrite look. done. }

      iDestruct ("pToQ" $! (msg_val <$> ms) vL) as (P ? ?) "pToQ".
      iDestruct ("pToQ" with "[]") as "[getP getQ]".
      { iPureIntro. done. }

      iEval (monPred_simpl) in "getP".
      iDestruct ("getP" $! (TV ⊔ _) with "[%] [-]") as "#P".
      { apply thread_view_le_l. }
      { (* Here's the reason we are not merging the two predicates in the lemma:
         * [phys_hist] is the history known to local thread,
         * [physHist] is the complete history obtained from [interp].
         * whether we get [predFull] or [predRead] depends on [physHist],
         * but the list of holding predicates we want to obtain is from [phys_hist]
         * which means the [extract_list_of_preds] lemma would
         * otherwise need to take both of them to work *)
        iDestruct (extract_list_of_preds
          with "predReadEquiv [predFullReadHolds]") as "L"; try done.
        - iPoseProof (big_sepM2_impl_subseteq with "predFullReadHolds") as "P"; try done.
          { rewrite -domEq2.
            rewrite absPhysHistDomEq.
            done. }
          { iApply (big_sepM2_impl with "P").
            iIntros "!> %t %msg %encS %physHistLook %absHistLook predFR".
            destruct (decide (OCV !!0 ℓ ≤ t ∧ phys_hist' !! S t = None)) as [ [] | no ].
            { assert (is_Some (@decode ST _ _ encS)) as [? ?]. {
                replace (decode encS) with (encAbsHist !! t ≫= @decode ST _ _) by by rewrite absHistLook.
                rewrite -lookup_omap.
                rewrite -elem_of_dom.
                rewrite domEq2.
                by rewrite elem_of_dom.
              }
              iPoseProof (predicate_holds_phi_decode_1 with "predFullEquiv predFR") as "H"; first done.
              iPoseProof (full_read_split with "H") as "[Hread _]".
              iApply (predicate_holds_phi_decode_2 with "predReadEquiv Hread"); first done.
            }
            { iApply "predFR". } }
        - iApply monPred_mono; last done.
          apply thread_view_le_r. }
      iEval (monPred_simpl) in "getQ".
      iDestruct ("getQ" with "[%] [P]") as "bing"; first done.
      { iApply objective_at. iApply "P". }
      rewrite monPred_at_objectively.

      eassert _ as temp.
      { eapply map_Forall_lookup_1; first apply atInvs.
        replace tL with (tL - (OCV !!0 ℓ) + (OCV !!0 ℓ)) in look by lia.
        rewrite drop_prefix_lookup. done. }
      simpl.
      destruct temp as (? & pvEq).
      simpl in pvEq.

      iAssert (at_encoded_full_read_predicates_hold abs_hist' phys_hist' (OCV !!0 ℓ) encp_full encp_read ∗
               Q1 vL (SV', _PV', ∅))%I with "[predFullReadHolds bing]"
        as "[predFullReadHolds Q]". {
        (* we now attempt to obtain [p_read] at [tL +  offset]. *)
        (* again, we need to case distinction over whether it's held at full or read. *)
        iDestruct (big_sepM2_lookup_acc with "predFullReadHolds") as "[predFR predMap]".
        { done. } { done. }
        simpl.
        destruct (decide _) as [[] | no ].
        - iDestruct (predicate_holds_phi_decode with "predFullEquiv predFR") as "PH";
            first done.

          iPoseProof (full_read_split with "PH") as "[PH Prestore]".

          iDestruct ("bing" $! _ with "PH") as "[Q predHolds]".

          iSpecialize ("Prestore" with "predHolds").

          iDestruct ("predMap" with "[Prestore]") as "predMap".
          { iIntros.
            iApply (predicate_holds_phi_decode with "predFullEquiv Prestore").
            assumption. }
          iFrame.
        - iDestruct (predicate_holds_phi_decode with "predReadEquiv predFR") as "PH";
            first done.

          iDestruct ("bing" $! _ with "PH") as "[Q predHolds]".

          iDestruct ("predMap" with "[predHolds]") as "predMap".
          { iIntros.
            iApply (predicate_holds_phi_decode with "predReadEquiv predHolds").
            assumption. }
          iFrame. }
      iModIntro.

      (* We re-establish [interp]. *)
      iDestruct ("reins" with "[$] [$] [$] [$] [$]") as "$".

      iSpecialize ("Φpost" $! vL).
      monPred_simpl.
      iApply "Φpost".
      { iPureIntro.
        etrans. eassumption.
        repeat split; try done; try apply view_le_l. }
      (* The thread view we started with [TV] is smaller than the view we ended
       * with. *)
      (* assert (TV ⊑ (SV ⊔ SV', PV, BV ⊔ PV')).
           { clear H4. do 2 (etrans; first done). repeat split; auto using view_le_l. }
       *)
      iRight. simpl.
      iSplit. {
        (* We show what is, essentially, the points-to predicate that we started with. *)
        iExistsN.
        iFrameF (lastEq).
        iFrameF (slice).
        iFrameF (slicePhys).
        iFrameF (nolater).
        iFrameF (absPhysHistDomEq).
        iFrameF "isAtLoc".
        iFrameNamedF.
        { iAssumption. }
        iEval (rewrite monPred_at_big_sepM).
        setoid_rewrite monPred_at_embed.
        iFrameF "absHist".
        iSplit.
        { iApply (monPred_mono _ (TV)).
          { etrans; first apply incl.
            etrans; first apply incl2.
            solve_view_le. }
          rewrite monPred_at_big_sepM.
          setoid_rewrite monPred_at_sep.
          simpl.
          setoid_rewrite monPred_at_embed.
          iApply "physHist". }
        iFrameF "offset".
        iPureIntro.
        etrans; first apply tSLe.
        f_equiv.
        solve_view_le. }
      iApply monPred_mono; last iFrame "Q".
      rewrite -pvEq.
      solve_view_le.
    - iDestruct "pToQ" as "[_ pToQ]".

      iMod (auth_map_map_lookup with "physHists") as "[physHists #physHistFrag]".
      { done. } { done. }

      eassert _ as temp. { eapply (read_atomic_location tS tL (OCV !!0 ℓ)); (done || lia). }
      destruct temp as (sL & encSL & ? & ? & ? & <- & orderRelated).

      iDestruct ("pToQ" $! (msg_val <$> ms) vL sL) as (P ? ?) "pToQ".
      iDestruct ("pToQ" with "[//]") as "[getP getQ]".
      iEval (monPred_simpl) in "getP".
      iDestruct ("getP" $! (TVfinal ⊔ _) with "[%] [-]") as "#P".
      { etrans; first done. apply thread_view_le_l. }
      { iDestruct (big_sepM2_delete with "predFullReadHolds") as "[phiI predHolds]".
        { apply look. } { done. }
        simpl.
        rewrite big_sepL2_snoc.
        iSplitR "phiI".
        - iDestruct (extract_list_of_preds
                       (delete tL abs_hist)
                       (delete tL phys_hist)
                       tLo tS
          with "predReadEquiv [predHolds]") as "L"; try done.
          (* iDestruct (extract_list_of_preds _ *)
          (*   (delete (tL + offset) abs_hist) *)
          (*   (delete (tL + offset) phys_hist) tLo tS _ _ _ _ _ _ *)
          (*   with "predEquiv [predHolds]") as "L". *)
          * rewrite -eqeq. rewrite -omap_delete. reflexivity.
          * rewrite -eqeq.
            apply map_sequence_delete_above; first lia.
            rewrite eqeq.
            done.
          * apply map_sequence_delete_above; [lia|done].
          * rewrite 2!dom_delete_L.
            rewrite absPhysHistDomEq.
            set_solver+.
          * iPoseProof (big_sepM2_impl_subseteq with "predHolds") as "predHolds".
            + apply delete_mono. done.
            + apply delete_mono. done.
            + rewrite 2!dom_delete_L.
              rewrite -absPhysHistDomEq.
              rewrite -domEq2.
              done.
            + iApply (big_sepM2_impl with "predHolds").
              iIntros (t msg encS physHistLook absHistLook) "!> predFR".
              destruct (decide _) as [ [] | no ].
              { assert (is_Some (@decode ST _ _ encS)) as [? ?]. {
                  replace (decode encS) with ((delete tL encAbsHist) !! t ≫= @decode ST _ _) by by rewrite absHistLook.
                  rewrite -lookup_omap.
                  rewrite -elem_of_dom.
                  rewrite omap_delete.
                  rewrite dom_delete.
                  rewrite eqeq.
                  rewrite elem_of_difference.
                  rewrite domEq2.
                  rewrite elem_of_dom.
                  apply lookup_delete_Some in absHistLook as [].
                  set_solver.
                }
                iPoseProof (predicate_holds_phi_decode_1 with "predFullEquiv predFR") as "H"; first done.
                iPoseProof (full_read_split with "H") as "[Hread _]".
                iApply (predicate_holds_phi_decode_2 with "predReadEquiv Hread"); first done.
              }
              { iApply "predFR". }
          * iApply monPred_mono; last done.
            apply thread_view_le_r.
        - destruct (decide _).
          * iDestruct (predicate_holds_phi_decode with "predFullEquiv phiI") as "phiI";
              first done.
            iPoseProof (full_read_split with "phiI") as "[phiI _]".
            iApply monPred_mono; last iApply "phiI".
            rewrite /TVfinal.
            etrans; last apply thread_view_le_l.
            solve_view_le.
          * iDestruct (predicate_holds_phi_decode with "predReadEquiv phiI") as "phiI";
              first done.
            iApply monPred_mono; last iApply "phiI".
            rewrite /TVfinal.
            etrans; last apply thread_view_le_l.
            solve_view_le. }
      iEval (monPred_simpl) in "getQ".
      iDestruct ("getQ" with "[%] [P]") as "bing".
      { done. }
      { iApply objective_at. iApply "P". }
      rewrite monPred_at_objectively.

      eassert _ as temp.
      { eapply map_Forall_lookup_1; first apply atInvs.
        replace tL with (tL - (OCV !!0 ℓ) + (OCV !!0 ℓ)) in look by lia.
        rewrite drop_prefix_lookup. done. }
      destruct temp as (? & pvEq).
      simpl in pvEq.

      iAssert (at_encoded_full_read_predicates_hold abs_hist' phys_hist' (OCV !!0 ℓ) encp_full encp_read ∗
               Q2 sL vL (SV', PV', ∅))%I with "[predFullReadHolds bing]"
        as "[predFullReadHolds Q]". {
        (* we now attempt to obtain [p_read] at [tL +  offset].
         * again, we need to case distinction over whether it's held at full or read. *)
        iDestruct (big_sepM2_lookup_acc with "predFullReadHolds") as "[predFR predMap]".
        { done. } { done. }
        simpl.
        destruct (decide _) as [[] | no ].
        - iDestruct (predicate_holds_phi_decode with "predFullEquiv predFR") as "PH";
            first done.

          iPoseProof (full_read_split with "PH") as "[PH Prestore]".

          iDestruct ("bing" $! _ with "PH") as "[Q predHolds]".

          iSpecialize ("Prestore" with "predHolds").

          iDestruct ("predMap" with "[Prestore]") as "predMap".
          { iIntros.
            iApply (predicate_holds_phi_decode with "predFullEquiv Prestore").
            assumption. }
          iFrame.
        - iDestruct (predicate_holds_phi_decode with "predReadEquiv predFR") as "PH";
            first done.

          iDestruct ("bing" $! _ with "PH") as "[Q predHolds]".

          iDestruct ("predMap" with "[predHolds]") as "predMap".
          { iIntros.
            iApply (predicate_holds_phi_decode with "predReadEquiv predHolds").
            assumption. }
          iFrame. }
      iModIntro.

      (* We re-establish [interp]. *)
      iDestruct ("reins" with "[$] [$] [$] [$] [$]") as "$".

      iSpecialize ("Φpost" $! vL).
      monPred_simpl.
      iApply "Φpost".
      { iPureIntro.
        etrans. eassumption.
        repeat split; try done; try apply view_le_l. }
      iLeft. iExists (sL).
      iSplitR "Q"; last first.
      { simpl. iApply monPred_mono; last iFrame "Q".
        solve_view_le. }
      iExists (<[ tL := sL ]>abs_hist). iExistsN.
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
      iFrameF "isAtLoc".
      rewrite big_sepM_insert. 2: { apply nolater. lia. }
      rewrite big_sepM_insert.
      2: {
        eapply map_dom_eq_lookup_None; first done.
        apply nolater. lia. }
      iFrameNamedF.
      { iAssumption. }
      iSplitPure.
      { apply: increasing_map_insert_last; try done. lia. }
      rewrite monPred_at_sep.
      rewrite monPred_at_big_sepM.
      setoid_rewrite monPred_at_embed.
      iFrame "absHist".
      iSplit.
      { iExists _.
        iSplitPure; first done.
        iApply (big_sepM_lookup with "frags"). done. }
      iFrame "offset".
      iSplit; last first.
      { simpl. iPureIntro.
        rewrite lookup_zero_lub.
        lia. }
      simpl.
      iSplit.
      { iFrame "physHistFrag".
        iPureIntro.
        simpl.
        solve_view_le. }
      iApply (monPred_mono _ TV).
      { etrans; first apply incl.
        etrans; first apply incl2.
        solve_view_le. }
      rewrite monPred_at_big_sepM.
      setoid_rewrite monPred_at_sep.
      setoid_rewrite monPred_at_embed.
      simpl.
      iFrame "physHist".
      Unshelve. done.
  Qed.

  Lemma wp_load_at_simple ℓ sI Q prot `{!ProtocolConditions prot} st E :
      {{{
        ℓ ↦_AT^{prot} [sI] ∗
        <obj> (∀ sL vL, ⌜ sI ⊑ sL ⌝ -∗ prot.(p_read) sL vL -∗ Q sL vL ∗ prot.(p_read) sL vL)
      }}}
        !_AT #ℓ @ st; E
      {{{ sL vL, RET vL;
        ℓ ↦_AT^{prot} [sL] ∗
        <fence> (Q sL vL) }}}.
    Proof.
      iIntros (Φ) "[pts impl] post".
      iApply (wp_load_at _ [] _ (λ v, Q sI v) Q with "[$pts impl]").
      { iSplit.
        * iIntros (??).
          iExists True%I, _, _.
          iIntros (?).
          iSplitL ""; first naive_solver.
          iIntros "_".
          iApply (monPred_objectively_mono with "impl").
          iIntros "impl P".
          iApply ("impl" with "[//] P").
        * iIntros (???).
          iExists True%I, _, _.
          iIntros (?).
          iSplitL ""; first naive_solver.
          iIntros "_".
          iApply (monPred_objectively_mono with "impl").
          iIntros "impl P".
          iApply ("impl" with "[//] P"). }
      iNext.
      iIntros (?).
      iIntros "[L|R]".
      - iDestruct "L" as (?) "[pts Q]".
        iApply "post".
        iFrame "Q".
        iApply mapsto_at_drop.
        done.
      - iApply "post".
        iApply "R".
    Qed.

  (* Load a location where the protocol invariant is persistent. *)
  Lemma wp_load_at_simple_pers ℓ (sI : ST) prot `{!ProtocolConditions prot} st E
    `{∀ s v, Persistent (prot.(p_read) s v)} :
      {{{ ℓ ↦_AT^{prot} [sI] }}}
        !_AT #ℓ @ st; E
      {{{ sL vL, RET vL;
        ⌜ sI ⊑ sL ⌝ ∗ ℓ ↦_AT^{prot} [sL] ∗ <fence> (prot.(p_read) sL vL) }}}.
  Proof.
    iIntros (Φ) "pts Φpost".
    iApply (wp_load_at_simple _ _
      (λ s v, ⌜ sI ⊑ s ⌝ ∗ prot.(p_read) s v)%I with "[$pts]").
    { iModIntro. iIntros (??) "$ #$". }
    iNext.
    iIntros (sL vL) "(pts & (>eq & hi))".
    iApply "Φpost".
    iFrame.
  Qed.

  (* Definition open_subjective (I P : dProp Σ) := <obj> I -∗ P ∗ I. *)

  (* This is a load lemma that allows for a sort of "threading" of resources
   * though all the invariants. The idea has some flaws (the order is arbitrary
   * for instance) but maybe it can be used to come up witha stronger load lemma. *)
  (* Lemma wp_load_at_strong ℓ ss s (QS : list (val → dProp Σ)) Q1 Q2 *)
  (*   prot `{!ProtocolConditions prot} st E : *)
  (*   length QS = length ss → *)
  (*   {{{ *)
  (*     ℓ ↦_AT^{prot} (ss ++ [s]) ∗ *)
  (*     (* Based on all the existing writes we can show [Q1]. *) *)
  (*     ((∀ vs, *)
  (*       ([∗ list] i ↦ s; v ∈ ss ++ [s];vs, ∃ Q Q', *)
  (*         ⌜ QS !! i = Some Q ⌝ -∗ *)
  (*         ⌜ (QS ++ [Q1]) !! (S i) = Some Q' ⌝ -∗ *)
  (*         <obj> prot.(p_inv) s v -∗ Q v -∗  prot.(p_inv) s v ∗ Q' v)) ∧ *)
  (*     (* In case of a new write we can show [Q2] *) *)
  (*     <obj> (∀ v v' s', *)
  (*       ⌜ s ⊑ s' ⌝ -∗ *)
  (*       prot.(p_inv) s' v -∗ *)
  (*       Q1 v -∗ *)
  (*       prot.(p_inv) s' v' ∗ Q2 s' v')) *)
  (*   }}} *)
  (*     !_AT #ℓ @ st; E *)
  (*   {{{ v, RET v; *)
  (*     (∃ s', ℓ ↦_AT^{prot} (ss ++ [s] ++ [s']) ∗ <fence> Q2 s' v) ∨ *)
  (*     <fence> Q1 v *)
  (*   }}}. *)
  (* Proof. Abort. *)
End wp_at.
