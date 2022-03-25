(* Assertions for locations.

  The assertions here are modeled usin the more resources defined in
  [self.high.resources], etc.
 *)

From iris.bi Require Import lib.fractional.
From iris.base_logic.lib Require Import own.
From iris.algebra Require Import gset gmap excl auth.
From iris.proofmode Require Import reduction monpred tactics.
From iris_named_props Require Import named_props.

From self Require Import extra ipm_tactics.
From self.algebra Require Import ghost_map ghost_map_map.
From self.base Require Import primitive_laws post_crash_modality.
From self.lang Require Import lang.
From self.high Require Import increasing_map monpred_simpl.
From self.high Require Import dprop abstract_state lifted_modalities if_rec or_lost.
From self.high Require Export abstract_state resources protocol modalities post_crash_modality.
From self.high.resources Require Export bumpers preorders auth_map_map abstract_history.
From self.high.modalities Require Export no_buffer no_flush.

Section points_to_at.
  Context `{nvmFixedG Σ, hGD : nvmDeltaG Σ, AbstractState ST}.

  Implicit Types (ℓ : loc) (s : ST) (ss : list ST) (prot : LocationProtocol ST).

  Lemma singleton_included_l' `{Countable K, CmraTotal A}
        (m : gmap K A) (i : K) x :
    {[i := x]} ≼ m ↔ (∃ y : A, m !! i ≡ Some y ∧ x ≼ y).
  Proof.
    setoid_rewrite <-(Some_included_total x).
    apply singleton_included_l.
  Qed.

  (* Points-to predicate for non-atomics. This predcate says that we know that
the last events at [ℓ] corresponds to the *)
  Program Definition mapsto_na (ℓ : loc) prot (q : frac) (ss : list ST) : dProp Σ :=
    (∃ (tP tStore : time) SV (abs_hist : gmap time ST) (msg : message) s,
      "%lastEq" ∷ ⌜ last ss = Some s ⌝ ∗
      "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
      "%incrMap" ∷ ⌜ increasing_map (⊑@{ST}) abs_hist ⌝ ∗
      "#isNaLoc" ∷ ⎡ is_na_loc ℓ ⎤ ∗

      (* [tStore] is the last message and it agrees with the last state in ss. *)
      "%lookupV" ∷ ⌜ abs_hist !! tStore = Some s ⌝ ∗
      "%nolater" ∷ ⌜ map_no_later abs_hist tStore ⌝ ∗

      (* Ownership over the full abstract history. *)
      "hist" ∷ ⎡ know_full_history_loc ℓ q abs_hist ⎤ ∗
      "#histFrag" ∷ ⎡ know_frag_history_loc ℓ tStore s ⎤ ∗

      "knowSV" ∷ ⎡ know_na_view ℓ q SV ⎤ ∗
      "%slice" ∷ ⌜ map_sequence abs_hist tP tStore ss ⌝ ∗
      "#physMsg" ∷ ⎡ auth_map_map_frag_singleton know_phys_history_name ℓ tStore msg ⎤ ∗
      "#inThreadView" ∷ monPred_in (SV, msg_persisted_after_view msg, ∅) ∗
      (* We have the [tStore] timestamp in our store view. *)
      "%haveTStore" ∷ ⌜ tStore ≤ SV !!0 ℓ ⌝ ∗
      "#pers" ∷ (⎡ persisted_loc ℓ tP ⎤ ∨ ⌜ tP = 0 ⌝)
    )%I.

  Global Instance mapsto_na_fractional ℓ prot ss :
    Fractional (λ q, mapsto_na ℓ prot q ss).
  Proof.
    intros p q.
    rewrite /mapsto_na.
    iSplit.
    - iNamed 1.
      iDestruct "hist" as "[histP histQ]".
      iDestruct "knowSV" as "[knowSVP knowSVQ]".
        iSplitL "histP knowSVP".
        + repeat iExists _. iFrame "#∗%".
        + repeat iExists _.
          iFrame "#∗%".
    - iDestruct 1 as "[L R]".
      iNamed "L".
      iDestruct "R" as (??????) "(_ & _ & ? & _ & _ & _ & histQ & _ & SV & HIP & ?)".
      iDestruct (full_entry_agree with "hist histQ") as %->%(inj (fmap _)).
      iDestruct (ghost_map_elem_agree with "knowSV SV") as %->.
      repeat iExists _. iFrame "#∗%".
  Qed.
  Global Instance mapsto_na_as_fractional ℓ prot q v :
    AsFractional (mapsto_na ℓ prot q v) (λ q, mapsto_na ℓ prot q v)%I q.
  Proof. split; [done | apply _]. Qed.

  Definition store_lb ℓ prot (s : ST) : dProp Σ :=
    ∃ (tS : nat),
      "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
      "#knowFragHist" ∷ ⎡ know_frag_history_loc ℓ tS s ⎤ ∗
      "#tSLe" ∷ have_SV ℓ tS.

  Definition flush_lb ℓ prot (s : ST) : dProp Σ :=
    ∃ (tF : nat),
      "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
      "knowFragHist" ∷ ⎡ know_frag_history_loc ℓ tF s ⎤ ∗
      "#tSLe" ∷ have_SV ℓ tF ∗
      (* Either we have something in the flush view or the location is
      persisted. The later case is for after a crash where we don't have
      anything in the flush view. *)
      "viewFact" ∷ (have_FV_strong ℓ tF ∨ ⎡ persisted_loc ℓ tF ⎤)%I.

  Program Definition persist_lb ℓ prot (sP : ST) : dProp Σ :=
    ∃ tP,
      "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
      "knowFragHist" ∷ ⎡ know_frag_history_loc ℓ tP sP ⎤ ∗
      (* We have the persisted state in our store view. *)
      "#tSLe" ∷ have_SV ℓ tP ∗
      "#tPLe" ∷ have_FV ℓ tP ∗
      "persisted" ∷ ⎡ persisted_loc ℓ tP ⎤.

  Definition crashed_in prot ℓ s : dProp Σ :=
    ∃ CV,
      "#crashed" ∷ ⎡ crashed_at CV ⎤ ∗
      "#crashedIn" ∷ ⎡ crashed_in_mapsto ℓ s ⎤ ∗
      "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
      "#pers" ∷ ⎡ persisted_loc ℓ 0 ⎤ ∗
      "#knowFragHist" ∷ ⎡ know_frag_history_loc ℓ 0 (bumper prot s) ⎤ ∗
      "%inCV" ∷ ⌜ℓ ∈ dom (gset _) CV⌝.

  (* [ℓ] was not recovered at the last crash. *)
  Definition lost ℓ : dProp Σ :=
    ∃ CV,
      "#crashed" ∷ ⎡crashed_at CV⎤ ∗
      "%notInCV" ∷ ⌜ℓ ∉ dom (gset _) CV⌝.

  (* Let's see if we want this.
  Definition mapsto_shared ℓ s1 s2 s3 ϕ : dProp Σ :=
    "knowPred" ∷ ⎡ know_pred ℓ ϕ ⎤ ∗
    "isSharedLoc" ∷ ⎡ own shared_locs_name (◯ {[ ℓ ]}) ⎤ ∗
    "globalPerLB" ∷ persist_lb ℓ s1 ∗
    "persistLB" ∷ flush_lb ℓ s2 ∗
    "storeLB" ∷ store_lb ℓ s3.
  *)

  Lemma store_lb_protocol ℓ prot s :
    store_lb ℓ prot s -∗ ⎡ know_protocol ℓ prot ⎤.
  Proof.
    iStartProof (iProp _). iIntros (TV). simpl. iNamed 1.
    iFrame "locationProtocol".
  Qed.

  Global Instance store_lb_persistent
         ℓ prot (s : ST) : Persistent (store_lb ℓ prot s).
  Proof. apply _. Qed.

  Global Instance flush_lb_persistent
         ℓ prot (s : ST) : Persistent (flush_lb ℓ prot s).
  Proof. apply _. Qed.

  Global Instance persist_lb_persistent
         ℓ prot (s : ST) : Persistent (persist_lb ℓ prot s).
  Proof. apply _. Qed.

  Lemma persist_lb_to_flush_lb ℓ prot s :
    persist_lb ℓ prot s -∗ flush_lb ℓ prot s.
  Proof. iNamed 1. iExists _. iFrame "∗#". Qed.

  Lemma flush_lb_to_store_lb ℓ prot s :
    flush_lb ℓ prot s -∗ store_lb ℓ prot s.
  Proof. iNamed 1. iExists _. iFrame "∗#". Qed.

  Lemma persist_lb_to_store_lb ℓ prot s :
    persist_lb ℓ prot s -∗ store_lb ℓ prot s.
  Proof. iNamed 1. iExists _. iFrame "∗#". Qed.
  
  (* Lemma flush_lb_at_zero ℓ (s s' : ST) : *)
  (*   s ⊑ s' → *)
  (*   ⎡ know_frag_history_loc ℓ {[0 := s']} ⎤ -∗ *)
  (*   ⎡ know_preorder_loc ℓ abs_state_relation ⎤ -∗ *)
  (*   flush_lb ℓ s. *)
  (* Proof. *)
  (*   iStartProof (iProp _). iIntros (incl ?) "?". *)
  (*   iIntros (? ?) "?". iExists 0, s'. iFrame "%∗". iPureIntro. lia. *)
  (* Qed. *)

  (*
  Lemma store_lb_at_zero ℓ (s s' : ST) :
    s ⊑ s' →
    ⎡ know_frag_history_loc ℓ {[0 := s']} ⎤ -∗
    ⎡ know_preorder_loc ℓ abs_state_relation ⎤ -∗
    store_lb ℓ s.
  Proof.
    iStartProof (iProp _). iIntros (incl ?) "?".
    iIntros (? ?) "?". iExists 0, s'. iFrame "%∗". iPureIntro. lia.
  Qed.
  *)

  (* Lemmas for [crashed_in]. *)
  Lemma crashed_in_agree prot ℓ s s' :
    crashed_in prot ℓ s -∗ crashed_in prot ℓ s' -∗ ⌜ s = s' ⌝.
  Proof.
    iNamed 1.
    iDestruct 1 as (?) "(? & ? & ? & ?)".
    iDestruct (crashed_in_mapsto_agree with "crashedIn [$]") as %->.
    done.
  Qed.

  Lemma crashed_in_or_lost `{AbstractState ST} prot ℓ P (s : ST) :
    crashed_in prot ℓ s -∗ or_lost ℓ P -∗ P.
  Proof.
    iNamed 1. iIntros "P".
    iApply (or_lost_get with "crashed P").
    apply elem_of_dom. done.
  Qed.

  Lemma crashed_in_if_rec `{AbstractState ST} prot ℓ P (s : ST) :
    crashed_in prot ℓ s -∗ if_rec ℓ P -∗ P.
  Proof.
    iNamed 1. iIntros "P".
    iApply "P"; iFrame "#%".
    iPureIntro. apply elem_of_dom. done.
  Qed.

  (* Lemmas for [mapsto_na] *)

  Lemma mapsto_na_store_lb ℓ prot q ss s :
    last ss = Some s →
    mapsto_na ℓ prot q ss -∗
    store_lb ℓ prot s.
  Proof.
    iIntros (last). iNamed 1.
    iExists (tStore).
    simplify_eq.
    iFrame "#".
    iApply monPred_in_have_SV; done.
  Qed.

  Lemma mapsto_na_last ℓ prot q ss : mapsto_na ℓ prot q ss -∗ ⌜∃ s, last ss = Some s⌝.
  Proof.
    rewrite /mapsto_na.
    iNamed 1.
    apply map_sequence_lookup_hi_alt in slice.
    naive_solver.
  Qed.

  Lemma mapsto_na_store_lb_incl ℓ prot q ss s1 s2 :
    last ss = Some s1 →
    store_lb ℓ prot s2 -∗
    mapsto_na ℓ prot q ss -∗
    ⌜s2 ⊑ s1⌝.
  Proof.
    iIntros (lastSome) "storeLb".
    iNamed 1.
    assert (s = s1) as -> by congruence.
    iDestruct "storeLb" as (t) "(_ & histFrag' & _)".
    iDestruct (full_entry_frag_entry_unenc with "hist histFrag'") as %look.
    eassert _ as le. { eapply map_no_later_Some; done. }
    eapply increasing_map_increasing in incrMap; done.
  Qed.

  Lemma mapsto_na_flush_lb_incl ℓ prot q ss s1 s2 :
    last ss = Some s1 →
    flush_lb ℓ prot s2 -∗
    mapsto_na ℓ prot q ss -∗
    ⌜s2 ⊑ s1⌝.
  Proof.
    iIntros (lastSome) "flushLb".
    iNamed 1.
    assert (s = s1) as -> by congruence.
    iDestruct "flushLb" as (t) "(_ & histFrag' & _)".
    iDestruct (full_entry_frag_entry_unenc with "hist histFrag'") as %look.
    eassert _ as le. { eapply map_no_later_Some; done. }
    eapply increasing_map_increasing in incrMap; done.
  Qed.

  Lemma mapsto_na_persist_lb ℓ prot q ss s1 s2 s3 :
    ¬(s2 ⊑ s1) →
    mapsto_na ℓ prot q (s1 :: s3 :: ss) -∗
    persist_lb ℓ prot s2 -∗
    mapsto_na ℓ prot q (s3 :: ss).
  Proof.
    iIntros (gt).
    iNamed 1.
    iDestruct 1 as (tP2) "(? & frag & ? & ? & ?)".
    assert (abs_hist !! tP = Some s1) as lookTP.
    { apply map_sequence_lookup_lo in slice. done. }
    apply map_sequence_cons_drop in slice as (tP3 & lt & noin & slice).
    iExists tP3, tStore, SV, abs_hist, msg, s.
    (* The non-trivial task now is to show that [tP2] is larger than [tP3]. *)
    iDestruct (full_entry_frag_entry_unenc with "hist frag") as %lookTP2.
    assert (tP < tP2). {
      apply (increasing_map_lookup_lt abs_hist _ _ s1 s2 incrMap); done. }
    destruct (decide (tP3 ≤ tP2)).
    2: { exfalso.
      assert (tP < tP2 < tP3) as order by lia.
      specialize (noin tP2 order).
      congruence. }
    iFrameF (lastEq). iFrameF "locationProtocol". iFrameF (incrMap).
    iFrameF "isNaLoc". iFrameF (lookupV). iFrameF (nolater).
    iFrameF "hist". iFrameF "histFrag". iFrameF "knowSV".
    iFrameF (slice). iFrame "physMsg". iFrame "inThreadView".
    iFrameF (haveTStore).
    iLeft. iApply persisted_loc_weak; done.
  Qed.

  (* Lemma mapsto_na_persist_lb ℓ prot q ss s1 s2 s3 : *)
  (*   ¬(s2 ⊑ s1) → *)
  (*   ss !! i = Some s1 → *)
  (*   length ss *)
  (*   mapsto_na ℓ prot q ss -∗ *)
  (*   persist_lb ℓ prot s2 -∗ *)
  (*   mapsto_na ℓ prot q (drop i ss). *)
  (* Proof. *)
  (* (* Instances. *) *)

  Lemma no_buffer_flush_lb ℓ prot (s : ST) :
    flush_lb ℓ prot s -∗ <nobuf> flush_lb ℓ prot s.
  Proof.
    rewrite /flush_lb.
    iModel. destruct TV as [[??]?].
    simpl.
    iNamed 1.
    iExists _. iFrame "#∗".
    iDestruct "viewFact" as "[%incl | $]".
    iLeft. iPureIntro. repeat split; try apply view_empty_least.
    apply incl.
  Qed.

  Global Instance buffer_free_flush_lb ℓ prot (s : ST) :
    BufferFree (flush_lb ℓ prot s).
  Proof. rewrite /IntoNoBuffer. eauto using no_buffer_flush_lb. Qed.

  Lemma no_flush_store_lb ℓ prot (s : ST) :
    store_lb ℓ prot s -∗ <noflush> store_lb ℓ prot s.
  Proof.
    rewrite /store_lb.
    iModel.
    simpl.
    iDestruct 1 as (?) "HI". iExists _. iFrame.
  Qed.

  Global Instance flush_free_flush_lb ℓ prot (s : ST) :
    FlushFree (store_lb ℓ prot s).
  Proof. rewrite /IntoNoFlush. eauto using no_flush_store_lb. Qed.

  Lemma no_buffer_store_lb ℓ prot (s : ST) :
    store_lb ℓ prot s -∗ <nobuf> store_lb ℓ prot s.
  Proof.
    rewrite /store_lb.
    iModel.
    simpl.
    iDestruct 1 as (?) "HI". iExists _. iFrame.
  Qed.

  Global Instance into_no_buffer_store_lb ℓ prot (s : ST) :
    BufferFree (store_lb ℓ prot s).
  Proof. rewrite /IntoNoBuffer. eauto using no_buffer_store_lb. Qed.

  Global Instance mapsto_na_buffer_free ℓ prot q (ss : list ST) :
    BufferFree (mapsto_na ℓ prot q ss).
  Proof. rewrite /mapsto_na. apply _. Qed.

End points_to_at.

(** Notation for the exclusive points-to predicate. *)
Notation "l ↦_{ prot } ss" := (mapsto_na l prot 1 ss) (at level 20).
Notation "l ↦_{ prot }^{ q } ss" := (mapsto_na l prot q ss) (at level 20).
(* Notation "l ↦^{ p } ss" := (mapsto_na p l 1 ss) (at level 20). *)
(* Notation "l ↦ ss" := (mapsto_na false l 1 ss) (at level 20). *)
(* Notation "l ↦{ q } ss" := (mapsto_na false l q ss) (at level 20). *)
(* Notation "l ↦ₚ ss" := (mapsto_na true l 1 ss) (at level 20). *)
(* Notation "l ↦ₚ{ q } ss" := (mapsto_na true l q ss) (at level 20). *)
(* Notation "l ↦ xs ; ys | P" := (mapsto_na l xs ys P) (at level 20). *)

(** Notation for the shared points-to predicate. *)
(* Notation "l ↦ ( s1 , s2 , s3 )  | P" := (mapsto_shared l s1 s2 s3 P) (at level 20). *)

Section points_to_at_more.
  Context `{nvmFixedG Σ, hGD : nvmDeltaG Σ, AbstractState ST}.

  Implicit Types (e : expr) (ℓ : loc) (s : ST)
           (ss : list ST) (prot : LocationProtocol ST).

  Lemma post_crash_persist_lb (ℓ : loc) prot (s1 : ST) :
    persist_lb ℓ prot s1 -∗
    post_crash (λ hG, ∃ s2, ⌜ s1 ⊑ s2 ⌝ ∗
      persist_lb ℓ prot (prot.(bumper) s2) ∗
      crashed_in prot ℓ s2).
  Proof.
    iNamed 1.
    rewrite /know_protocol. rewrite 2!embed_sep.
    iDestruct "locationProtocol" as "(-#pred & -#order & -#bumper)".
    iDestruct (post_crash_frag_history with "[$order $bumper $knowFragHist]") as "H".
    iCrash.
    iDestruct "persisted" as "(#persisted & (% & % & [% %] & #crashed))".
    iDestruct (or_lost_with_t_get with "[$] H")
      as "(% & % & #crashedIn & order & bumper & hist)";
      first done.
    iDestruct (if_rec_get with "[$] [$] pred") as "pred"; first done.
    iExists s2.
    iSplitPure; first intuition.
    iSplit.
    { iExists 0.
      iFrame "∗#".
      iDestruct (have_SV_0) as "$".
      iDestruct (have_FV_0) as "$". }
    rewrite /crashed_in.
    iExists _. iFrame "#∗". iPureIntro. apply elem_of_dom. done.
  Qed.

  Global Instance persist_lb_into_crash ℓ prot s : IntoCrash _ _ :=
    post_crash_persist_lb ℓ prot s.

  Lemma post_crash_flush_lb (ℓ : loc) prot (s : ST) :
    flush_lb ℓ prot s -∗
    post_crash (λ hG, if_rec ℓ (∃ (s' : ST), persist_lb ℓ prot s')).
  Proof.
    iNamed 1.
    iDestruct (know_protocol_extract with "locationProtocol")
      as "(-#pred & -#order & -#bumper)".
    iDestruct (post_crash_frag_history with "[$order $bumper $knowFragHist]") as "H".
    iCrash.
    iDestruct (if_rec_or_lost_with_t with "H") as "H".
    iDestruct (if_rec_is_persisted ℓ) as "pers".
    iModIntro.
    iDestruct "H" as (???) "(? & ? & ? & ?)".
    iExists _, 0. iFrame "#∗".
    iDestruct (have_SV_0) as "$".
    iDestruct (have_FV_0) as "$".
  Qed.

  Global Instance flush_lb_into_crash ℓ prot s : IntoCrash _ _ :=
    post_crash_flush_lb ℓ prot s.

  Lemma post_crash_store_lb (ℓ : loc) prot (s : ST) :
    store_lb ℓ prot s -∗
    post_crash (λ hG, if_rec ℓ (∃ (s' : ST),
      persist_lb ℓ prot s')).
  Proof.
    iNamed 1.
    iDestruct (know_protocol_extract with "locationProtocol")
      as "(-#pred & -#order & -#bumper)".
    iDestruct (post_crash_frag_history with "[$order $bumper $knowFragHist]") as "H".
    iCrash.
    iDestruct (if_rec_or_lost_with_t with "H") as "H".
    iDestruct (if_rec_is_persisted ℓ) as "pers".
    iModIntro.
    iDestruct "H" as (???) "(? & ? & ? & ?)".
    iExists _, 0. iFrame "#∗".
    iDestruct (have_SV_0) as "$".
    iDestruct (have_FV_0) as "$".
  Qed.

  Global Instance store_lb_into_crash ℓ prot s : IntoCrash _ _ :=
    post_crash_store_lb ℓ prot s.

  Lemma post_crash_mapsto_na ℓ prot q (ss : list ST) :
    ℓ ↦_{prot}^{q} ss -∗
    post_crash (λ hG',
      if_rec ℓ (∃ s, ⌜s ∈ ss⌝ ∗
                      ℓ ↦_{prot}^{q} [bumper prot s] ∗
                      crashed_in prot ℓ s)).
  Proof.
    rewrite /mapsto_na.
    iNamed 1.
    iDestruct "locationProtocol" as "(-#pred & -#order & -#bumper)".
    iDestruct "isNaLoc" as "-#isNaLoc".
    iDestruct (post_crash_know_full_history_loc with "[$bumper $hist]") as "H".
    iDestruct "physMsg" as "-#physMsg".
    iDestruct "pers" as "-#pers".
    iCrash.
    iDestruct "pers" as "#pers".
    iDestruct (if_rec_is_rec ℓ) as "rec".
    iModIntro.
    iDestruct "rec" as (CV [[t]?]) "[crashed pers']".
    iDestruct (or_lost_with_t_get with "[$] H")
      as (sNew ?) "(bump & fullHist & fragHist & crashedIn)"; first done.
    iExists (sNew).

    iAssert (⌜ tP ≤ t ⌝)%I as %?.
    { iDestruct "pers" as "[(_ & (%CV' & % & [% %] & crashed'))|->]";
        last (iPureIntro; lia).
      iDestruct (crashed_at_agree with "crashed crashed'") as %<-.
      iPureIntro.
      assert (t = t'); last lia.
      congruence. }
    iSplit.
    { iPureIntro. apply: map_sequence_lookup_between; try done.
      split; first done.
      eapply map_no_later_Some; try naive_solver. }

    iDestruct "physMsg" as (v) "hist".

    rewrite /crashed_in.
    iSplit.
    + iExists 0, 0, ∅, _, (Msg _ ∅ ∅ ∅), _. iFrame. iFrame "#".
      iPureGoal. { done. }
      iPureGoal. { apply increasing_map_singleton. }
      iPureGoal. { by rewrite lookup_singleton. }
      iPureGoal. { apply map_no_later_singleton. }
      iPureGoal. { by rewrite lookup_singleton. }
      iSplit. { simpl. iApply monPred_in_bottom. }
      done.
    + iExists _. iFrame "∗#".
      iPureIntro. rewrite elem_of_dom. naive_solver.
  Qed.

  Global Instance mapsto_na_into_crash ℓ prot q (ss : list ST) :
    IntoCrash (ℓ ↦_{prot}^{q} ss)%I _ := post_crash_mapsto_na ℓ prot q ss.

  Global Instance mapsto_na_into_crash_flush ℓ prot q (ss : list ST) :
    IntoCrashFlush _ _ :=
    (into_crash_into_crash_flushed _ _ (post_crash_mapsto_na ℓ prot q ss)).

  Lemma post_crash_flush_flush_lb (ℓ : loc) prot (s : ST) :
    flush_lb ℓ prot s -∗
    <PCF> hG, ∃ s__pc,
      ⌜ s ⊑ s__pc ⌝ ∗ crashed_in prot ℓ s__pc ∗ persist_lb ℓ prot (bumper prot s__pc).
  Proof.
    iNamed 1.
    iDestruct "locationProtocol" as "(-#pred & -#order & -#bumper)".
    iDestruct (post_crash_frag_history with "[$]") as "HI".
    iDestruct (post_crash_flush_post_crash with "HI") as "HI".
    iCrashFlush.
    iAssert (_)%I with "[viewFact]" as "pers".
    { iDestruct "viewFact" as "[pers | pers]".
      - iAccu.
      - iDestruct "pers" as "($ & (%CV & % & [% %] & ?))".
        iExists _, _. iFrame. done. }
    iDestruct "pers" as "(#pers & (%CV & %t & (%cvLook & %le) & #crashed))".
    iDestruct (or_lost_with_t_get with "crashed HI") as "HI"; first done.
    iDestruct (if_rec_get with "crashed pers pred") as "pred"; first done.
    iDestruct "HI" as (s2 impl) "(#crashedIn & #? & #? & #?)".
    iExists s2.
    iSplitPure; first by apply impl.
    rewrite /crashed_in /persist_lb.
    iSplit.
    - iExists _.
      iFrame "crashed crashedIn pred".
      iFrame "#". iPureIntro. apply elem_of_dom. done.
    - iExists _. iFrame "#∗".
      iDestruct (have_SV_0) as "$".
      iDestruct (have_FV_0) as "$".
  Qed.

  Global Instance know_flush_into_crash ℓ prot (s : ST) :
    IntoCrashFlush (flush_lb ℓ prot s) _ := post_crash_flush_flush_lb ℓ prot s.

End points_to_at_more.

Typeclasses Opaque mapsto_na.
Typeclasses Opaque store_lb.
Typeclasses Opaque flush_lb.
Typeclasses Opaque persist_lb.
