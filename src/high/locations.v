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
  Context `{nvmG Σ, hGD : nvmDeltaG, AbstractState ST}.

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
  (* FIXME: Can [mapsto_na] use [lb_base]? *)
  Program Definition mapsto_na (ℓ : loc) prot (q : frac) (ss : list ST) : dProp Σ :=
    (∃ (tLo tHi offset : time) SV (abs_hist : gmap time ST) (msg : message) s,
      "%lastEq" ∷ ⌜ last ss = Some s ⌝ ∗
      "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
      "%incrMap" ∷ ⌜ increasing_map (⊑@{ST}) abs_hist ⌝ ∗
      "#isNaLoc" ∷ ⎡ is_na_loc ℓ ⎤ ∗

      (* [tHi] is the last message and it agrees with the last state in ss. *)
      "%lookupV" ∷ ⌜ abs_hist !! tHi = Some s ⌝ ∗
      "%nolater" ∷ ⌜ map_no_later abs_hist tHi ⌝ ∗

      (* Ownership over the full abstract history. *)
      "hist" ∷ ⎡ know_full_history_loc ℓ q abs_hist ⎤ ∗
      "#histFrag" ∷ ⎡ know_frag_history_loc ℓ tHi s ⎤ ∗
      "#offset" ∷ ⎡ ℓ ↪[offset_name]□ offset ⎤ ∗

      "knowSV" ∷ ⎡ know_na_view ℓ q SV ⎤ ∗
      "%slice" ∷ ⌜ map_sequence abs_hist tLo tHi ss ⌝ ∗
      "#physMsg" ∷ ⎡ auth_map_map_frag_singleton phys_history_name ℓ tHi msg ⎤ ∗
      "#inThreadView" ∷ monPred_in (SV, msg_persisted_after_view msg, ∅) ∗
      (* We have the [tHi] timestamp in our store view. *)
      "%offsetLe" ∷ ⌜ offset ≤ tHi ⌝ ∗
      "%haveTStore" ∷ ⌜ tHi - offset ≤ SV !!0 ℓ ⌝ ∗
      "#pers" ∷ (⎡ persisted_loc ℓ (tLo - offset) ⎤ ∨ ⌜ tLo - offset = 0 ⌝)
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
      iDestruct "R" as (???????) "(_ & _ & ? & _ & _ & _ & histQ & _ & _ & SV & HIP & ?)".
      iDestruct (full_entry_agree with "hist histQ") as %->%(inj (fmap _)).
      iDestruct (ghost_map_elem_agree with "knowSV SV") as %->.
      repeat iExists _. iFrame "#∗%".
  Qed.
  Global Instance mapsto_na_as_fractional ℓ prot q v :
    AsFractional (mapsto_na ℓ prot q v) (λ q, mapsto_na ℓ prot q v)%I q.
  Proof. split; [done | apply _]. Qed.

  Program Definition have_msg_after_fence msg : dProp Σ :=
    MonPred (λ TV,
      ⌜ msg.(msg_store_view) ⊑ (store_view TV) ⌝ ∗
      ⌜ msg.(msg_persisted_after_view) ⊑ (flush_view TV ⊔ buffer_view TV) ⌝
    )%I _.
  Next Obligation. solve_proper. Qed.

  Global Instance have_msg_after_fence_persistent msg :
    Persistent (have_msg_after_fence msg).
  Proof. apply monPred_persistent=> j. apply _. Qed.

  Definition mapsto_at ℓ prot ss : dProp Σ :=
    (∃ (abs_hist : gmap time ST) (phys_hist : gmap time message) tLo tS offset s ms,
      "%lastEq" ∷ ⌜ last ss = Some s ⌝ ∗ (* NOTE: Could we change this to non-empty? *)
      "%slice" ∷ ⌜ map_sequence abs_hist tLo tS ss ⌝ ∗
      "%slicePhys" ∷ ⌜ map_sequence phys_hist tLo tS ms ⌝ ∗
      "%nolater" ∷ ⌜ map_no_later abs_hist tS ⌝ ∗
      "%absPhysHistDomEq" ∷ ⌜ dom (gset _) abs_hist = dom _ phys_hist ⌝ ∗
      "#isAtLoc" ∷ ⎡ is_at_loc ℓ ⎤ ∗
      "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
      "%incrMap" ∷ ⌜ increasing_map (⊑@{ST}) abs_hist ⌝ ∗
      "#absHist" ∷
        ⎡ ([∗ map] t ↦ s ∈ abs_hist, know_frag_history_loc ℓ t s) ⎤ ∗
      "#physHist" ∷
        ([∗ map] t ↦ msg ∈ phys_hist,
          have_msg_after_fence msg ∗
          ⎡ auth_map_map_frag_singleton phys_history_name ℓ t msg ⎤) ∗
      "#offset" ∷ ⎡ ℓ ↪[offset_name]□ offset ⎤ ∗
      "#tSLe" ∷ have_SV ℓ (tS - offset)).

  Global Instance mapsto_na_persistent ℓ prot ss :
    Persistent (mapsto_at ℓ prot ss).
  Proof. apply _. Qed.

  Definition lb_base ℓ prot offset tS (s : ST) : dProp Σ :=
    "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
    "#knowFragHist" ∷ ⎡ know_frag_history_loc ℓ tS s ⎤ ∗
    "#offset" ∷ ⎡ ℓ ↪[offset_name]□ offset ⎤ ∗
    "#tSLe" ∷ have_SV ℓ (tS - offset).

  Definition store_lb ℓ prot (s : ST) : dProp Σ :=
    ∃ (tS : nat) (offset : nat),
      "#lbBase" ∷ lb_base ℓ prot offset tS s.

  Definition flush_lb ℓ prot (s : ST) : dProp Σ :=
    ∃ (tF : nat) offset,
      "#lbBase" ∷ lb_base ℓ prot offset tF s ∗
      (* Either we have something in the flush view or the location is
      persisted. The later case is for after a crash where we don't have
      anything in the flush view. *)
      "viewFact" ∷ (have_FV_strong ℓ (tF - offset) ∨
                    ⎡ persisted_loc ℓ (tF - offset) ⎤)%I.

  Program Definition persist_lb ℓ prot (sP : ST) : dProp Σ :=
    ∃ tP offset,
      "#lbBase" ∷ lb_base ℓ prot offset tP sP ∗
      (* We have the persisted state in our store view. *)
      "#tPLe" ∷ have_FV ℓ (tP - offset) ∗
      "persisted" ∷ ⎡ persisted_loc ℓ (tP - offset) ⎤.

  Definition crashed_in prot ℓ s : dProp Σ :=
    ∃ CV,
      "#persistLb" ∷ persist_lb ℓ prot (prot.(bumper) s) ∗
      "#crashed" ∷ ⎡ crashed_at CV ⎤ ∗
      "#crashedIn" ∷ ⎡ crashed_in_mapsto ℓ s ⎤ ∗
      "%inCV" ∷ ⌜ℓ ∈ dom (gset _) CV⌝.

  Global Instance crashed_in_persistent prot ℓ s :
    Persistent (crashed_in prot ℓ s).
  Proof. apply _. Qed.

  (* [ℓ] was not recovered at the last crash. *)
  Definition lost ℓ : dProp Σ :=
    ∃ CV,
      "#crashed" ∷ ⎡ crashed_at CV ⎤ ∗
      "%notInCV" ∷ ⌜ℓ ∉ dom (gset _) CV⌝.

  Lemma store_lb_protocol ℓ prot s :
    store_lb ℓ prot s -∗ ⎡ know_protocol ℓ prot ⎤.
  Proof. iNamed 1. iNamed "lbBase". iFrame "locationProtocol". Qed.

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
  Proof. iNamed 1. iExistsN. iFrame "∗#". Qed.

  Lemma flush_lb_to_store_lb ℓ prot s :
    flush_lb ℓ prot s -∗ store_lb ℓ prot s.
  Proof. iNamed 1. iExistsN. iFrame "∗#". Qed.

  Lemma persist_lb_to_store_lb ℓ prot s :
    persist_lb ℓ prot s -∗ store_lb ℓ prot s.
  Proof. iNamed 1. iExistsN. iFrame "∗#". Qed.

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
    crashed_in prot ℓ s -∗ crashed_in prot ℓ s' -∗ ⌜ s = s' ⌝. Proof.
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
    iNamed 1. iNamed "persistLb". iIntros "P".
    iDestruct (persisted_loc_weak with "persisted") as "persisted2".
    { apply le_0_n. }
    iApply "P"; iFrame "#%".
    iPureIntro. apply elem_of_dom. done.
  Qed.

  Lemma crashed_in_persist_lb `{AbstractState ST} prot ℓ (s : ST) :
    crashed_in prot ℓ s -∗ persist_lb ℓ prot (prot.(bumper) s).
  Proof. iNamed 1. iFrame "persistLb". Qed.

  (* Lemmas for [mapsto_na] *)

  Lemma mapsto_na_store_lb ℓ prot q ss s :
    last ss = Some s →
    mapsto_na ℓ prot q ss -∗
    store_lb ℓ prot s.
  Proof.
    iIntros (last). iNamed 1.
    iExists tHi, offset.
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
    iDestruct "storeLb" as (t ?) "(_ & histFrag' & _)".
    iDestruct (full_entry_frag_entry_unenc with "hist histFrag'") as %look.
    eassert _ as le. { eapply map_no_later_Some; done. }
    eapply increasing_map_increasing in incrMap; done.
  Qed.

  Lemma mapsto_na_flush_lb_incl ℓ prot q ss s1 s2 :
    last ss = Some s1 →
    flush_lb ℓ prot s2 -∗
    mapsto_na ℓ prot q ss -∗
    ⌜s2 ⊑ s1⌝.
  Proof. rewrite flush_lb_to_store_lb. apply mapsto_na_store_lb_incl. Qed.

  Lemma mapsto_na_increasing ℓ prot q ss :
    mapsto_na ℓ prot q ss -∗ ⌜ increasing_list (⊑) ss ⌝.
  Proof.
    iNamed 1. iPureIntro. eapply increasing_map_to_increasing_list; done.
  Qed.

  Lemma mapsto_na_persist_lb ℓ prot q ss s1 s2 s3 :
    ¬(s2 ⊑ s1) →
    mapsto_na ℓ prot q (s1 :: s3 :: ss) -∗
    persist_lb ℓ prot s2 -∗
    mapsto_na ℓ prot q (s3 :: ss).
  Proof.
    iIntros (gt).
    iNamed 1.
    iDestruct 1 as (tP2 ?) "((? & frag & ? & ?) & ? & ?)".
    assert (abs_hist !! tLo = Some s1) as lookTP.
    { apply map_sequence_lookup_lo in slice. done. }
    apply map_sequence_cons_drop in slice as (tP3 & lt & noin & slice).
    iExists tP3, tHi, offset, SV, abs_hist, msg, s.
    (* The non-trivial task now is to show that [tP2] is larger than [tP3]. *)
    iDestruct (full_entry_frag_entry_unenc with "hist frag") as %lookTP2.
    assert (tLo < tP2). {
      apply (increasing_map_lookup_lt abs_hist _ _ s1 s2 incrMap); done. }
    destruct (decide (tP3 ≤ tP2)).
    2: { exfalso.
      assert (tLo < tP2 < tP3) as order by lia.
      specialize (noin tP2 order).
      congruence. }
    iDestruct (ghost_map_elem_agree with "offset [$]") as %<-.
    iFrameF (lastEq). iFrameF "locationProtocol". iFrameF (incrMap).
    iFrameF "isNaLoc". iFrameF (lookupV). iFrameF (nolater).
    iFrameF "hist". iFrameF "histFrag". iFrameF "offset". iFrameF "knowSV".
    iFrameF (slice). iFrame "physMsg". iFrame "inThreadView".
    iSplitPure; first done.
    iFrameF (haveTStore).
    iLeft. iApply persisted_loc_weak; last done. lia.
  Qed.

  Lemma mapsto_na_persist_lb_last ℓ prot q ss s :
    last ss = Some s →
    persist_lb ℓ prot s -∗
    mapsto_na ℓ prot q ss -∗
    mapsto_na ℓ prot q [s].
  Proof.
    induction ss as [|s1 ss IH]; first done.
    iIntros (lastLook) "#per pts".
    destruct ss as [|s2 ss].
    { inversion lastLook. done. }
    iApply IH.
    - done.
    - done.
    - iDestruct (mapsto_na_increasing with "[$]") as %incr.
      iApply (mapsto_na_persist_lb with "pts per").
  Abort. (* This lemma only holds if [s] is strictly greater than all other
  elements of [ss]. *)

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
    iExists _, _. iFrame "#∗".
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

Notation "l ↦_AT^{ prot } ss" := (mapsto_at l prot ss) (at level 20).

Section points_to_at_more.
  Context `{nvmG Σ, hGD : nvmDeltaG, AbstractState ST}.

  Implicit Types (e : expr) (ℓ : loc) (s : ST)
           (ss : list ST) (prot : LocationProtocol ST).

  Lemma post_crash_persist_lb (ℓ : loc) prot (s : ST) :
    persist_lb ℓ prot s -∗
    <PC> _,
      persist_lb ℓ prot (prot.(bumper) s) ∗
      ∃ s', ⌜ s ⊑ s' ⌝ ∗ crashed_in prot ℓ s'.
  Proof.
    iNamed 1. iNamed "lbBase".
    rewrite /know_protocol.
    iDestruct "locationProtocol" as "(-#pred & #order & #bumper)".
    iDestruct (post_crash_frag_history with "order offset bumper knowFragHist") as "-#H".
    iDestruct "offset" as "-#offset".
    iDestruct "bumper" as "-#bumper".
    iDestruct "order" as "-#order".
    iCrash.
    iDestruct "persisted" as "(#persisted & (% & %tC & [% %] & #crashed))".
    iApply (if_rec_get with "crashed persisted"); first done.
    iModIntro.
    iDestruct "offset" as (???) "[crashed' offset]".
    iDestruct (crashed_at_agree with "crashed crashed'") as %<-.
    iClear "crashed'".
    simplify_eq.
    iDestruct "H" as (????) "(#crashed' & ? & #hist & impl)".
    iDestruct (crashed_at_agree with "crashed crashed'") as %<-.
    iClear "crashed'".
    assert (tC = tC0) as <- by congruence.
    iDestruct ("impl" with "[%]") as "[% ?]"; first lia.
    iSplit.
    * iExists _, _.
      iFrame "∗#".
      assert (tP - (offset + tC) = 0) as -> by lia.
      iFrame "persisted".
      iDestruct (have_SV_0) as "$".
      iDestruct (have_FV_0) as "$".
    * iExists s2. iSplitPure; first done.
      iExists _. iFrame "crashed". iFrame.
      iSplit; last (iPureIntro; apply elem_of_dom; done).
      iExists (offset + tC), (offset + tC).
      assert ((offset + tC - (offset + tC)) = 0) as -> by lia.
      iFrame "#∗".
      iDestruct (have_SV_0) as "$".
      iDestruct (have_FV_0) as "$".
  Qed.

  Global Instance persist_lb_into_crash ℓ prot s : IntoCrash _ _ :=
    post_crash_persist_lb ℓ prot s.

  (* This lemma is commented out as it doesn't seem useful. *)
  (* Lemma post_crash_flush_lb (ℓ : loc) prot (s : ST) : *)
  (*   flush_lb ℓ prot s -∗ *)
  (*   post_crash (λ hG, if_rec ℓ (∃ (s' : ST), persist_lb ℓ prot s')). *)
  (* Proof. *)
  (*   iNamed 1. *)
  (*   iDestruct (know_protocol_extract with "locationProtocol") *)
  (*     as "(-#pred & -#order & -#bumper)". *)
  (*   iDestruct (post_crash_frag_history with "[$order $bumper $knowFragHist]") as "H". *)
  (*   iCrash. *)
  (*   iDestruct (if_rec_or_lost_with_t with "H") as "H". *)
  (*   iDestruct (if_rec_is_persisted ℓ) as "pers". *)
  (*   iModIntro. *)
  (*   iDestruct "H" as (???) "(? & ? & ? & ?)". *)
  (*   iExists _, 0. iFrame "#∗". *)
  (*   iDestruct (have_SV_0) as "$". *)
  (*   iDestruct (have_FV_0) as "$". *)
  (* Qed. *)

  (* Global Instance flush_lb_into_crash ℓ prot s : IntoCrash _ _ := *)
  (*   post_crash_flush_lb ℓ prot s. *)

  Lemma post_crash_store_lb (ℓ : loc) prot (s : ST) :
    store_lb ℓ prot s -∗
    <PC> hG, if_rec ℓ (∃ (s' : ST), persist_lb ℓ prot s').
  Proof.
    iNamed 1. iNamed "lbBase".
    iDestruct (know_protocol_extract with "locationProtocol")
      as "(#pred & #order & #bumper)".
    iDestruct (post_crash_frag_history
      with "order offset bumper knowFragHist") as "-#H".
    iDestruct "pred" as "-#pred".
    iDestruct "offset" as "-#offset".
    iDestruct "bumper" as "-#bumper".
    iDestruct "order" as "-#order".
    iCrash.
    iDestruct (if_rec_is_persisted ℓ) as "pers".
    iModIntro.
    iDestruct "H" as (????) "(crashed & ? & ? & ?)".
    iDestruct "offset" as (???) "(crashed' & ?)".
    iDestruct (crashed_at_agree with "crashed crashed'") as %->.
    simplify_eq.
    iExistsN.
    iFrame.
    replace (offset + tC - (offset + tC)) with 0 by lia.
    iDestruct (have_SV_0) as "$".
    iDestruct (have_FV_0) as "$".
    iFrame "pers".
  Qed.

  (* Global Instance store_lb_into_crash ℓ prot s : IntoCrash _ _ := *)
  (*   post_crash_store_lb ℓ prot s. *)

  (* Lemma map_sequence_prefix tLo tHi t ss abs_hist : *)
  (*   map_sequence abs_hist tLo tHi ss → *)
  (*   tLo ≤ t ≤ tHi → *)
  (*   ∃ ss', ss' `prefix_of` ss ∧ *)
  (*   map_sequence abs_hist tLo t ss. *)
  (* Proof. *)

  Lemma post_crash_mapsto_na ℓ prot q (ss : list ST) :
    ℓ ↦_{prot}^{q} ss -∗
    post_crash (λ hG',
      if_rec ℓ (∃ ss' s,
        ⌜ ss' `prefix_of` ss ⌝ ∗
        ⌜ last ss' = Some s ⌝ ∗
        crashed_in prot ℓ s ∗
        ℓ ↦_{prot}^{q} (bumper prot <$> ss'))).
  Proof.
    rewrite /mapsto_na.
    iNamed 1.
    iDestruct "locationProtocol" as "(-#pred & -#order & -#bumper)".
    iDestruct "isNaLoc" as "-#isNaLoc".
    iDestruct (post_crash_know_full_history_loc with "[$bumper $hist]") as "H".
    iDestruct "physMsg" as "-#physMsg".
    iDestruct "pers" as "-#pers".
    iDestruct "offset" as "-#offset".
    iCrash.
    iDestruct (if_rec_is_persisted ℓ) as "persisted".
    iModIntro.
    iDestruct "offset" as (tC CV cvLook) "(crashed & offset)".
    iDestruct "H" as (? s2 v absHistLook)
      "(bumper & #crashedIn & offset' & fullHist & fragHist & #phys)".
    iDestruct (ghost_map_elem_agree with "offset offset'") as %<-.
    iClear "offset'".
    assert (offset + tC ≤ tHi). { eapply map_no_later_Some; done. }

    iAssert (⌜ tLo ≤ offset + tC ⌝)%I as %?.
    { iDestruct "pers" as "[(_ & (%CV' & % & [% %] & crashed'))|%eq]".
      - iDestruct (crashed_at_agree with "crashed crashed'") as %<-.
        simplify_eq. iPureIntro. lia.
      - iPureIntro. lia. }
    eassert _ as HT. { eapply map_sequence_prefix; done. }
    destruct HT as (ss' & prefix & slice' & lastEq').
    iExists ss', s2.
    iSplitPure; first done.
    iSplitPure; first done.
    iSplit.
    { rewrite /crashed_in.
      iExists CV.
      iFrame "crashed crashedIn".
      iSplit; last (iPureIntro; apply elem_of_dom; done).
      iFrame.
      iExists (offset + tC), (offset + tC).
      assert ((offset + tC - (offset + tC)) = 0) as -> by lia.
      iFrame "persisted".
      iFrame "#∗".
      iDestruct (have_SV_0) as "$".
      iDestruct (have_FV_0) as "$". }
    iExists tLo, (offset + tC), (offset + tC), ∅, _, (Msg _ ∅ ∅ ∅), _.
    iFrame. iFrame "#".
    iPureGoal. { rewrite fmap_last. rewrite lastEq'. done. }
    iPureGoal.
    { apply: increasing_map_fmap.
      apply increasing_map_filter.
      done. }
    iPureGoal.
    { rewrite lookup_fmap.
      rewrite drop_above_lookup_t.
      rewrite absHistLook.
      done. }
    iPureGoal. {
      apply map_no_later_fmap.
      apply map_no_later_drop_above. }
    iPureGoal.
    { apply map_sequence_fmap.
      apply map_sequence_drop_above.
      done. }
    iPureGoal; first lia.
    iSplit. { simpl. iApply monPred_in_bottom. }
    iSplitPure; first lia.
    iRight. iPureIntro. lia.
  Qed.

  Global Instance mapsto_na_into_crash ℓ prot q (ss : list ST) :
    IntoCrash (ℓ ↦_{prot}^{q} ss)%I _ := post_crash_mapsto_na ℓ prot q ss.

  (* This lemma is strictly weaker than the above but could be useful if we do
  not want to preserve the prefix after a crash. *)
  Lemma post_crash_mapsto_na_singleton ℓ prot q (ss : list ST) :
    ℓ ↦_{prot}^{q} ss -∗
    post_crash (λ hG',
      if_rec ℓ (∃ s,
        ⌜ s ∈ ss ⌝ ∗
        crashed_in prot ℓ s ∗
        ℓ ↦_{prot}^{q} [prot.(bumper) s])).
  Proof.
    iIntros "pts".
    iCrash. iModIntro.
    iDestruct "pts" as (????) "(crashed & pts)".
    iExists s.
    iSplitPure.
    { eapply elem_of_list_lookup_2.
      eapply prefix_lookup; last done.
      erewrite <- last_lookup.
      done. }
    iDestruct (crashed_in_persist_lb with "[$]") as "#per".
  Abort. (* This should be true but is a bit annoying to show. *)

  Global Instance mapsto_na_into_crash_flush ℓ prot q (ss : list ST) :
    IntoCrashFlush _ _ :=
    (into_crash_into_crash_flushed _ _ (post_crash_mapsto_na ℓ prot q ss)).

  Lemma post_crash_flush_flush_lb (ℓ : loc) prot (s : ST) :
    flush_lb ℓ prot s -∗
    <PCF> hG, persist_lb ℓ prot (bumper prot s) ∗
              ∃ s__pc, ⌜ s ⊑ s__pc ⌝ ∗ crashed_in prot ℓ s__pc.
  Proof.
    iNamed 1. iNamed "lbBase".
    iDestruct "locationProtocol" as "(-#pred & #order & #bumper)".
    iDestruct (post_crash_frag_history
      with "order offset bumper knowFragHist") as "-#HI".
    iDestruct (post_crash_flush_post_crash with "HI") as "-#HI".
    iDestruct "offset" as "-#offset".
    iDestruct "bumper" as "-#bumper".
    iDestruct "order" as "-#order".
    iDestruct (post_crash_know_bumper with "bumper") as "bumper".
    iDestruct (post_crash_flush_post_crash with "bumper") as "bumper".
    iDestruct (post_crash_preorder with "order") as "order".
    iDestruct (post_crash_flush_post_crash with "order") as "order".
    iCrashFlush.
    iAssert (_)%I with "[viewFact]" as "pers".
    { iDestruct "viewFact" as "[pers | pers]".
      - iApply "pers".
      - iDestruct "pers" as "($ & (%CV & % & % & ?))".
        iExists _, _. iFrame. done. }
    iDestruct "pers" as "(#persisted & (%CV & %t & (%cvLook & %le) & #crashed))".
    iApply (if_rec_get with "crashed persisted"); first done.
    iModIntro.

    iDestruct "offset" as (???) "[crashed' offset]".
    iDestruct (crashed_at_agree with "crashed crashed'") as %<-.
    iClear "crashed'".
    simplify_eq.
    iDestruct "HI" as (????) "(#crashed' & ? & #hist & impl)".
    iDestruct (crashed_at_agree with "crashed crashed'") as %<-.
    iClear "crashed'".
    simplify_eq.
    iDestruct ("impl" with "[%]") as "[%incl ?]"; first lia.
    iSplit.
    - iExists _, _.
      iFrame "∗#".
      assert (tF - (offset + t) = 0) as -> by lia.
      iDestruct (have_SV_0) as "$".
      iDestruct (have_FV_0) as "$".
      iFrame "persisted".
    - iExists s2.
      iFrame (incl).
      iExists _. iFrame "∗#".
      iSplit; last (iPureIntro; apply elem_of_dom; try naive_solver).
      iExists _, _. iFrame "∗#".
      replace (offset + t - (offset + t)) with 0 by lia.
      iFrame "persisted".
      iDestruct (have_SV_0) as "$".
      iDestruct (have_FV_0) as "$".
  Qed.

  Global Instance know_flush_into_crash ℓ prot (s : ST) :
    IntoCrashFlush (flush_lb ℓ prot s) _ := post_crash_flush_flush_lb ℓ prot s.

  Global Instance post_crash_into_crash P :
    IntoCrash (post_crash P) P.
  Proof. done. Qed.

  Lemma mapsto_at_store_lb ℓ prot ss s :
    ℓ ↦_AT^{prot} (ss ++ [s]) -∗ store_lb ℓ prot s.
  Proof.
    iNamed 1.
    iExists tS, offset.
    simplify_eq.
    iFrame "#".
    rewrite embed_big_sepM.
    iDestruct (big_sepM_lookup with "absHist") as "frag".
    { apply map_sequence_lookup_hi in slice.
      rewrite last_snoc in slice.
      done. }
    iFrame "frag".
  Qed.

  Lemma mapsto_at_increasing ℓ prot ss :
    ℓ ↦_AT^{prot} ss -∗ ⌜ increasing_list (⊑) ss ⌝.
  Proof.
    iNamed 1. iPureIntro. eapply increasing_map_to_increasing_list; done.
  Qed.

  Lemma post_crash_mapsto_at ℓ prot (ss : list ST) :
    ℓ ↦_AT^{prot} ss -∗
    post_crash (λ hG',
      if_rec ℓ (∃ sC,
        crashed_in prot ℓ sC ∗
        (* At least one of our states are still there. *)
        ((∃ ss1 s ss2,
          ⌜ ss1 ++ [s] ++ ss2 = ss ⌝ ∗
          ⌜ ∀ s2, head ss2 = Some s2 → sC ⊑ s2 ⌝ ∗
          ⌜ s ⊑ sC ⌝ ∗
          ℓ ↦_AT^{prot} ((prot.(bumper) <$> ss1) ++ [prot.(bumper) s])) ∨
        (* None of our states where recovered. *)
        ∃ sF,
          ⌜ head ss = Some sF ∧ sC ⊑ sF ∧ sC ≠ sF ⌝ ∗
          ℓ ↦_AT^{prot} [prot.(bumper) sC])
      )
    ).
  Proof.
    rewrite /mapsto_at.
    iNamed 1.
    iDestruct (know_protocol_extract with "locationProtocol")
      as "(-#pred & order & bumper)".
    iAssert (□ ∀ t s, ⎡ know_frag_history_loc ℓ t s ⎤ -∗ _)%I as "#impl".
    { iIntros "!>" (??).
      iApply (post_crash_frag_history with "order offset bumper"). }
    iDestruct "isAtLoc" as "-#isAtLoc".
    rewrite embed_big_sepM.
    iDestruct (big_sepM_impl with "absHist []") as "-#HI".
    { iIntros "!>" (???).
      iApply "impl". }
    iDestruct "offset" as "-#offset".
    iDestruct "locationProtocol" as "-#locationProtocol".
    iCrash.
    iDestruct (if_rec_is_persisted ℓ) as "persisted".
    (* TODO: Why is this [IntoIfRec] instance not picked up automatically. *)
    iDestruct (into_if_rec with "HI") as "HH".
    { apply big_sepM_into_if_rec. intros. apply into_if_rec_if_rec. }
    iModIntro.
    iDestruct "locationProtocol" as "#locationProtocol".
    iDestruct "offset" as (tC CV cvLook) "(crashed & #offset)".
    iDestruct (big_sepM_lookup with "HH") as (sC CV' tC' ?) "(#hi & #crashedIn & #frag & #hi2)".
    { erewrite <- lastEq. eapply map_sequence_lookup_hi. done. }
    iDestruct (crashed_at_agree with "crashed hi") as %<-.
    assert (tC = tC') as <- by congruence.
    (* Note, [sC] is the last location that was recovered after the crash.
     * However, this location may not be among the locations in [ss]. *)
    iExists (sC).
    iSplitL "".
    { iExists _. iFrame "hi crashedIn".
      iSplit; last first.
      - iPureIntro. apply elem_of_dom. done.
      - rewrite /persist_lb.
        iExists (offset + tC), (offset + tC).
        replace (offset + tC - (offset + tC)) with 0 by lia.
        iFrame "persisted".
        iDestruct (have_FV_0) as "$".
        rewrite /lb_base.
        iFrameF "locationProtocol".
        iFrameF "frag".
        iFrameF "offset".
        replace (offset + tC - (offset + tC)) with 0 by lia.
        iDestruct (have_SV_0) as "$". }

    (* Sketch: Case on wether tC+offset is below tLo or not. If it is above
     * show left disjunct. Case on whether sC is equal to sF. If it is equal
     * show left disjunct. If not show right disjunct. *)
    destruct (decide (tLo ≤ tC + offset)).
    - iLeft.
      admit.
    - admit.
  Admitted.

  Global Instance mapsto_at_into_crash ℓ prot ss : IntoCrash _ _ :=
  post_crash_mapsto_at ℓ prot ss.

  Global Instance mapsto_at_into_crash_flush ℓ prot ss : IntoCrashFlush _ _ :=
      into_crash_into_crash_flushed _ _ (post_crash_mapsto_at ℓ prot ss).

  Lemma post_crash_mapsto_na_flush_lb ℓ prot ss (s : ST) :
    flush_lb ℓ prot s -∗
    ℓ ↦_AT^{prot} (ss ++ [s]) -∗
    <PCF> _,
      persist_lb ℓ prot (prot.(bumper) s) ∗
      ℓ ↦_AT^{prot} ((prot.(bumper) <$> ss) ++ [prot.(bumper) s]).
  Proof.
    iIntros "fLb pts".
    iDestruct (mapsto_at_increasing with "pts") as %incr.
    iCrashFlush.
    iDestruct "fLb" as "[pLb (%sC & %le & #xCr)]".
    iDestruct (crashed_in_if_rec with "xCr pts") as (?) "(xCr' & disj)".
    iDestruct (crashed_in_agree with "xCr xCr'") as %<-.
    iDestruct "disj" as "[H|H]"; last first.
    { iDestruct "H" as (? ([= eq] & le2 & neq)) "H".
      rewrite head_lookup in eq.
      assert (s = sC).
      { admit. }
      eapply increasing_list_last_greatest in incr; try done.
      2: { apply _. }
      2: { apply last_snoc. }
      (* destruct sC; try done. *)
  Abort.

End points_to_at_more.

Opaque mapsto_na.
Opaque mapsto_at.
Opaque store_lb.
Opaque flush_lb.
Opaque persist_lb.
Opaque crashed_in.
