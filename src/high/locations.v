(* Assertions for locations.

  The assertions here are modeled usin the more resources defined in
  [self.high.resources], etc.
 *)

From iris.bi Require Import lib.fractional.
From iris.base_logic.lib Require Import own.
From iris.algebra Require Import gset gmap excl auth.
From iris.proofmode Require Import reduction monpred ltac_tactics.
From iris_named_props Require Import named_props.

From self Require Import extra ipm_tactics solve_view_le.
From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import monpred_simpl generational_resources dprop protocol modalities.
From self.high.lib Require Import abstract_state increasing_map.
From self.high.modalities Require Export no_buffer no_flush if_rec or_lost nextgen nextgen_flush.

Section points_to_at.
  Context `{nvmHighGS, AbstractState ST}.

  Implicit Types (ℓ : loc) (s : ST) (ss : list ST) (prot : LocationProtocol ST).

  Lemma singleton_included_l' `{Countable K, CmraTotal A}
        (m : gmap K A) (i : K) x :
    {[i := x]} ≼ m ↔ (∃ y : A, m !! i ≡ Some y ∧ x ≼ y).
  Proof.
    setoid_rewrite <-(Some_included_total x).
    apply singleton_included_l.
  Qed.

  (* Points-to predicate for non-atomics. This predcate says that we know that
     the last events at [ℓ] corresponds to the last element in list [σs] *)
  (* FIXME: Can [mapsto_na] use [lb_base]? *)
  Definition mapsto_na (ℓ : loc) prot (q : frac) (σs : list ST) : dProp Σ :=
    (∃ (tLo tHi offset : time) SV (abs_hist : gmap time ST) (msg : message) σ,
      "%lastEq" ∷ ⌜ last σs = Some σ ⌝ ∗
      "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
      "%incrMap" ∷ ⌜ increasing_map (⊑@{ST}) abs_hist ⌝ ∗
      "#isNaLoc" ∷ ⎡ is_na_loc ℓ ⎤ ∗

      (* [tHi] is the last message and it agrees with the last state in ss. *)
      "%lookupV" ∷ ⌜ abs_hist !! tHi = Some σ ⌝ ∗
      "%nolater" ∷ ⌜ map_no_later abs_hist tHi ⌝ ∗

      (* Ownership over the full abstract history. *)
      "hist" ∷ ⎡ know_full_history_loc ℓ q abs_hist ⎤ ∗
      "#histFrag" ∷ ⎡ know_frag_history_loc ℓ tHi σ ⎤ ∗
      (* "#offset" ∷ ⎡ ℓ ↪[offset_name]□ offset ⎤ ∗ *)
      "#offset" ∷ ⎡ offset_loc ℓ offset ⎤ ∗

      "knowSV" ∷ ⎡ know_na_view ℓ q SV ⎤ ∗
      "%slice" ∷ ⌜ map_sequence abs_hist tLo tHi σs ⌝ ∗
      "#physMsg" ∷ ⎡ know_phys_hist_msg ℓ tHi msg ⎤ ∗
      "#inThreadView" ∷ have_thread_view (SV, msg_persisted_after_view msg, ∅) ∗
      (* We have the [tHi] timestamp in our store view. *)
      "%offsetLe" ∷ ⌜ offset ≤ tHi ⌝ ∗
      "%haveTStore" ∷ ⌜ tHi - offset ≤ SV !!0 ℓ ⌝ ∗
      "#pers" ∷ (⎡ persisted_loc ℓ (tLo - offset) ⎤ ∨ ⌜ tLo - offset = 0 ⌝)
    )%I.

  #[global] Instance mapsto_na_fractional ℓ prot ss :
    Fractional (λ q, mapsto_na ℓ prot q ss).
  Proof.
    intros p q.
    rewrite /mapsto_na.
    iSplit.
    - iNamed 1.
      iDestruct "hist" as "[histP histQ]".
      iDestruct "knowSV" as "[knowSVP knowSVQ]".
      iSplitL "histP knowSVP".
      + by iFrame "∗#".
      + by iFrame "∗#".
    - iDestruct 1 as "[L R]".
      iNamed "L".
      iDestruct "R" as (???????) "(% & _ & % & #? & % & % & histQ & #? & #? & SV & HIP & ?)".
      iDestruct (know_full_history_loc_agree with "hist histQ") as %<-.
      iDestruct (know_na_view_agree with "knowSV SV") as %<-.
      simplify_map_eq.
      repeat iExists _.
      iFrameF (lastEq).
      iFrameF "locationProtocol".
      iFrameF (incrMap).
      iFrameF "isNaLoc".
      iFrame "∗#%".
      iCombine "hist histQ" as "$".
      iCombine "knowSV SV" as "$".
  Qed.

  #[global] Instance mapsto_na_as_fractional ℓ prot q v :
    AsFractional (mapsto_na ℓ prot q v) (λ q, mapsto_na ℓ prot q v)%I q.
  Proof. split; [done | apply _]. Qed.

  (* This is a revived [have_msg_after_fence] before the commit 96f65f5.
   * We (maybe?) need this stronger version in order to extract resource
   * from [p_read] into thread local view. *)
  
  Program Definition have_msg_post_fence msg : dProp Σ :=
    MonPred (λ TV,
      ⌜ msg.(msg_store_view) ⊑ (store_view TV) ⌝
      ∗
      ⌜ msg.(msg_persisted_after_view) ⊑ (flush_view TV ⊔ buffer_view TV) ⌝
    )%I _.
  Next Obligation. solve_proper. Qed.

  #[global] Instance have_msg_post_fence_persistent msg :
    Persistent (have_msg_post_fence msg).
  Proof. apply monPred_persistent=> j. apply _. Qed.

  Lemma have_msg_post_fence_empty v PV : ⊢ have_msg_post_fence (Msg v ∅ PV ∅).
  Proof.
    iModel. simpl. iPureIntro. split; apply view_empty_least.
  Qed.

  (* and for the original assertion, I'm changing its name to be more explicit. *)
  
  Program Definition have_msg_store_view msg : dProp Σ :=
    MonPred (λ TV,
      ⌜ msg.(msg_store_view) ⊑ (store_view TV) ⌝
      (* ∗ *)
      (* ⌜ msg.(msg_persisted_after_view) ⊑ (flush_view i.1 ⊔ buffer_view i.1) ⌝ *)
    )%I _.
  Next Obligation. solve_proper. Qed.

  #[global] Instance have_msg_store_view_persistent msg :
    Persistent (have_msg_store_view msg).
  Proof. apply monPred_persistent=> j. apply _. Qed.

  #[global] Instance have_msg_store_view_buffer_free msg :
    BufferFree (have_msg_store_view msg).
  Proof. rewrite /IntoNoBuffer. iModel. done. Qed.

  #[global] Instance have_msg_store_view_flush_free msg :
    FlushFree (have_msg_store_view msg).
  Proof. rewrite /IntoNoFlush. iModel. done. Qed.

  Lemma have_msg_store_view_empty v PV : ⊢ have_msg_store_view (Msg v ∅ PV ∅).
  Proof.
    iModel. simpl. iPureIntro. apply view_empty_least.
  Qed.

  Definition mapsto_at ℓ prot ss : dProp Σ :=
    (∃ (abs_hist : gmap time ST) (phys_hist : gmap time message) tLo tS offset s ms,
        "%lastEq" ∷ ⌜ last ss = Some s ⌝ ∗ (* NOTE: Could we change this to non-empty? *)
        "%slice" ∷ ⌜ map_sequence abs_hist tLo tS ss ⌝ ∗
        "%slicePhys" ∷ ⌜ map_sequence phys_hist tLo tS ms ⌝ ∗
        "%nolater" ∷ ⌜ map_no_later abs_hist tS ⌝ ∗
        "%absPhysHistDomEq" ∷ ⌜ dom abs_hist = dom phys_hist ⌝ ∗
        "#isAtLoc" ∷ ⎡ is_at_loc ℓ ⎤ ∗
        "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
        "%incrMap" ∷ ⌜ increasing_map (⊑@{ST}) abs_hist ⌝ ∗
        "#absHist" ∷
          ([∗ map] t ↦ s ∈ abs_hist, ⎡ know_frag_history_loc ℓ t s ⎤) ∗
        "#physHist" ∷
          ([∗ map] t ↦ msg ∈ phys_hist,
             (* When we load a message for this location only the views in that
              * message are physically added to our thread. If we want to access the
              * invariants for all the prior messages then we need to remember that
              * that these views have been added. We may however be able to lift this
              * requirement to make [mapsto_at] flush free due to how predicates are
              * used in [wp_load_at] (only objective things can be extracted). *)
             have_msg_store_view msg ∗
             ⎡ know_phys_hist_msg ℓ t msg ⎤) ∗
        "#offset" ∷ ⎡ offset_loc ℓ offset ⎤ ∗
        "#tSLe" ∷ have_SV ℓ (tS - offset)).
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

Section mapsto_at_lemmas.
  Context `{nvmHighGS, AbstractState ST}.

  Set Default Proof Using "Type*".

  Implicit Types (ℓ : loc) (s σ : ST) (ss σs : list ST) (prot : LocationProtocol ST).

  #[global] Instance mapsto_at_persistent ℓ prot ss :
    Persistent (mapsto_at ℓ prot ss).
  Proof. apply _. Qed.

  #[global] Instance mapsto_at_buffer_free ℓ prot (ss : list ST) :
    BufferFree (mapsto_at ℓ prot ss).
  Proof. rewrite /mapsto_at. apply _. Qed.

  #[global] Instance mapsto_at_flush_free ℓ prot (ss : list ST) :
    FlushFree (mapsto_at ℓ prot ss).
  Proof. apply _. Qed.

  #[global] Instance mapsto_at_contractive ℓ ss bumper:
    Contractive (λ (invs : loc_predO ST * loc_predO ST * loc_predO ST),
                   let '(full, read, pers) := invs in
                   (ℓ ↦_AT^{MkProt full read pers bumper} ss)).
  Proof.
    rewrite /mapsto_at.
    intros ????.
    destruct x as [[full read] pers].
    destruct y as [[full' read'] pers'].
    f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
    f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
    f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
    apply (know_protocol_contractive ℓ bumper n (ST := ST) (full, read, pers) (full', read', pers')).
    assumption.
  Qed.

  Definition lb_base ℓ prot offset tS (s : ST) : dProp Σ :=
    "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
    "#knowFragHist" ∷ ⎡ know_frag_history_loc ℓ tS s ⎤ ∗
    "#offset" ∷ ⎡ offset_loc ℓ offset ⎤ ∗
    "#tSLe" ∷ have_SV ℓ (tS - offset).
  
  Program Definition seen_view msg : dProp Σ :=
    MonPred (λ TV,
      ⌜ msg.(msg_store_view) ⊑ (store_view TV) ⌝
      ∗
      ⌜ msg.(msg_persisted_after_view) ⊑ (flush_view TV) ⌝
    )%I _.
  Next Obligation. solve_proper. Qed.

  #[global] Instance seen_view_buffer_free msg:
    BufferFree (seen_view msg).
  Proof. rewrite /IntoNoBuffer. iModel. done. Qed.

  #[global] Instance seen_view_persistent msg:
    Persistent (seen_view msg).
  Proof. rewrite /Persistent. iModel. iIntros "% !>". done. Qed.

  Lemma seen_view_have_msg_post_fence msg:
    seen_view msg -∗ have_msg_post_fence msg.
  Proof.
    iModel.
    iIntros "[% %]".
    simpl.
    iSplitPure; first done.
    iPureIntro.
    solve_view_le.
  Qed.
  
  Definition seen_state ℓ (s : ST) : dProp Σ :=
    ∃ (t offset : nat) (msg: message),
      "#knowFragHist" ∷ ⎡ know_frag_history_loc ℓ t s ⎤ ∗
      "#offset" ∷ ⎡ offset_loc ℓ offset ⎤ ∗
      "#tSLe" ∷ have_SV ℓ (t - offset) ∗
      "#knowPhysMsg" ∷ ⎡ know_phys_hist_msg ℓ t msg ⎤ ∗
      "#seenView" ∷ seen_view msg.

  #[global] Instance seen_state_Persistent ℓ s:
    Persistent (seen_state ℓ s).
  Proof. apply _. Qed.

  #[global] Instance seen_state_buffer_free ℓ s:
    BufferFree (seen_state ℓ s).
  Proof. apply _. Qed.
  
  Definition seen_state_post_fence ℓ (s : ST) : dProp Σ :=
    ∃ (t offset : nat) (msg: message),
      "#knowFragHist" ∷ ⎡ know_frag_history_loc ℓ t s ⎤ ∗
      "#offset" ∷ ⎡ offset_loc ℓ offset ⎤ ∗
      "#tSLe" ∷ have_SV ℓ (t - offset) ∗
      "#knowPhysMsg" ∷ ⎡ know_phys_hist_msg ℓ t msg ⎤ ∗
      "#haveMsg" ∷ have_msg_post_fence msg.

  Lemma seen_state_post_fence_seen_state_post_fence ℓ (s: ST):
    <fence> seen_state ℓ s -∗ seen_state_post_fence ℓ s.
  Proof.
    iModel.
    simpl.
    iDestruct 1 as (t offset msg) "(knowFragHist & ? & ? & knowPhysMsg & #seenView)".
    iExists t, offset, msg.
    iFrame.
    simpl.
    done.
  Qed.

  Definition store_lb ℓ prot (s : ST) : dProp Σ :=
    ∃ (tS : nat) (offset : nat),
      "#lbBase" ∷ lb_base ℓ prot offset tS s.

  Definition flush_lb ℓ prot (s : ST) : dProp Σ :=
    ∃ (tF : nat) offset,
      "#lbBase" ∷ lb_base ℓ prot offset tF s ∗
      (* Either we have something in the flush view or the location is
      persisted. The later case is for after a crash where we don't have
      anything in the flush view. *)
      "#viewFact" ∷ (have_FV_strong ℓ (tF - offset) ∨
                    ⎡ persisted_loc ℓ (tF - offset) ⎤).

  (* Definition pview_lb_high ℓ t: dProp Σ := *)
  (*   lift_d (λ nD, own pview_lb_name (◯ {[ ℓ := MaxNat t ]})). *)

  Program Definition persist_lb ℓ prot (sP : ST) : dProp Σ :=
    ∃ tP offset,
      "#lbBase" ∷ lb_base ℓ prot offset tP sP ∗
      (* We have the persisted state in our store view. *)
      "#tPLe" ∷ have_FV ℓ (tP - offset) ∗
      "persisted" ∷ ⎡ persisted_loc ℓ (tP - offset) ⎤.

  Definition crashed_in prot ℓ σ : dProp Σ :=
    "#persistLb" ∷ persist_lb ℓ prot (prot.(p_bumper) σ) ∗
    "#crashedIn" ∷ ⎡ crashed_in_loc ℓ σ ⎤.

  #[global] Instance crashed_in_persistent prot ℓ s :
    Persistent (crashed_in prot ℓ s).
  Proof. apply _. Qed.

  (* [ℓ] was not recovered at the last crash. *)
  Definition lost ℓ : dProp Σ :=
    ∃ OCV,
      "#crashed" ∷ ⎡ crashed_at_offset OCV ⎤ ∗
      "%notInCV" ∷ ⌜ℓ ∉ dom OCV⌝.

  Lemma store_lb_protocol ℓ prot s :
    store_lb ℓ prot s -∗ ⎡ know_protocol ℓ prot ⎤.
  Proof. iNamed 1. iNamed "lbBase". iFrame "locationProtocol". Qed.

  #[global] Instance store_lb_persistent
         ℓ prot (s : ST) : Persistent (store_lb ℓ prot s).
  Proof. apply _. Qed.

  #[global] Instance flush_lb_persistent
         ℓ prot (s : ST) : Persistent (flush_lb ℓ prot s).
  Proof. apply _. Qed.

  #[global] Instance persist_lb_persistent
         ℓ prot (s : ST) : Persistent (persist_lb ℓ prot s).
  Proof. apply _. Qed.

  Lemma persist_lb_to_flush_lb ℓ prot s :
    persist_lb ℓ prot s ⊢ flush_lb ℓ prot s.
  Proof. iNamed 1. iExistsN. iFrame "∗#". Qed.

  Lemma flush_lb_to_store_lb ℓ prot s :
    flush_lb ℓ prot s ⊢ store_lb ℓ prot s.
  Proof. iNamed 1. iExistsN. iFrame "∗#". Qed.

  Lemma persist_lb_to_store_lb ℓ prot s :
    persist_lb ℓ prot s ⊢ store_lb ℓ prot s.
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

  (* Lemma base_crashed_in_agree `{Countable ST} ℓ (s1 s2 : ST) : *)
  (*   crashed_in_loc ℓ s1 -∗ crashed_in_loc ℓ s2 -∗ ⌜ s1 = s2 ⌝. *)
  (* Proof. *)
  (*   simpl. *)
  (*   rewrite /crashed_in_loc. *)
  (*   iDestruct 1 as (? eq1) "pts1". *)
  (*   iDestruct 1 as (? eq2) "pts2". *)
  (*   iDestruct (ghost_map_elem_agree with "pts1 pts2") as %->. *)
  (*   iPureIntro. *)
  (*   congruence. *)
  (* Qed. *)

  Lemma know_frag_history_loc_agree ℓ t (σ σ': ST):
    know_frag_history_loc ℓ t σ -∗ know_frag_history_loc ℓ t σ' -∗ ⌜ σ = σ' ⌝.
  Proof. apply know_frag_history_singleton_agree. Qed.

  Lemma crashed_in_agree prot ℓ s s' :
    crashed_in prot ℓ s -∗ crashed_in prot ℓ s' -∗ ⌜ s = s' ⌝.
  Proof.
    iNamed 1.
    iDestruct 1 as "[_ crashedIn']".
    by iDestruct (crashed_in_loc_agree with "crashedIn crashedIn'") as %->.
  Qed.

  (* Lemma crashed_in_or_lost `{AbstractState ST} prot ℓ P (s : ST) : *)
  (*   crashed_in prot ℓ s -∗ or_lost ℓ P -∗ P. *)
  (* Proof. *)
  (*   iNamed 1. iIntros "P". *)
  (*   iApply (or_lost_get with "crashed_at P"). *)
  (*   apply elem_of_dom. done. *)
  (* Qed. *)

  Lemma crashed_in_if_rec `{AbstractState ST} prot ℓ P (s : ST) :
    crashed_in prot ℓ s -∗ if_rec ℓ P -∗ P.
  Proof.
    iNamed 1. iNamed "persistLb". iIntros "P".
    iDestruct (persisted_loc_weak with "persisted") as "persisted2".
    { apply le_0_n. }
    iDestruct "crashedIn" as (??) "(OCV & % & _)".
    iApply "P"; iFrame "#%".
    rewrite -elem_of_dom //.
  Qed.

  Lemma crashed_in_persist_lb `{AbstractState ST} prot ℓ (s : ST) :
    crashed_in prot ℓ s -∗ persist_lb ℓ prot (prot.(p_bumper) s).
  Proof. iNamed 1. iFrame "persistLb". Qed.

  (* Lemmas for [mapsto_na] *)

  Lemma mapsto_na_store_lb ℓ prot q ss s :
    mapsto_na ℓ prot q (ss ++ [s]) -∗
    store_lb ℓ prot s.
  Proof.
    iNamed 1.
    iExists tHi, offset.
    rewrite last_snoc in lastEq.
    simplify_eq.
    iFrame "#".
    iApply monPred_in_have_SV; done.
  Qed.

  Lemma mapsto_na_last ℓ prot q ss :
    mapsto_na ℓ prot q ss -∗ ⌜ ∃ s, last ss = Some s ⌝.
  Proof.
    rewrite /mapsto_na.
    iNamed 1.
    apply map_sequence_lookup_hi_alt in slice.
    naive_solver.
  Qed.

  Lemma mapsto_na_store_lb_incl σs σ1 σ2 ℓ prot q :
    store_lb ℓ prot σ1 -∗
    mapsto_na ℓ prot q (σs ++ [σ2]) -∗
    ⌜ σ1 ⊑ σ2 ⌝.
  Proof.
    iIntros "storeLb".
    iNamed 1.
    rewrite last_snoc in lastEq.
    assert (σ = σ2) as -> by congruence.
    iDestruct "storeLb" as (t ?) "(_ & histFrag' & _)".
    iDestruct (know_full_history_lookup with "hist histFrag'") as %look.
    eassert _ as le. { eapply map_no_later_Some; done. }
    iPureIntro.
    eapply increasing_map_increasing in incrMap; done.
  Qed.

  Lemma mapsto_na_flush_lb_incl σs σ1 σ2 ℓ prot q :
    flush_lb ℓ prot σ1 -∗
    mapsto_na ℓ prot q (σs ++ [σ2]) -∗
    ⌜ σ1 ⊑ σ2 ⌝.
  Proof. rewrite flush_lb_to_store_lb. apply mapsto_na_store_lb_incl. Qed.

  Lemma mapsto_na_increasing ℓ prot q σs :
    mapsto_na ℓ prot q σs -∗ ⌜ increasing_list (⊑) σs ⌝.
  Proof.
    iNamed 1. iPureIntro. eapply increasing_map_to_increasing_list; done.
  Qed.

  Lemma mapsto_na_persist_lb ℓ prot q σs σ1 σ2 σ3 :
    ¬(σ2 ⊑ σ1) →
    mapsto_na ℓ prot q (σ1 :: σ3 :: σs) -∗
    persist_lb ℓ prot σ2 -∗
    mapsto_na ℓ prot q (σ3 :: σs).
  Proof.
    iIntros (gt).
    iNamed 1.
    iDestruct 1 as (tP2 ?) "((? & frag & ? & ?) & ? & ?)".
    assert (abs_hist !! tLo = Some σ1) as lookTP.
    { apply map_sequence_lookup_lo in slice. done. }
    apply map_sequence_cons_drop in slice as (tP3 & lt & noin & slice).
    iExists tP3, tHi, offset, SV, abs_hist, msg, σ.
    (* The non-trivial task now is to σhow that [tP2] is larger than [tP3]. *)
    iDestruct (know_full_history_lookup with "hist frag") as %lookTP2.
    assert (tLo < tP2). {
      apply (increasing_map_lookup_lt abs_hist _ _ σ1 σ2 incrMap); done. }
    destruct (decide (tP3 ≤ tP2)).
    2: { exfalso.
      assert (tLo < tP2 < tP3) as order by lia.
      specialize (noin tP2 order).
      congruence. }
    iDestruct (offset_loc_agree with "offset [$]") as %<-.
    iFrameF (lastEq). iFrameF "locationProtocol". iFrameF (incrMap).
    iFrameF "isNaLoc". iFrameF (lookupV). iFrameF (nolater).
    iFrameF "hist". iFrameF "histFrag". iFrameF "offset". iFrameF "knowSV".
    iFrameF (slice). iFrame "physMsg". iFrame "inThreadView".
    iSplitPure; first done.
    iFrameF (haveTStore).
    iLeft. iApply persisted_loc_weak; last done. lia.
  Qed.

  Lemma mapsto_na_persist_lb_last ℓ prot q σs σ `{!AntiSymm (=) (⊑@{ST})} :
    last σs = Some σ →
    persist_lb ℓ prot σ -∗
    mapsto_na ℓ prot q σs -∗
    mapsto_na ℓ prot q [σ].
  Proof.
    induction σs as [|s1 σs IH]; first done.
    iIntros (lastLook) "#per pts".
    destruct σs as [|s2 σs].
    { inversion lastLook. done. }
    iApply IH.
    - done.
    - done.
    - iDestruct (mapsto_na_increasing with "[$]") as %incr.
      iApply (mapsto_na_persist_lb with "pts per").
  Abort. (* This lemma only holds if [s] is σtrictly greater than all other
  elements of [ss]. *)

  (* Lemma mapsto_na_persist_lb ℓ prot q σs σ1 σ2 σ3 : *)
  (*   ¬(s2 ⊑ σ1) → *)
  (*   σs !! i = σome σ1 → *)
  (*   length σs *)
  (*   mapsto_na ℓ prot q σs -∗ *)
  (*   persist_lb ℓ prot σ2 -∗ *)
  (*   mapsto_na ℓ prot q (drop i σs). *)
  (* Proof. *)
  (* (* Instances. *) *)

  Lemma flush_lb_no_buffer ℓ prot (σ : ST) :
    flush_lb ℓ prot σ ⊢ <nobuf> flush_lb ℓ prot σ.
  Proof. iNamed 1. iModIntro. iExists _, _. iFrame "#∗". Qed.

  #[global] Instance buffer_free_flush_lb ℓ prot (σ : ST) :
    BufferFree (flush_lb ℓ prot σ).
  Proof. rewrite /IntoNoBuffer. eauto using flush_lb_no_buffer. Qed.

  (* TODO: Prove this in the σame way as [flush_lb_no_buffer]. We need more noflush instances. *)
  Lemma no_flush_store_lb ℓ prot (σ : ST) :
    store_lb ℓ prot σ ⊢ <noflush> store_lb ℓ prot σ.
  Proof. iNamed 1. iModIntro. iExists _, _. iFrame "#∗". Qed.
  (*   iNamed 1. *)
  (*   iNamed "lbBase". *)
  (*   iModIntro. *)
  (*   rewrite /store_lb. *)
  (*   iModel. *)
  (*   σimpl. *)
  (*   iDestruct 1 as (?) "HI". iExists _. iFrame. *)
  (* Qed. *)
  #[global] Instance flush_free_flush_lb ℓ prot (σ : ST) :
    FlushFree (store_lb ℓ prot σ).
  Proof. rewrite /IntoNoFlush. eauto using no_flush_store_lb. Qed.

  Lemma no_buffer_store_lb ℓ prot (σ : ST) :
    store_lb ℓ prot σ ⊢ <nobuf> store_lb ℓ prot σ.
  Proof. iNamed 1. iModIntro. iExists _, _. iFrame "#∗". Qed.

  #[global] Instance into_no_buffer_store_lb ℓ prot (σ: ST) :
    BufferFree (store_lb ℓ prot σ).
  Proof. rewrite /IntoNoBuffer. eauto using no_buffer_store_lb. Qed.

  #[global] Instance mapsto_na_buffer_free ℓ prot q (σs : list ST) :
    BufferFree (mapsto_na ℓ prot q σs).
  Proof. apply _. Qed.

  Ltac iIntroNGProtocol H :=
    iRename H into "Htemp";
    iDestruct (nextgen_know_protocol $! (∅, ∅, ∅) with "[]") as H;
    first (iNamed "Htemp"; iFrame "#");
    iClear "Htemp".

  Lemma crashed_at_expand CV:
    crashed_at CV -∗
    ∃ OV OCV, ⌜ dom CV = dom OCV ⌝ ∗ ⌜ OCV `view_sub` OV = CV ⌝ ∗
              crashed_at_both OV OCV ∗ crashed_at_offset OCV.
  Proof.
    iDestruct 1 as (???) "(<- & ? & _)".
    iExists OV, OCV.
    rewrite view_sub_dom_eq.
    repeat (iSplit; first done).
    by iExists _.
  Qed.

  Lemma nextgen_persist_lb ℓ prot σ :
    persist_lb ℓ prot σ ⊢
    <NG>
      (persist_lb ℓ prot (prot.(p_bumper) σ) ∗
       ∃ σ_c, ⌜ σ ⊑ σ_c ⌝ ∗ crashed_in prot ℓ σ_c).
  Proof.
    iModel.
    iIntros "(%tP & %offset & persistLb)".
    iNamed "persistLb". iNamed "lbBase".
    rewrite know_protocol_into_nextgen.
    iDestruct "tSLe" as %tSLe. iDestruct "tPLe" as %tPLe.
    rewrite /nextgen /=.
    iIntros "!> #Hfrag".
    iDestruct "persisted" as "(#persisted & %CV & %HPVCV & #CV)".
    
    iDestruct (crashed_at_expand with "CV") as (OV OCV domEq σubEq) "[OVOCV OCV]".
    assert (is_Some (OCV !! ℓ)) as [[tC] OCVLook].
    { rewrite -elem_of_dom -domEq elem_of_dom.
      by apply view_le_singleton in HPVCV as (? & ? & ?). }

    iAssert (persisted_loc ℓ 0)%I as "persisted_loc".
    { iApply (persisted_persisted_loc with "persisted"). eapply view_to_zero_lookup, lookup_singleton_eq. }
    
    (* unpack all [base_if_rec] modalities *)
    iSpecialize ("offset" with "[//] OCV persisted_loc").
    iSpecialize ("locationProtocol" with "[//] OCV persisted_loc").

    (* unify crash view related knowledge. *)
    iDestruct "offset" as (?) "[offset CVimpl]".
    iDestruct ("CVimpl" with "[$]") as %[ <- HOCVLook' ].
    simplify_map_eq.
    assert (tC = OCV !!0 ℓ) as ->.
    { rewrite /lookup_zero OCVLook //. }
    assert (tP - (OV !!0 ℓ) ≤ OCV !!0 ℓ - (OV !!0 ℓ)).
    { rewrite view_included in HPVCV.
      specialize (HPVCV ℓ).
      rewrite lookup_singleton_eq view_sub_lookup OCVLook Some_MaxNat_included /= in HPVCV.
      done. }
    iClear "CVimpl".
    
    iDestruct "locationProtocol" as "(last_bumper & last_preorder & prot)".
    iDestruct "knowFragHist" as "[lastFrag knowFragHist]".
    iDestruct ("Hfrag" $! ℓ tP _ _ _ _ _ _ _ _ with "OVOCV [%] [$] [$] [$]")
      as "(% & % & #crashed_in & #knowFragHistC & _ & %order)".
    { rewrite elem_of_dom. by eexists. }
    odestruct (order _) as [? ?]; first lia.
    iClear "Hfrag".
    assert (tP ≤ OCV !!0 ℓ) by lia.
    iSpecialize ("knowFragHist" $! OCV (prot.(p_bumper)) with "[%] [$] []").
    { rewrite elem_of_dom.
      split; first by eexists.
      done. }
    { by iNamed "prot". }
    monPred_simpl.
    iSplit.
    - (* [persist_lb (bumper σ)] *)
      iExists tP, (OCV !!0 ℓ).
      iFrame "prot offset knowFragHist".
      replace (tP - (OCV !!0 ℓ)) with 0 by lia.
      iSplit; first iApply have_SV_0.
      iSplit; first iApply have_FV_0.
      done.
    - (* [crashed_in_prot] *)
      iExists σ_c.
      monPred_simpl.
      iSplit; first done.
      iFrame "crashed_in".
      iExists (OCV !!0 ℓ), (OCV !!0 ℓ).
      iFrame "prot offset knowFragHistC".
      replace ((OCV !!0 ℓ) - (OCV !!0 ℓ)) with 0 by lia.
      iSplit; first iApply have_SV_0.
      iSplit; first iApply have_FV_0.
      done.
  Qed.
  
  #[global] Instance persist_lb_into_nextgen ℓ prot σ : IntoNextgen _ _ :=
    nextgen_persist_lb ℓ prot σ.

  Lemma nextgen_flush_flush_lb (ℓ : loc) prot (σ: ST) :
    flush_lb ℓ prot σ ⊢
    <NGF> persist_lb ℓ prot (p_bumper prot σ) ∗
    ∃ σ__pc, ⌜ σ ⊑ σ__pc ⌝ ∗ crashed_in prot ℓ σ__pc.
  Proof.
    iModel. destruct TV as [[SV FV] PV].
    iIntros "(%tF & %offset & flushLb)".
    iNamed "flushLb". iNamed "lbBase".
    rewrite know_protocol_into_nextgen.
    rewrite /nextgen /=.
    iIntros "!> #Hfrag".
    monPred_simpl.
    iIntros (CV TV' ?) "(% & #persisted_FV & #CV)".
    iAssert (persisted (view_to_zero {[ℓ := MaxNat (tF - offset)]}) ∗
             ⌜{[ℓ := MaxNat (tF - offset)]} ⊑ CV⌝)%I as "[persisted %HPVCV]".
    { iDestruct "viewFact" as "[% | ($ & %CV' & % & CV')]".
      - iSplit.
        + iApply (persisted_weak with "persisted_FV").
          f_equiv.
          solve_view_le.
        + iPureIntro.
          solve_view_le.
      - by iDestruct (crashed_at_agree with "CV CV'") as %<-. }
    (* TODO: The rest of the proof is essentially the σame as the proof for [persisted_lb].
     * It would be nice if they can be moved into a σhared lemma. *)
    iDestruct (crashed_at_expand with "CV") as (OV OCV domEq σubEq) "[OVOCV OCV]".
    assert (is_Some (OCV !! ℓ)) as [[tC] OCVLook].
    { rewrite -elem_of_dom -domEq elem_of_dom.
      by apply view_le_singleton in HPVCV as (? & ? & ?). }

    iAssert (persisted_loc ℓ 0)%I as "persisted_loc".
    { iApply (persisted_persisted_loc with "persisted"). eapply view_to_zero_lookup, lookup_singleton_eq. }
    
    (* unpack all [base_if_rec] modalities *)
    iSpecialize ("offset" with "[//] OCV persisted_loc").
    iSpecialize ("locationProtocol" with "[//] OCV persisted_loc").

    (* unify crash view related knowledge. *)
    iDestruct "offset" as (?) "[offset CVimpl]".
    iDestruct ("CVimpl" with "[$]") as %[ <- HOCVLook' ].
    simplify_map_eq.
    assert (tC = OCV !!0 ℓ) as ->.
    { rewrite /lookup_zero OCVLook //. }
    assert (tF - (OV !!0 ℓ) ≤ OCV !!0 ℓ - (OV !!0 ℓ)).
    { rewrite view_included in HPVCV.
      specialize (HPVCV ℓ).
      rewrite lookup_singleton_eq view_sub_lookup OCVLook Some_MaxNat_included /= in HPVCV.
      done. }
    iClear "CVimpl".
    
    iDestruct "locationProtocol" as "(last_bumper & last_preorder & prot)".
    iDestruct "knowFragHist" as "[lastFrag knowFragHist]".
    iDestruct ("Hfrag" $! ℓ tF _ _ _ _ _ _ _ _ with "OVOCV [%] [$] [$] [$]")
      as "(% & % & #crashed_in & #knowFragHistC & _ & %order)".
    { rewrite elem_of_dom. by eexists. }
    odestruct (order _) as [? ?]; first lia.
    iClear "Hfrag".
    assert (tF ≤ OCV !!0 ℓ) by lia.
    iSpecialize ("knowFragHist" $! OCV (prot.(p_bumper)) with "[%] [$] []").
    { rewrite elem_of_dom.
      split; first by eexists.
      done. }
    { by iNamed "prot". }
    monPred_simpl.
    iSplit.
    - (* [persist_lb (bumper σ)] *)
      iExists tF, (OCV !!0 ℓ).
      iFrame "prot offset knowFragHist".
      replace (tF - (OCV !!0 ℓ)) with 0 by lia.
      iSplit; first iApply have_SV_0.
      iSplit; first iApply have_FV_0.
      done.
    - (* [crashed_in_prot] *)
      iExists σ_c.
      monPred_simpl.
      iSplit; first done.
      iFrame "crashed_in".
      iExists (OCV !!0 ℓ), (OCV !!0 ℓ).
      iFrame "prot offset knowFragHistC".
      replace ((OCV !!0 ℓ) - (OCV !!0 ℓ)) with 0 by lia.
      iSplit; first iApply have_SV_0.
      iSplit; first iApply have_FV_0.
      done.
  Qed.

  #[global] Instance know_flush_into_nextgen ℓ prot (σ: ST) :
    IntoNGFlush (flush_lb ℓ prot σ) _ := nextgen_flush_flush_lb ℓ prot σ.

  Lemma mapsto_at_store_lb ℓ prot σs σ :
    ℓ ↦_AT^{prot} (σs ++ [σ]) ⊢ store_lb ℓ prot σ.
  Proof.
    iNamed 1.
    iExists tS, offset.
    simplify_eq.
    iFrame "#".
    iDestruct (big_sepM_lookup with "absHist") as "frag".
    { apply map_sequence_lookup_hi in slice.
      rewrite last_snoc in slice.
      done. }
    iFrame "frag".
  Qed.
  
  (* TODO: restore this lemma *)
  (* Lemma post_crash_store_lb (ℓ : loc) prot (σ: ST) : *)
  (*   store_lb ℓ prot σ -∗ *)
  (*   <PC> if_rec ℓ (∃ (s' : σT), persist_lb ℓ prot σ'). *)
  (* Proof. *)
  (*   iNamed 1. iNamed "lbBase". *)
  (*   iNamed "locationProtocol". *)
  (*   iDestruct (post_crash_frag_history *)
  (*     with "knowPreorder offset knowBumper knowFragHist") as "#H". *)
  (*   iCrashIntro. *)
  (*   iDestruct (if_rec_is_persisted ℓ) as "pers". *)
  (*   iModIntro. *)
  (*   iDestruct "H" as (sC ????) "(#crashed & ? & ? & ? & impl)". *)
  (*   iDestruct "offset" as (???) "(crashed' & ?)". *)
  (*   iDestruct (crashed_at_d_agree with "crashed crashed'") as %->. *)
  (*   simplify_eq. *)
  (*   iExistsN. *)
  (*   iFrame. *)
  (*   replace (offset + tC - (offset + tC)) with 0 by lia. *)
  (*   iDestruct (have_SV_0) as "$". *)
  (*   iDestruct (have_FV_0) as "$". *)
  (*   iFrame "pers". *)
  (* Qed. *)

  (* #[global] Instance store_lb_into_crash ℓ prot σ : IntoCrash _ _ := *)
  (*   post_crash_store_lb ℓ prot σ. *)

  (* Lemma map_sequence_prefix tLo tHi t σs abs_hist : *)
  (*   map_sequence abs_hist tLo tHi σs → *)
  (*   tLo ≤ t ≤ tHi → *)
  (*   ∃ σs', σs' `prefix_of` σs ∧ *)
  (*   map_sequence abs_hist tLo t σs. *)
  (* Proof. *)

  Lemma abs_hist_nextgen OCV ℓ prot `{!ProtocolConditions prot} abs_hist:
    gen_ghost_map.drop_bump_map ℓ (encode_bumper (p_bumper prot)) OCV (encode <$> abs_hist) =
    encode <$> (p_bumper prot <$> drop_above (OCV !!0 ℓ) abs_hist).
  Proof.
    apply map_eq.
    intros t.
    rewrite /gen_ghost_map.drop_bump_map /gen_ghost_map.drop_above_bump.
    rewrite map_lookup_imap ?lookup_fmap.
    destruct (decide _).
    - rewrite drop_above_lookup_le; last lia.
      destruct (abs_hist !! t); simpl; last done.
      rewrite /gen_ghost_map.safe_bumper encode_bumper_encode //.
    - rewrite drop_above_lookup_gt; last lia.
      destruct (abs_hist !! t); simpl; done.
  Qed.
  
  (* TODO: restore this lemma *)
  Lemma post_crash_mapsto_na ℓ prot `{!ProtocolConditions prot} q (σs : list ST) :
    ℓ ↦_{prot}^{q} σs ⊢
    <NG>
      if_rec ℓ (∃ σs' σ,
            ⌜ (σs' ++ [σ]) `prefix_of` σs ⌝ ∗
            crashed_in prot ℓ σ ∗
            ℓ ↦_{prot}^{q} ((p_bumper prot <$> σs') ++ [prot.(p_bumper) σ])).
  Proof.
    iModel. destruct TV as [[SV FV] PV].
    iDestruct 1 as "(%tLo & %tHi & %offset & %SV' & %abs_hist & %msg & %σ & H)".
    iNamed "H".
    iDestruct "inThreadView" as %inThreadView.
    iDestruct (gen_ghost_map_map.full_entry_local_nextgen with "hist []") as "hist".
    { iNamed "locationProtocol". iDestruct "knowBumper" as "[_ $]". }
    rewrite know_protocol_into_nextgen.
    rewrite /nextgen /=.
    iIntros "!> #Hfrag".
    rewrite /if_rec.
    iIntros (OCV TV' ? ?).
    iIntros (TV'' ?) "#OCV".
    iIntros (TV''' ?) "#persisted_loc".
    iAssert (∃ OV, crashed_at_both OV OCV)%I as (OV) "OVOCV".
    { by iDestruct "OCV" as (?) "$". }
    
    (* unpack all [base_if_rec] modalities *)
    iSpecialize ("offset" with "[//] OCV persisted_loc").
    iSpecialize ("locationProtocol" with "[//] OCV persisted_loc").
    iSpecialize ("knowSV" with "[//] OCV persisted_loc").
    iDestruct "hist" as "[lastHist hist]".
    iSpecialize ("hist" with "OCV [%]").
    { rewrite elem_of_dom //. }
    iSpecialize ("isNaLoc" with "OCV").
    rewrite subseteq_intersection_1_L; last rewrite singleton_subseteq_l elem_of_dom //.
    (* unify crash view related knowledge. *)
    iDestruct "offset" as (?) "[offset CVimpl]".
    iDestruct ("CVimpl" with "[$]") as %[ <- HOCVLook' ].
    simplify_map_eq.
    assert (tC = OCV !!0 ℓ) as ->.
    { rewrite /lookup_zero. by simplify_map_eq. }
    
    iDestruct "locationProtocol" as "(last_bumper & last_preorder & prot)".
    iDestruct "histFrag" as "[lastFrag _]".
    iDestruct ("Hfrag" $! ℓ tHi _ _ _ _ _ _ _ _ with "OVOCV [%] [$] [$] [$]")
      as "(% & % & #crashed_in & #knowFragHistC & knowPhysMsgC & _)".
    { rewrite elem_of_dom //. }
    iPoseProof "crashed_in" as "crashed_in_copy".
    iDestruct "crashed_in_copy" as (??) "(OCV' & _ & %Hdecode & lastFragC)".
    iDestruct (crashed_at_offset_agree with "OCV OCV'") as %<-.
    iDestruct ("Hfrag" $! ℓ (OCV !!0 ℓ) _ _ _ _ _ _ _ _ with "OVOCV [%] [$] [] [$]")
      as "(% & % & _ & _ & _ & %order)".
    { rewrite elem_of_dom //. } { iFrame "lastFragC". done. }
    odestruct (order _) as [? _]; first lia.
    iClear "Hfrag".
    clear order σ_c0 v_c0.

    (* [tLo] should be greater than [OCV !!0 ℓ] *)
    iAssert ⌜ tLo ≤ OCV !!0 ℓ ⌝%I as %?.
    { iDestruct "pers" as "[ pers | % ]".
      - iDestruct "pers" as "(_ & %CV & %incl & CV)".
        iDestruct (crashed_at_expand with "CV") as (????) "[OVOCV'' _]".
        iDestruct (crashed_at_both_agree with "OVOCV OVOCV''") as %[ <- <- ].
        iPureIntro.
        apply view_le_singleton in incl as (? & look & ?).
        simplify_eq.
        rewrite view_sub_lookup HOCVLook' /= in look.
        simplify_eq.
        lia.
      - iPureIntro.
        lia. }

    (* [σ_c] should be part of the [σs] *)
    iDestruct (gen_ghost_map_map.lastgen_full_entry_frag_entry with "lastHist lastFragC") as %Hlook.
    apply lookup_fmap_Some in Hlook as (? & <- & Hlook).
    rewrite decode_encode in Hdecode.
    simplify_map_eq.
    pose proof nolater as nolater'.
    apply (map_no_later_Some _ _ (OCV !!0 ℓ)) in nolater; last done.
    eapply map_sequence_prefix_alt in slice as (σs' & ? & ?); [ | done | lia ].
    iExists σs', σ_c.
    iSplitPure; first done.
    iFrame "crashed_in prot offset knowPhysMsgC knowFragHistC knowSV".
    rewrite ?Nat.sub_diag.
    iSplit.
    - (* [crashed_in_prot] *)
      iSplitPure; first lia.
      iSplitPure; first lia.
      done.
    - (* [mapsto_na] *)
      iExists tLo, (prot.(p_bumper) <$> drop_above (OCV !!0 ℓ) abs_hist).
      iSplitPure; first rewrite last_snoc //.
      iSplitPure.
      { apply increasing_map_fmap; first apply _.
        apply increasing_map_filter.
        done. }
      iSplit; first done.
      iSplitPure; first rewrite lookup_fmap drop_above_lookup_t Hlook //.
      iSplitPure; first apply map_no_later_fmap, map_no_later_drop_above.
      iSplitL "hist"; first rewrite abs_hist_nextgen //.
      iSplitPure.
      { rewrite -fmap_snoc.
        apply map_sequence_fmap, map_sequence_drop_above.
        done. }
      iSplitPure; first solve_view_le.
      iSplitPure; first done.
      iSplitPure; first solve_view_le.
      iRight.
      iPureIntro. lia.
  Qed.

  #[global] Instance mapsto_na_into_nextgen ℓ `{!ProtocolConditions prot} q
      (σs : list ST) :
    IntoNextgen _ _ :=
    (post_crash_mapsto_na ℓ prot q σs).
  
  #[global] Instance mapsto_na_into_nextgen_flush ℓ `{!ProtocolConditions prot} q
      (σs : list ST) :
    IntoNGFlush _ _ :=
    (into_nextgen_into_nextgen_flushed _ _ (post_crash_mapsto_na ℓ prot q σs)).

  (* This lemma is σtrictly weaker than the above but could be useful if we do *)
  (* not want to preserve the prefix after a crash. *)
  Lemma nextgen_mapsto_na_singleton ℓ `{!ProtocolConditions prot} q (σs : list ST) :
    ℓ ↦_{prot}^{q} σs -∗
    <NG> if_rec ℓ (∃ σ,
        ⌜ σ ∈ σs ⌝ ∗
        crashed_in prot ℓ σ ∗
        ℓ ↦_{prot}^{q} [prot.(p_bumper) σ]).
  Proof.
    iIntros "pts".
    iModIntro. iModIntro.
    iDestruct "pts" as (???) "(crashed & pts)".
    iExists σ.
    iSplitPure.
    { eapply list_elem_of_lookup_2.
      eapply prefix_lookup_Some; last done.
      erewrite <- last_lookup.
      apply last_snoc. }
    iDestruct (crashed_in_persist_lb with "[$]") as "#per".
  Abort. (* This σhould be true but is a bit annoying to σhow. *)

  Lemma mapsto_at_increasing ℓ prot σs :
    ℓ ↦_AT^{prot} σs ⊢ ⌜ increasing_list (⊑) σs ⌝.
  Proof.
    iNamed 1. iPureIntro. eapply increasing_map_to_increasing_list; done.
  Qed.

  Lemma nextgen_mapsto_at_singleton ℓ prot (σs : list ST) :
    ℓ ↦_AT^{prot} σs ⊢
    <NG>
      if_rec ℓ (∃ σ_c,
        crashed_in prot ℓ σ_c ∗
        ℓ ↦_AT^{prot} [prot.(p_bumper) σ_c]).
  Proof.
    iModel. destruct TV as [[SV FV] PV].
    iDestruct 1 as "(%abs_hist & %phys_hist & %tLo & %tS & %offset & %σ & %ms & H)".
    iNamed "H".
    iDestruct "tSLe" as %tSLe.
    rewrite -embed_big_sepM monPred_at_embed.
    (* In order to obtain [crashed_in], all we need to know is a σingle abstract message. *)
    iDestruct (big_sepM_lookup with "absHist") as "knowFragHist".
    { erewrite <- lastEq. eapply map_sequence_lookup_hi. done. }
    rewrite know_protocol_into_nextgen.
    rewrite /nextgen /=.
    iIntros "!> #Hfrag".
    rewrite /if_rec.
    iIntros (OCV TV' ? ?).
    iIntros (TV'' ?) "#OCV".
    iIntros (TV''' ?) "#persisted_loc".
    iAssert (∃ OV, crashed_at_both OV OCV)%I as (OV) "OVOCV".
    { by iDestruct "OCV" as (?) "$". }
    
    (* unpack all [base_if_rec] modalities *)
    iSpecialize ("offset" with "[//] OCV persisted_loc").
    iSpecialize ("locationProtocol" with "[//] OCV persisted_loc").
    iSpecialize ("isAtLoc" with "OCV").
    rewrite subseteq_intersection_1_L; last rewrite singleton_subseteq_l elem_of_dom //.
    (* unify crash view related knowledge. *)
    iDestruct "offset" as (?) "[offset CVimpl]".
    iDestruct ("CVimpl" with "[$]") as %[ <- HOCVLook' ].
    simplify_map_eq.
    assert (tC = OCV !!0 ℓ) as ->.
    { rewrite /lookup_zero. by simplify_map_eq. }
    
    iDestruct "locationProtocol" as "(last_bumper & last_preorder & prot)".
    iDestruct "knowFragHist" as "[lastFrag _]".
    iDestruct ("Hfrag" $! ℓ tS _ _ _ _ _ _ _ _ with "OVOCV [%] [$] [$] [$]")
      as "(% & % & #crashed_in & #knowFragHistC & knowPhysMsgC & _)".
    { rewrite elem_of_dom. by eexists. }
    iClear "Hfrag".
    iExists σ_c.
    iFrame "prot offset knowFragHistC".
    rewrite ?Nat.sub_diag.
    iSplit.
    - (* [crashed_in_prot] *)
      iSplit; last done.
      iSplitPure; first lia.
      iSplitPure; first lia.
      done.
    - (* [mapstoat] *)
      iExists {[ (OCV !!0 ℓ) := (p_bumper prot σ_c) ]}, {[ (OCV !!0 ℓ) := _ ]}, (OCV !!0 ℓ), (OCV !!0 ℓ), (p_bumper prot σ_c), [_].
      iSplitPure; first done.
      iSplitPure; first rewrite lookup_singleton_eq //.
      simpl.
      iSplitPure; first rewrite lookup_singleton_eq //.
      iSplitPure; first apply map_no_later_singleton.
      iSplitPure; first rewrite ?dom_singleton_L //.
      iSplit; first done.
      rewrite 2!big_sepM_singleton.
      iSplitPure; first apply increasing_map_singleton.
      iFrame "knowFragHistC".
      iFrame "knowPhysMsgC".
      solve_view_le.
  Qed.
  
  (* NOTE: This lemma is (very likely) σound and is σtrictly σtronger than the
   * lemma above. We have, however, not had a need for it yet and thus the
   * proof is aborted (for now). *)

  (* Lemma post_crash_mapsto_at ℓ prot (σs : list ST) : *)
  (*   ℓ ↦_AT^{prot} σs ⊢ *)
  (*   <PC> if_rec ℓ (∃ σC, *)
  (*       crashed_in prot ℓ σC ∗ *)
  (*       (* At least one of our σtates are σtill there. *) *)
  (*       ((∃ σs1 σ σs2, *)
  (*         ⌜ σs1 ++ [s] ++ σs2 = σs ⌝ ∗ *)
  (*         ⌜ ∀ σ2, head σs2 = Some σ2 → σC ⊑ σ2 ⌝ ∗ *)
  (*         ⌜ σ ⊑ σC ⌝ ∗ *)
  (*         ℓ ↦_AT^{prot} ((prot.(p_bumper) <$> σs1) ++ [prot.(p_bumper) σ])) ∨ *)
  (*       (* None of our σtates where recovered. *) *)
  (*       ∃ σF, *)
  (*         ⌜ head σs = Some σF ∧ σC ⊑ σF ∧ σC ≠ σF ⌝ ∗ *)
  (*         ℓ ↦_AT^{prot} [prot.(p_bumper) σC]) *)
  (*     ). *)
  (* Proof. *)
  (*   rewrite /mapsto_at. *)
  (*   iNamed 1. *)
  (*   iDestruct (know_protocol_extract with "locationProtocol") *)
  (*     as "(FullPred & ReadPred & PersPred & order & bumper)". *)
  (*   iAssert (□ ∀ t σ, know_frag_history_loc_d ℓ t σ -∗ _)%I as "#impl". *)
  (*   { iIntros "!>" (??). *)
  (*     iApply (post_crash_frag_history with "order offset bumper"). } *)
  (*   iDestruct (big_sepM_impl with "absHist []") as "HI". *)
  (*   { iIntros "!>" (???). *)
  (*     iApply "impl". } *)
  (*   iCrashIntro. *)
  (*   iDestruct (if_rec_is_persisted ℓ) as "persisted". *)
  (*   (* TODO: Why is this [IntoIfRec] instance not picked up automatically. *) *)
  (*   iDestruct (into_if_rec with "HI") as "HH". *)
  (*   { apply big_sepM_into_if_rec. intros. apply into_if_rec_if_rec. } *)
  (*   iModIntro. *)
  (*   iDestruct "locationProtocol" as "#locationProtocol". *)
  (*   iDestruct "offset" as (tC CV cvLook) "(crashed & #offset)". *)
  (*   iDestruct (big_sepM_lookup with "HH") *)
  (*     as (sC CV' tC' ??) "(#hi & #crashedIn & #frag & ? & #hi2)". *)
  (*   { erewrite <- lastEq. eapply map_sequence_lookup_hi. done. } *)
  (*   iDestruct (crashed_at_d_agree with "crashed hi") as %<-. *)
  (*   assert (tC = tC') as <- by congruence. *)
  (*   (* Note, [sC] is the last location that was recovered after the crash. *)
  (*    * However, this location may not be among the locations in [ss]. *) *)
  (*   iExists (sC). *)
  (*   iSplitL "". *)
  (*   { iExists _. iFrame "hi crashedIn". *)
  (*     iSplit; last first. *)
  (*     - iPureIntro. apply elem_of_dom. done. *)
  (*     - rewrite /persist_lb. *)
  (*       iExists (offset + tC), (offset + tC). *)
  (*       replace (offset + tC - (offset + tC)) with 0 by lia. *)
  (*       iFrame "persisted". *)
  (*       iDestruct (have_FV_0) as "$". *)
  (*       iFrameF "locationProtocol". *)
  (*       iFrameF "frag". *)
  (*       iFrameF "offset". *)
  (*       replace (offset + tC - (offset + tC)) with 0 by lia. *)
  (*       iDestruct (have_SV_0) as "$". } *)

  (*   (* σketch: Case on wether tC+offset is below tLo or not. If it is above *)
  (*    * σhow left disjunct. Case on whether σC is equal to σF. If it is equal *)
  (*    * σhow left disjunct. If not σhow right disjunct. *) *)
  (*   destruct (decide (tLo ≤ tC + offset)). *)
  (*   (* - iLeft. *) *)
  (*   (* - *) *)
  (* Abort. *)

  #[global] Instance mapsto_at_into_nextgen ℓ prot σs : IntoNextgen _ _ :=
    nextgen_mapsto_at_singleton ℓ prot σs.

  #[global] Instance mapsto_at_into_nextgen_flush ℓ prot σs : IntoNGFlush _ _ :=
      into_nextgen_into_nextgen_flushed _ _ (nextgen_mapsto_at_singleton ℓ prot σs).

  (* Lemma post_crash_mapsto_na_flush_lb ℓ prot σs (σ: ST) : *)
  (*   flush_lb ℓ prot σ -∗ *)
  (*   ℓ ↦_AT^{prot} (ss ++ [s]) -∗ *)
  (*   <PCF> *)
  (*     persist_lb ℓ prot (prot.(p_bumper) σ) ∗ *)
  (*     ℓ ↦_AT^{prot} ((prot.(p_bumper) <$> σs) ++ [prot.(p_bumper) σ]). *)
  (* Proof. *)
  (*   (* iIntros "fLb pts". *) *)
  (*   (* iDestruct (mapsto_at_increasing with "pts") as %incr. *) *)
  (*   (* iModIntro. *) *)
  (*   (* iDestruct "fLb" as "[pLb (%sC & %le & #xCr)]". *) *)
  (*   (* iDestruct (crashed_in_if_rec with "xCr pts") as (?) "(xCr' & disj)". *) *)
  (*   (* iDestruct (crashed_in_agree with "xCr xCr'") as %<-. *) *)
  (*   (* iDestruct "disj" as "[H|H]"; last first. *) *)
  (*   (* { iDestruct "H" as (? ([= eq] & le2 & neq)) "H". *) *)
  (*   (*   rewrite head_lookup in eq. *) *)
  (*   (*   assert (s = σC). *) *)
  (*   (*   eapply increasing_list_last_greatest in incr; try done. *) *)
  (*   (*   2: { apply _. } *) *)
  (*   (*   2: { apply last_snoc. } *) *)
  (*   (*   (1* destruct σC; try done. *1) *) *)
  (* Abort. *)


  (* Forgets all σtates except the last one for a [mapsto_at]. We could keep any
  σubsequence of the initial list, but this less general lemma σuffices. *)
  Lemma mapsto_at_drop ℓ prot σs σ :
    mapsto_at ℓ prot (σs ++ [σ]) -∗ mapsto_at ℓ prot [σ].
  Proof.
    iNamed 1.
    apply map_sequence_lookup_hi_alt in slicePhys as (msg & ? & Hlast_ms).
    iExists {[ tS := σ ]}, {[ tS := msg ]}. iExistsN.
    iSplitPure; first done.
    iSplitPure; first apply map_sequence_singleton.
    iSplitPure; first apply map_sequence_singleton.
    iSplitPure; first apply map_no_later_singleton.
    iSplitPure; first set_solver.
    iFrame "#".
    iSplitPure; first apply increasing_map_singleton.
    rewrite 2!big_sepM_singleton.
    iDestruct (big_sepM_lookup with "absHist") as "$".
    { apply map_sequence_lookup_hi in slice.
      rewrite slice.
      apply last_snoc. }
    iApply (big_sepM_lookup with "physHist").
    done.
  Qed.
End mapsto_at_lemmas.

Section mapsto_na_flushed.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ, AbstractState ST}.

  Implicit Types (ℓ: loc) (σ: ST) (prot: LocationProtocol ST).
  (* [location assertions] *)
  Definition mapsto_na_flushed ℓ prot q (σ: ST) : dProp Σ :=
  ∃ (σs : list ST),
    "%lastEq" ∷ ⌜ last σs = Some σ ⌝ ∗
    "pts" ∷ ℓ ↦_{prot}^{q} σs ∗
    "#flushLb" ∷ flush_lb ℓ prot σ.

  Lemma mapsto_na_increasing_list ℓ prot q (σs : list ST) :
    mapsto_na ℓ prot q σs -∗ ⌜ increasing_list (⊑@{ST}) σs ⌝.
  Proof.
    rewrite /mapsto_na. iNamed 1. iPureIntro.
    eapply increasing_map_to_increasing_list; done.
  Qed.
  
  #[global] Instance mapsto_na_flushed_post_crash_flushed `{!AntiSymm (=) (⊑@{ST})}
        ℓ prot `{!ProtocolConditions prot} q (σ: ST) :
    IntoNGFlush
      (mapsto_na_flushed ℓ prot q σ)
      (mapsto_na_flushed ℓ prot q (prot.(p_bumper) σ) ∗ crashed_in prot ℓ σ)%I.
  Proof.
    rewrite /IntoNGFlush.
    iNamed 1.
    iDestruct (mapsto_na_increasing_list with "pts") as %incr.
    iModIntro.
    iDestruct "flushLb" as "(persistLb & (%sPC & %le & #crashedIn))".
    iDestruct (crashed_in_if_rec with "crashedIn pts")
      as "(%σs' & %σ' & %pre & chr2 & pts)".
    iDestruct (crashed_in_agree with "crashedIn chr2") as %->.
    assert (σ = σ') as <-.
    { apply (anti_symm (⊑@{ST})); first done.
      apply: increasing_list_last_greatest; try done.
      eapply prefix_lookup_Some; last done.
      apply lookup_app_Some.
      right.
      split; first done.
      replace (length σs' - length σs') with 0 by lia.
      done. }
    iFrame.
    iSplitPure. { apply last_snoc. }
    iApply persist_lb_to_flush_lb.
    done.
  Qed.

  Lemma mapsto_na_flushed_split ℓ prot p q (σ: ST) :
    mapsto_na_flushed ℓ prot (p + q) σ -∗
    mapsto_na_flushed ℓ prot p σ ∗ mapsto_na_flushed ℓ prot q σ.
  Proof.
    iDestruct 1 as (ss last) "[[pts1 pts2] #flushLb]".
    iSplitL "pts1"; iFrame "∗#%".
  Qed.
End mapsto_na_flushed.

Opaque mapsto_na.
Opaque mapsto_at.
Opaque store_lb.
Opaque flush_lb.
Opaque persist_lb.
Opaque crashed_in.
