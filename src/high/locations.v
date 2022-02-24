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
From self.lang Require Import lang.
From self.base Require Import primitive_laws.
From self.high Require Import dprop abstract_state lifted_modalities or_lost.
From self.high Require Export abstract_state resources protocol modalities post_crash_modality.
From self.high.resources Require Export bumpers preorders auth_map_map abstract_history.
From self.high.modalities Require Export no_buffer.

Definition increasing_list `{SqSubsetEq ST} (ss : list ST) :=
  ∀ i j s s', i < j → (ss !! i = Some s) → (ss !! j = Some s') → s ⊑ s'.

Section increasing_list.
  Context `{SqSubsetEq ST, !PreOrder (⊑@{ST})}.
  Implicit Types (s : ST).

  Lemma increasing_list_singleton s : increasing_list [s].
  Proof. intros [|][|]?????; try naive_solver. Qed.

  Lemma lookup_snoc_Some {A} (l : list A) x x2 i :
    (l ++ [x]) !! i = Some x2 →
    (l !! i = Some x2) ∨ (length l = i ∧ x = x2).
  Proof.
    intros [look|[? [??]%list_lookup_singleton_Some]]%lookup_app_Some.
    - left. apply look.
    - right. auto with lia.
  Qed.

  Lemma increasing_list_last_greatest ss s i s' :
    increasing_list ss →
    last ss = Some s →
    ss !! i = Some s' →
    s' ⊑ s.
  Proof.
    rewrite last_lookup.
    rewrite /increasing_list.
    intros incr lookLast look.
    destruct (decide (i = pred (length ss))).
    { simplify_eq. reflexivity. }
    eapply incr; try done.
    apply lookup_lt_Some in look.
    lia.
  Qed.

  Lemma increasing_list_snoc xs xs__last (x : ST) :
    (last xs) = Some xs__last →
    xs__last ⊑ x →
    increasing_list xs → increasing_list (xs ++ [x]).
  Proof.
    intros last incl incr.
    intros ?????.
    intros [?|[??]]%lookup_snoc_Some; intros [look|[??]]%lookup_snoc_Some.
    * eapply incr; done.
    * simplify_eq.
      etrans; last apply incl.
      eapply increasing_list_last_greatest; done.
    * apply lookup_lt_Some in look. lia.
    * lia.
  Qed.

End increasing_list.

Section points_to_at.
  Context `{nvmFixedG Σ, hGD : nvmDeltaG Σ, AbstractState ST}.

  Implicit Types (ℓ : loc) (s : ST) (ss : list ST) (prot : LocationProtocol ST).

  (* Definition abs_hist_to_ra_old *)
  (*         (abs_hist : gmap time (message * positive)) : encoded_abs_historyR := *)
  (*   (to_agree ∘ snd) <$> abs_hist. *)

  Lemma singleton_included_l' `{Countable K, CmraTotal A}
        (m : gmap K A) (i : K) x :
    {[i := x]} ≼ m ↔ (∃ y : A, m !! i ≡ Some y ∧ x ≼ y).
  Proof.
    setoid_rewrite <-(Some_included_total x).
    apply singleton_included_l.
  Qed.

  (* Points-to predicate for non-atomics. This predcate says that we know that
the last events at [ℓ] corresponds to the *)
  Program Definition mapsto_na (ℓ : loc) prot (* (per : bool) *) (q : frac) (ss : list ST) : dProp Σ :=
    (∃ (tP tStore : time) SV (abs_hist : gmap time ST) (msg : message) s,
      "%lastEq" ∷ ⌜ last ss = Some s ⌝ ∗
      "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
      (* NOTE: Maybe we can actually remove [increasing_list]? It should be
      covered by the fact that the list corresponds to [abs_hist] and that one
      is sorted. *)
      "%incrList" ∷ ⌜ increasing_list ss ⌝ ∗
      "#isNaLoc" ∷ ⎡ is_na_loc ℓ ⎤ ∗

      (* [tStore] is the last message and it agrees with the last state in ss. *)
      "%lookupV" ∷ ⌜ abs_hist !! tStore = Some s ⌝ ∗
      "%nolater" ∷ ⌜ map_no_later abs_hist tStore ⌝ ∗

      (* Ownership over the full abstract history. *)
      "hist" ∷ ⎡ know_full_history_loc ℓ q abs_hist ⎤ ∗
      "#histFrag" ∷ ⎡ know_frag_history_loc ℓ tStore s ⎤ ∗

      "knowSV" ∷ ⎡ know_na_view ℓ q SV ⎤ ∗
      "%slice" ∷ ⌜ map_slice abs_hist tP tStore ss ⌝ ∗
      "#physMsg" ∷ ⎡ auth_map_map_frag_singleton know_phys_history_name ℓ tStore msg ⎤ ∗
      (* "%msgViewIncluded" ∷ ⌜ msg_store_view msg ⊑ SV ⌝ ∗ *)
      "#inThreadView" ∷ monPred_in (SV, msg_persisted_after_view msg, ∅) ∗
      (* We have the [tStore] timestamp in our store view. *)
      "%haveTStore" ∷ ⌜ tStore ≤ SV !!0 ℓ ⌝ ∗
      (* "haveTStore" ∷ monPred_in ({[ ℓ := MaxNat tStore ]}, ∅, ∅) ∗ *)

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

  Program Definition have_SV ℓ t : dProp Σ :=
    MonPred (λ TV, ⌜ t ≤ (store_view TV) !!0 ℓ ⌝)%I _.
  Next Obligation. solve_proper. Qed.

  Global Instance have_SV_persistent ℓ t : Persistent (have_SV ℓ t).
  Proof. apply monPred_persistent=> j. apply _. Qed.

  Program Definition have_FV ℓ t : dProp Σ :=
    MonPred (λ TV, ⌜ t ≤ (flush_view TV) !!0 ℓ ⌝)%I _.
  Next Obligation. solve_proper. Qed.

  Global Instance have_FV_persistent ℓ t : Persistent (have_FV ℓ t).
  Proof. apply monPred_persistent=> j. apply _. Qed.

  Lemma have_SV_0 ℓ : ⊢ have_SV ℓ 0.
  Proof. iModel. iPureIntro. lia. Qed.

  Lemma have_FV_0 ℓ : ⊢ have_FV ℓ 0.
  Proof. iModel. iPureIntro. lia. Qed.

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
      (* Either the location is persisted or we have something in the flush
      view. The later case is for use after a crash where we don't have
      anything in the flush view. *)
      "viewFact" ∷ (have_FV ℓ tF ∨ (⌜tF = 0⌝ ∗ ⎡ persisted_loc ℓ 0 ⎤))%I.

  Program Definition persist_lb ℓ prot (sP : ST) : dProp Σ :=
    ∃ tP,
      "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
      "knowFragHist" ∷ ⎡ know_frag_history_loc ℓ tP sP ⎤ ∗
      (* We have the persisted state in our store view. *)
      "#tSLe" ∷ have_SV ℓ tP ∗
      "#tPLe" ∷ have_FV ℓ tP ∗
      "persisted" ∷ ⎡ persisted_loc ℓ tP ⎤.

  (* The location [ℓ] was recovered in the abstract state [s]. *)
  Definition recovered_at ℓ s : dProp Σ :=
    ∃ CV,
      "#knowFragHist" ∷ ⎡ know_frag_history_loc ℓ 0 s ⎤ ∗
      "#crashed" ∷ ⎡ crashed_at CV⎤ ∗
      "%inCV" ∷ ⌜ℓ ∈ dom (gset _) CV⌝.

  (* [ℓ] was recovered at the last crash. *)
  Definition recovered ℓ : dProp Σ := ∃ s, recovered_at ℓ s.

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

  (* A few utility lemmas. *)
  Lemma recovered_at_not_lot ℓ s : recovered_at ℓ s -∗ lost ℓ -∗ False.
  Proof.
    iNamed 1. iIntros "(%CV' & crashed' & %notInCV)".
    iDestruct (crashed_at_agree with "[$] [$]") as %->.
    set_solver.
  Qed.

  Lemma recovered_at_agree ℓ s s' :
    recovered_at ℓ s -∗ recovered_at ℓ s' -∗ ⌜ s = s' ⌝.
  Proof.
    iNamed 1. iIntros "(%CV' & hist & crashed' & pizz)".
    iDestruct (own_frag_history_singleton_agreee with "[$] [$]") as %->.
    done.
  Qed.

  Lemma monPred_in_have_SV SV PV BV ℓ t :
    t ≤ SV !!0 ℓ →
    monPred_in (SV, PV, BV) -∗
    have_SV ℓ t.
  Proof.
    intros le.
    iStartProof (iProp _). iPureIntro. intros [[SV' ?] ?] [[incl ?]?].
    etrans; first done. f_equiv. done.
  Qed.

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
    apply map_slice_lookup_hi_alt in slice.
    naive_solver.
  Qed.

  Lemma mapsto_na_store_lb_incl ℓ prot q ss s1 s2 :
    last ss = Some s1 →
    store_lb ℓ prot s2 -∗
    mapsto_na ℓ prot q ss -∗
    ⌜s2 ⊑ s1⌝.
  Proof. Admitted.

  Lemma mapsto_na_flush_lb_incl ℓ prot q ss s1 s2 :
    last ss = Some s1 →
    flush_lb ℓ prot s2 -∗
    mapsto_na ℓ prot q ss -∗
    ⌜s2 ⊑ s1⌝.
  Proof.
    iIntros (lastSome) "flushLb".
    iNamed 1.
    iDestruct "flushLb" as (t) "(_ & B & C & D)".
  Admitted.

  (* Instances. *)

  Lemma no_buffer_flush_lb ℓ prot (s : ST) :
    flush_lb ℓ prot s -∗ <nobuf> flush_lb ℓ prot s.
  Proof.
    rewrite /flush_lb.
    iModel.
    simpl.
    iDestruct 1 as (?) "HI". iExists _. iFrame.
  Qed.

  Global Instance buffer_free_flush_lb ℓ prot (s : ST) :
    BufferFree (flush_lb ℓ prot s).
  Proof. rewrite /IntoNoBuffer. eauto using no_buffer_flush_lb. Qed.

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

  Lemma post_crash_persist_lb (ℓ : loc) prot (s : ST) :
    persist_lb ℓ prot s -∗
    post_crash (λ hG, ∃ s', ⌜s ⊑ s'⌝ ∗
      persist_lb ℓ prot (prot.(bumper) s') ∗
      recovered_at ℓ (prot.(bumper) s')).
  Proof.
    iNamed 1.
    rewrite /know_protocol. rewrite 2!embed_sep.
    iDestruct "locationProtocol" as "(-#pred & -#order & -#bumper)".
    iDestruct (post_crash_frag_history with "[$order $bumper $knowFragHist]") as "H".
    iCrash.

    (* rewrite embed_sep. *)
    iDestruct "persisted" as "(persisted & (% & % & [% %] & #crashed))".
    iDestruct (or_lost_with_t_get with "[$] H") as "(% & % & order & bumper & hist)";
      first done.
    iDestruct (or_lost_get with "[$] pred") as "pred"; first done.
    iExists s'.
    iSplitPure; first intuition.
    iSplit.
    { iExists 0.
      iFrame "∗#".
      iDestruct (have_SV_0) as "$".
      iDestruct (have_FV_0) as "$". }
    rewrite /recovered_at.
    iExists _. iFrame "#∗". iPureIntro. apply elem_of_dom. done.
  Qed.

  Global Instance persist_lb_into_crash ℓ prot s : IntoCrash _ _ :=
    post_crash_persist_lb ℓ prot s.

  Lemma post_crash_flush_lb (ℓ : loc) prot (s : ST) :
    flush_lb ℓ prot s -∗
    post_crash (λ hG,
                  or_lost ℓ (∃ (s' : ST), persist_lb ℓ prot s')).
  Proof.
    iNamed 1.
    rewrite /know_protocol. rewrite 2!embed_sep.
    iDestruct "locationProtocol" as "(-#pred & -#order & -#bumper)".
    (* iNamed "locationProtocol". *)
    iDestruct (post_crash_frag_history with "[$order $bumper $knowFragHist]") as "H".
    iCrash.
    iCombine "pred H" as "H".
    rewrite !or_lost_with_t_sep.
    iApply (or_lost_with_t_mono_strong with "[] H").
    iIntros (??). iNamed 1. iIntros "(pred & (% & _ & order & bump & hist))".
    iExists (bumper prot s').
    rewrite /persist_lb.
    iExists 0.
    rewrite /know_protocol. iEval (rewrite 2!embed_sep).
    iFrame "∗#".
    iDestruct (have_SV_0) as "$".
    iDestruct (have_FV_0) as "$".
  Qed.

  Global Instance flush_lb_into_crash ℓ prot s : IntoCrash _ _ :=
    post_crash_flush_lb ℓ prot s.

  Lemma post_crash_store_lb (ℓ : loc) prot (s : ST) :
    store_lb ℓ prot s -∗
    post_crash (λ hG, or_lost ℓ (∃ (s' : ST),
      persist_lb ℓ prot s')).
  Proof.
    iNamed 1.
    rewrite /know_protocol. rewrite 2!embed_sep.
    iDestruct "locationProtocol" as "(-#pred & -#order & -#bumper)".
    (* iNamed "locationProtocol". *)
    iDestruct (post_crash_frag_history with "[$order $bumper $knowFragHist]") as "H".
    iCrash.
    iCombine "pred H" as "H".
    rewrite !or_lost_with_t_sep.
    iApply (or_lost_with_t_mono_strong with "[] H").
    iIntros (??). iNamed 1. iIntros "(pred & (% & H & order & bump & hist))".
    iExists (bumper prot s').
    rewrite /persist_lb.
    iExists 0.
    rewrite /know_protocol. iEval (rewrite 2!embed_sep).
    iFrame "∗#".
    iDestruct (have_SV_0) as "$".
    iDestruct (have_FV_0) as "$".
  Qed.

  Global Instance store_lb_into_crash ℓ prot s : IntoCrash _ _ :=
    post_crash_store_lb ℓ prot s.

  (* NOTE: This rule should be changed once the "bump-back function" is
  introduced. *)
  (* Lemma post_crash_mapsto_persisted_ex ℓ prot q (ss : list ST) : *)
  (*   ℓ ↦_{prot}^{q} ss -∗ <PC> hG', ∃ s, ⌜s ∈ ss⌝ ∗ ℓ ↦_{prot}^{q} [s] ∗ recovered_at ℓ s. *)
  (* Proof. *)
  (*   rewrite /mapsto_na. iNamed 1. *)
  (*   iDestruct "isNaLoc" as "-#isNaLoc". *)
    (* iDestruct "order" as "-#order". *)
    (* iCrash. *)
    (* iDestruct "pers" as "(persisted & (%CV & % & [% %] & #crash))". *)
    (* iDestruct (or_lost_get with "crash isNaLoc") as "isNaLoc"; first done. *)
    (* iDestruct (or_lost_get with "crash order") as "order"; first done. *)
    (* iDestruct (or_lost_get with "crash knowSV") as "knowSV"; first done. *)
    (* iDestruct (or_lost_with_t_get with "crash hist") as (s) "(% & ? & ? & _)"; *)
    (*   first done. *)
    (* iExists s. *)
    (* iPureGoal. { by eapply map_slice_no_later_elem_of. } *)
    (* iSplit. *)
    (* - iExists 0, 0, ∅, _, (Msg _ ∅ ∅ ∅). iFrame. *)
    (*   iPureGoal. { apply increasing_list_singleton. } *)
    (*   iPureGoal. { by rewrite lookup_singleton. } *)
    (*   iPureGoal. { apply map_no_later_singleton. } *)
    (*   iPureGoal. { simpl. by rewrite lookup_singleton. } *)
    (*   iSplit. { admit. } (* FIXME: We'd need to add some post crash rule for this. *) *)
    (*   iStopProof. *)
    (*   iStartProof (iProp _). iIntros (?) "_ !%". *)
    (*   split_and!; try done. *)
    (*   destruct i as [[??]?]; repeat split; apply view_empty_least. *)
    (* - iExists _. iFrame "∗#". iPureIntro. apply elem_of_dom. naive_solver. *)
  (* Admitted. *)

  Lemma monPred_in_bottom : ⊢@{dPropI Σ} monPred_in (∅, ∅, ∅).
  Proof.
    iStartProof (iProp _). iPureIntro.
    intros [[??]?].
    repeat split; apply view_empty_least.
  Qed.

  Lemma post_crash_mapsto_na ℓ prot q (ss : list ST) :
    ℓ ↦_{prot}^{q} ss -∗
    post_crash (λ hG', or_lost ℓ (∃ s, ⌜s ∈ ss⌝ ∗ ℓ ↦_{prot}^{q} [bumper prot s] ∗
                                  recovered_at ℓ (bumper prot s))).
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
    iCombine "knowSV pred order isNaLoc H physMsg" as "H".
    rewrite /or_lost. rewrite !or_lost_with_t_sep.
    iApply (or_lost_with_t_mono_strong with "[] H").
    iIntros (??). iNamed 1.
    iIntros "(A & B & C & D & E & F)".
    iDestruct "E" as (sNew ?) "(bump & fullHist & fragHist)".
    iExists (sNew).

    iAssert (⌜ tP ≤ t ⌝)%I as %?.
    { iDestruct "pers" as "[(_ & (%CV' & % & [% %] & crashed'))|->]";
        last (iPureIntro; lia).
      iDestruct (crashed_at_agree with "crashed crashed'") as %<-.
      iPureIntro.
      assert (t = t'); last lia.
      congruence. }
    iSplit.
    { iPureIntro. apply: map_slice_lookup_between; try done.
      split; first done.
      eapply map_no_later_Some; naive_solver. }
    iDestruct "F" as (v) "hist".

    rewrite /recovered_at.
    iSplit.
    + iExists 0, 0, ∅, _, (Msg _ ∅ ∅ ∅), _. iFrame. iFrame "#".
      iPureGoal. { done. }
      iPureGoal. { apply increasing_list_singleton. }
      iPureGoal. { by rewrite lookup_singleton. }
      iPureGoal. { apply map_no_later_singleton. }
      iPureGoal. { by rewrite lookup_singleton. }
      iSplit. { simpl. iApply monPred_in_bottom. }
      done.
    + iExists _. iFrame "∗#".
      iPureIntro. rewrite elem_of_dom. naive_solver.
  Qed.

  Global Instance mapsto_na_into_crash ℓ prot q (ss : list ST) :
    IntoCrash
      (ℓ ↦_{prot}^{q} ss)%I
      (λ hG', or_lost ℓ (∃ s, ⌜s ∈ ss⌝ ∗ ℓ ↦_{prot}^{q} [bumper prot s] ∗
                              recovered_at ℓ (bumper prot s)))%I.
  Proof. rewrite /IntoCrash. iIntros "P". by iApply post_crash_mapsto_na. Qed.

  Global Instance mapsto_na_into_crash_flush ℓ prot q (ss : list ST) :
    IntoCrashFlush _ _ :=
    (into_crash_into_crash_flushed _ _ (post_crash_mapsto_na ℓ prot q ss)).

  Lemma post_crash_flush_flush_lb (ℓ : loc) prot (s : ST) :
    flush_lb ℓ prot s -∗
    <PCF> hG, ∃ s__pc, ⌜s ⊑ s__pc⌝ ∗
      recovered_at ℓ s__pc ∗ persist_lb ℓ prot s__pc.
  Proof.
    iStartProof (iProp _).
    iIntros (TV).
    rewrite /flush_lb.
    simpl.
    iNamed 1.
    iIntros (???).
    (*
    iDestruct (post_crash_modality.post_crash_nodep with "order") as "order".
    iDestruct (post_crash_modality.post_crash_nodep with "knowFragHist") as "knowFragHist".
    iDestruct "viewFact" as "[[%neq %leq] | [%eq pers]]".
    * base.post_crash_modality.iCrash.
      iNamed 1.
      rewrite /post_crash_resource.
      iFrameNamed.
      iDestruct ("post_crash_history_impl" with "knowFragHist") as "knowFragHist".
      iDestruct ("post_crash_preorder_impl" with "order") as "order'".
      iIntros (CV).
      iIntros (??) "(% & #pers & #crash)".
      simpl.
      destruct (flush_view TV !! ℓ) as [[tF']|] eqn:eq; last first.
      { exfalso.
        rewrite /lookup_zero in leq.
        rewrite eq in leq.
        simpl in leq.
        lia. }
      edestruct view_le_look as (t'' & lookCV & lt); [apply eq|eassumption |].
      iDestruct (or_lost_post_crash_lookup CV with "crash order'") as "#order";
        first apply lookCV.
      iDestruct (or_lost_post_crash_lookup CV with "crash knowFragHist")
        as "(%s'' & %imp & knowFragHist)";
        first apply lookCV.
      assert (s ⊑ s'') as sInclS''.
      { etrans; first done. apply imp.
        etrans; first done.
        rewrite /lookup_zero.
        rewrite eq.
        simpl. done. }
      iAssert (persisted_loc ℓ 0) as "persisted".
      { iApply (persisted_persisted_loc with "pers").
        rewrite /view_to_zero.
        rewrite lookup_fmap.
        rewrite eq.
        done. }
      iExists s''.
      iSplit. { done. }
      iSplit. { iExists CV. iFrame "crash knowFragHist". iPureIntro.
                apply elem_of_dom. done. }
      iSplit. { iExists 0. iFrameNamed. iPureIntro. lia. }
      iSplit.
      { iExists 0.
        iFrameNamed.
        iRight. by iFrame "#". }
      iExists 0.
      iFrameNamed.
      iPureIntro. apply lookup_zero_gt_zero.
    * base.post_crash_modality.iCrash.
      iNamed 1.
      rewrite /post_crash_resource.
      iFrameNamed.
      iDestruct ("post_crash_frag_history_impl" with "knowFragHist") as "knowFragHist".
      iDestruct ("post_crash_preorder_impl" with "order") as "order'".
      iIntros (CV).
      iIntros (??) "(% & #pers' & #crash)".
      simpl.
      iDestruct "pers" as "[#persisted (%CV' & %t & [%lookCV _] & crash')]".
      iDestruct (crashed_at_agree with "crash crash'") as %<-.
      iClear "crash'".
      iDestruct (or_lost_post_crash_lookup CV with "crash order'") as "#order";
        first apply lookCV.
      iDestruct (or_lost_post_crash_lookup CV with "crash knowFragHist")
        as "(%s'' & %imp & knowFragHist)";
        first apply lookCV.
      assert (s ⊑ s'') as sInclS''.
      { etrans; first done. apply imp.
        etrans; first done.
        rewrite /lookup_zero.
        rewrite eq.
        lia. }
      iExists s''.
      iSplit. { done. }
      iSplit. { iExists CV. iFrame "crash knowFragHist". iPureIntro.
                apply elem_of_dom. done. }
      iSplit.
      { iExists 0. iFrameNamed. iPureIntro. lia. }
      iSplit.
      { iExists 0. iFrameNamed. iRight. by iFrame "#". }
      iExists 0. iFrameNamed. iPureIntro. lia.
     *)
  Admitted.

  Global Instance know_flush_into_crash ℓ prot (s : ST) :
    IntoCrashFlush (flush_lb ℓ prot s) (λ _, ∃ s__pc, ⌜ s ⊑ s__pc ⌝ ∗
      recovered_at ℓ s__pc ∗ persist_lb ℓ prot s__pc)%I.
  Proof.
    rewrite /IntoCrashFlush. iIntros "P".
    by iApply post_crash_flush_flush_lb.
  Qed.
  (* Global Instance mapsto_na_persisted_into_crash `{AbstractState ST} ℓ (ss : list ST) : *)
  (*   IntoCrash (ℓ ↦_{true} ss)%I (λ hG', ∃ s, ⌜s ∈ ss⌝ ∗ ℓ ↦_{true} [s] ∗ recovered_at ℓ s)%I. *)
  (* Proof. *)
  (*   rewrite /IntoCrash. iIntros "P". by iApply post_crash_mapsto_persisted_ex. *)
  (* Qed. *)

  Lemma recovered_at_or_lost `{AbstractState ST} ℓ P (s : ST) :
    recovered_at ℓ s -∗ or_lost ℓ P -∗ P.
  Proof.
    iNamed 1. iIntros "P".
    iApply (or_lost_get with "crashed P").
    apply elem_of_dom.
    done.
  Qed.

End points_to_at_more.

Typeclasses Opaque mapsto_na.
Typeclasses Opaque store_lb.
Typeclasses Opaque flush_lb.
Typeclasses Opaque persist_lb.
