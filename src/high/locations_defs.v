From iris_named_props Require Import named_props.
From iris.proofmode Require Import proofmode.

From self Require Import solve_view_le.
From self.lang Require Import lang.
From self.high Require Import generational_resources dprop protocol_defs.
From self.high.modalities Require Import no_buffer no_flush.
From self.high.lib Require Import abstract_state increasing_map.

Section location_assertions.
  Context `{nvmHighGS, AbstractState ST}.

  Implicit Types (ℓ : loc) (σ : ST) (σs : list ST) (prot : LocationProtocol ST).
  (*** mapsto predicates *)
  (* Points-to predicate for non-atomics. This predcate says that we know that
     the last events at [ℓ] corresponds to the last element in list [σs] *)
  (* FIXME: Can [mapsto_na] use [lb_base]? *)
  Definition mapsto_na (ℓ : loc) prot (q : frac) (σs : list ST) : dProp Σ :=
    (∃ (tLo tHi offset : time) SV (abs_hist : gmap time ST) (msg : message) σ,
      "%lastEq" ∷ ⌜ list.last σs = Some σ ⌝ ∗
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

  Program Definition have_msg_post_fence msg : dProp Σ :=
    MonPred (λ TV,
      ⌜ msg.(msg_store_view) ⊑ (store_view TV) ⌝
      ∗
      ⌜ msg.(msg_persisted_after_view) ⊑ (flush_view TV ⊔ buffer_view TV) ⌝
    )%I _.
  Next Obligation. solve_proper. Qed.

  Program Definition have_msg_store_view msg : dProp Σ :=
    MonPred (λ TV,
      ⌜ msg.(msg_store_view) ⊑ (store_view TV) ⌝
      (* ∗ *)
      (* ⌜ msg.(msg_persisted_after_view) ⊑ (flush_view i.1 ⊔ buffer_view i.1) ⌝ *)
    )%I _.
  Next Obligation. solve_proper. Qed.

  (** The following lemmas/instances cannot infer [Σ] when proved in a different context.
   ** They are otherwise not used as definitions. *)
  (* This is a revived [have_msg_after_fence] before the commit 96f65f5.
   * We (maybe?) need this stronger version in order to extract resource
   * from [p_read] into thread local view. *)
  Lemma have_msg_post_fence_empty v PV : ⊢ have_msg_post_fence (Msg v ∅ PV ∅).
  Proof.
    iModel. simpl. iPureIntro. split; apply view_empty_least.
  Qed.

  (* and for the original assertion, I'm changing its name to be more explicit. *)
  #[global] Instance have_msg_post_fence_persistent msg :
    Persistent (have_msg_post_fence msg).
  Proof. apply monPred_persistent=> j. apply _. Qed.

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
        "%lastEq" ∷ ⌜ list.last ss = Some s ⌝ ∗ (* NOTE: Could we change this to non-empty? *)
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

  (*** Lower-bound assertions *)
  Definition lb_base ℓ prot offset tS (s : ST) : dProp Σ :=
    "#locationProtocol" ∷ ⎡ know_protocol ℓ prot ⎤ ∗
    "#knowFragHist" ∷ ⎡ know_frag_history_loc ℓ tS s ⎤ ∗
    "#offset" ∷ ⎡ offset_loc ℓ offset ⎤ ∗
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
      "#viewFact" ∷ (have_FV_strong ℓ (tF - offset) ∨
                    ⎡ persisted_loc ℓ (tF - offset) ⎤).

  Definition persist_lb ℓ prot (sP : ST) : dProp Σ :=
    ∃ tP offset,
      "#lbBase" ∷ lb_base ℓ prot offset tP sP ∗
      (* We have the persisted state in our store view. *)
      "#tPLe" ∷ have_FV ℓ (tP - offset) ∗
      "persisted" ∷ ⎡ persisted_loc ℓ (tP - offset) ⎤.

  Program Definition seen_view msg : dProp Σ :=
    MonPred (λ TV,
      ⌜ msg.(msg_store_view) ⊑ (store_view TV) ⌝
      ∗
      ⌜ msg.(msg_persisted_after_view) ⊑ (flush_view TV) ⌝
    )%I _.
  Next Obligation. solve_proper. Qed.

  Definition seen_state ℓ (s : ST) : dProp Σ :=
    ∃ (t offset : nat) (msg: message),
      "#knowFragHist" ∷ ⎡ know_frag_history_loc ℓ t s ⎤ ∗
      "#offset" ∷ ⎡ offset_loc ℓ offset ⎤ ∗
      "#tSLe" ∷ have_SV ℓ (t - offset) ∗
      "#knowPhysMsg" ∷ ⎡ know_phys_hist_msg ℓ t msg ⎤ ∗
      "#seenView" ∷ seen_view msg.

  Definition seen_state_post_fence ℓ (s : ST) : dProp Σ :=
    ∃ (t offset : nat) (msg: message),
      "#knowFragHist" ∷ ⎡ know_frag_history_loc ℓ t s ⎤ ∗
      "#offset" ∷ ⎡ offset_loc ℓ offset ⎤ ∗
      "#tSLe" ∷ have_SV ℓ (t - offset) ∗
      "#knowPhysMsg" ∷ ⎡ know_phys_hist_msg ℓ t msg ⎤ ∗
      "#haveMsg" ∷ have_msg_post_fence msg.

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
    iSplit; iPureIntro; first done.
    solve_view_le.
  Qed.

  (*** Crash assertions. *)
  Definition crashed_in prot ℓ σ : dProp Σ :=
    "#persistLb" ∷ persist_lb ℓ prot (prot.(p_bumper) σ) ∗
    "#crashedIn" ∷ ⎡ crashed_in_loc ℓ σ ⎤.

  (* [ℓ] was not recovered at the last crash. *)
  Definition lost ℓ : dProp Σ :=
    ∃ OCV,
      "#crashed" ∷ ⎡ crashed_at_offset OCV ⎤ ∗
      "%notInCV" ∷ ⌜ℓ ∉ dom OCV⌝.

  (*** Combo assertions. *)
  #[local] Notation "l ↦_{ prot }^{ q } ss" := (mapsto_na l prot q ss) (at level 20).
  Definition mapsto_na_flushed ℓ prot q (σ: ST) : dProp Σ :=
  ∃ (σs : list ST),
    "%lastEq" ∷ ⌜ list.last σs = Some σ ⌝ ∗
    "pts" ∷ ℓ ↦_{prot}^{q} σs ∗
    "#flushLb" ∷ flush_lb ℓ prot σ.
End location_assertions.

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
