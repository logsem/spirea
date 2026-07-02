From iris.proofmode Require Import proofmode.
From iris_named_props Require Import named_props.

From iris.algebra Require Import auth gset.
From self Require Import extra view_slice.
From self.high.lib Require Import increasing_map.

From self.nextgen Require Import nextgen_promises.
From self.base Require Import primitive_laws generational_resources.
From self.high Require Export dprop predicates generational_resources protocol.
From self.high.resources Require Import
  gen_ghost_map gen_ghost_map_map gen_alocs gen_predicates auth_map_map.
From self.high.modalities Require Import nextgen_flush.
From self.lang Require Import lang.

Set Default Proof Using "Type".

(* Convert a message to a thread_view corresponding to what is stored in the
message. *)
Definition msg_to_tv (m : message) : thread_view :=
  (* NOTE: We use the [msg_persisted_after_view] and _not_ the
  [msg_persist_view]. This is because the [msg_persisted_after] can be
  transfered to the recovery program after a crash and the predicate then
  still holds. *)
  (m.(msg_store_view), m.(msg_persisted_after_view), ∅).

Definition map_map_Forall `{Countable K1, Countable K2} {A : Type}
            (P : K1 → K2 → A → Prop) (m : gmap K1 (gmap K2 A)):=
  map_Forall (λ k1, map_Forall (λ k2 x, P k1 k2 x)) m.

Section map_map_Forall.
  Context `{Countable K1, Countable K2} {A : Type}.

  Implicit Types (m : gmap K1 (gmap K2 A)) (P : K1 → K2 → A → Prop).

  Lemma map_map_Forall_lookup_1 P m n i j x :
    map_map_Forall P m → m !! i = Some n → n !! j = Some x → P i j x.
  Proof.
    intros map ??.
    eapply map_Forall_lookup_1 in map; last done.
    eapply map_Forall_lookup_1 in map; done.
  Qed.

  Lemma map_map_Forall_insert_2 P m n k1 k2 a :
    m !! k1 = Some n →
    P k1 k2 a →
    map_map_Forall P m →
    map_map_Forall P (<[k1:=<[k2:=a]>n]>m).
  Proof.
    intros look HP map.
    apply map_Forall_insert_2; last done.
    apply map_Forall_insert_2; first done.
    apply map. done.
  Qed.

End map_map_Forall.

(* A property that holds for all messages for atomic locations. *)
Definition atomic_loc_inv (ℓ : loc) (t : time) (msg : message) :=
  (* The store view includes the message itself. *)
  msg.(msg_store_view) !!0 ℓ = t ∧
  (* For shared locations the two persist views are equal. This enforces
  that shared locations can only be written to using release store and
  RMW operations. *)
  msg.(msg_persist_view) = msg.(msg_persisted_after_view).

Definition shared_locs_inv (locs : gmap loc (gmap time message)) :=
  map_map_Forall atomic_loc_inv locs.

(* make it easier to replace this assertion in nextgen proof *)

Definition encoded_full_read_predicates_hold `{nvmHighGS} ℓ (abs_hist: gmap time positive) (phys_hist: gmap time message) (na_views: gmap loc view) (offsets: gmap loc nat) (predicates_full predicates_read: gmap loc enc_predicate) : iProp Σ :=
  ∃ encp_full encp_read offset,
    ⌜predicates_full !! ℓ = Some encp_full ⌝ ∗
    ⌜predicates_read !! ℓ = Some encp_read ⌝ ∗
    ⌜ offsets !! ℓ = Some offset ⌝ ∗
    (* The predicate holds for "exclusive-write" message in the history. *)
    ([∗ map] t ↦ msg; encS ∈ phys_hist; abs_hist,
       if (decide (offset ≤ t ∧ phys_hist !! (S t) = None)) then (* full predicate *)
         encoded_predicate_holds
           encp_full
           encS
           msg.(msg_val)
                 ((default msg.(msg_store_view) (na_views !! ℓ)), msg.(msg_persisted_after_view), ∅)
       else (* read predicate *)
         encoded_predicate_holds
           encp_read
           encS
           msg.(msg_val)
                 ((default msg.(msg_store_view) (na_views !! ℓ)), msg.(msg_persisted_after_view), ∅)).

Notation all_full_read_preds_hold phys_hists abs_hists na_views offsets predicates_full predicates_read :=
  ([∗ map] ℓ ↦ phys_hist;abs_hist ∈ phys_hists;abs_hists,
     encoded_full_read_predicates_hold ℓ abs_hist phys_hist na_views offsets predicates_full predicates_read)%I.

Definition encoded_pers_predicate_holds `{nvmHighGS}
  ℓ (abs_hist: gmap time positive) (phys_hist: gmap time message)
  (global_pview: view) (offsets: gmap loc nat) (predicates_pers: gmap loc enc_predicate): iProp Σ :=
  ∃ encp_pers (t offset: nat) encσ msg,
    ⌜ predicates_pers !! ℓ = Some encp_pers ⌝ ∗
    ⌜ offsets !! ℓ = Some offset ⌝ ∗
    ⌜ abs_hist !! t = Some encσ ⌝ ∗
    ⌜ phys_hist !! t = Some msg ⌝ ∗
    (* if a location has never been [fence_sync]ed, it will not have any [persisted] knowledge,
     * in which case we can always use [offset] *)
    ⌜ Nat.add offset (global_pview !!0 ℓ) = t ⌝ ∗
    (* It's easier to work with a per-location assertion. *)
    default emp (persisted_loc ℓ <$> (max_nat_car <$> (global_pview !! ℓ))) ∗            
    (* [p_pers] are objective anyway, might as well make it easy here. *)
    encoded_predicate_holds encp_pers encσ msg.(msg_val) (∅, ∅, ∅).

Notation all_pers_preds_hold phys_hists abs_hists global_pview offsets predicates_pers :=
  ([∗ map] ℓ ↦ phys_hist;abs_hist ∈ phys_hists;abs_hists,
     encoded_pers_predicate_holds ℓ abs_hist phys_hist global_pview offsets predicates_pers)%I.

Section state_interpretation.
  Context `{nvmHighGS}.

  Implicit Types (TV : thread_view).

  Lemma encoded_full_read_predicates_hold_equiv ℓ abs_hist phys_hist na_views na_views' offsets offsets' predicates_full predicates_full' predicates_read predicates_read':
    na_views !! ℓ = na_views' !! ℓ →
    offsets !! ℓ = offsets' !! ℓ →
    predicates_full !! ℓ = predicates_full' !! ℓ →
    predicates_read !! ℓ = predicates_read' !! ℓ →
    encoded_full_read_predicates_hold ℓ abs_hist phys_hist na_views offsets predicates_full predicates_read -∗
    encoded_full_read_predicates_hold ℓ abs_hist phys_hist na_views' offsets' predicates_full' predicates_read'.
  Proof.
    iIntros (eq1 eq2 eq3 eq4) "(% & % & % & % & % & % & H)".
    iExists encp_full, encp_read, offset.
    rewrite -eq1 -eq2 -eq3 -eq4.
    iFrame "%".
    iFrame.
  Qed.

  Lemma encoded_pers_predicate_holds_equiv ℓ abs_hist phys_hist offsets offsets' global_pview global_pview' predicates_pers predicates_pers':
    global_pview !! ℓ = global_pview' !! ℓ →
    offsets !! ℓ = offsets' !! ℓ →
    predicates_pers !! ℓ = predicates_pers' !! ℓ →
    encoded_pers_predicate_holds ℓ abs_hist phys_hist global_pview offsets predicates_pers -∗
    encoded_pers_predicate_holds ℓ abs_hist phys_hist global_pview' offsets' predicates_pers'.
  Proof.
    iIntros (eq1 eq2 eq3) "(%encp_pers & %t & %offset & %encσ & %msg & % & % & % & % & % & Hpview & H)".
    iExists encp_pers, t, offset, encσ, msg.
    rewrite /lookup_zero -eq1 -eq2 -eq3.
    iFrame "%".
    iFrame.
  Qed.

  (** This is our analog to the state interpretation in the Iris weakest
  precondition. We keep this in our crash weakest precondition ensuring that it
  holds before and after each step. **)

  #[local] Existing Instance nvmHighGS_inG.
  
  Definition interp : iProp Σ :=
    ∃ (phys_hists : gmap loc (gmap time message))
      (abs_hists : gmap loc (gmap time positive))
      (global_pview : view)
      (predicates_full : gmap loc enc_predicate)
      (predicates_read: gmap loc enc_predicate)
      (predicates_pers: gmap loc enc_predicate)
      (orders : gmap loc (relation2 positive))
      (bumpers : gmap loc (positive → option positive))
      (na_locs : gset loc)
      (at_locs : gset loc)
      (offsets : gmap loc nat)
      (na_views : gmap loc view),
      (* We keep the points-to predicates to ensure that we know that the keys
       * in the abstract history correspond to the physical history. This ensures
       * that at a crash we know that the value recovered after a crash has a
       * corresponding abstract value. *)
      "ptsMap" ∷ ([∗ map] ℓ ↦ hist ∈ phys_hists, ℓ ↦fh hist) ∗
      "offsets" ∷ offset_auth offsets ∗
      (* For the abstract history map, we need a trivial copy of [rely_self] everytime
       * we insert a new location.
       * This should be obtained from [crashed_at_tok] from base logic. *)
      "#crashedRely" ∷ (∃ OPV, rely_self crashed_at_name (crashed_at_pred OPV)) ∗
      
      "physHists" ∷ auth_map_map_auth histories_rel phy_history_name phys_hists ∗
      (* The messages in [phys_hists] that precede their corresponding offset
      (i.e., those that are no longer present the real physical history) don't
      store any views. *)
      "#oldViewsDiscarded" ∷
        ([∗ map] ℓ ↦ hist;offset ∈ phys_hists;offsets,
          ⌜ ∀ t msg, t < offset → hist !! t = Some msg → discard_msg_views msg = msg ⌝) ∗

      (* Ownership over the full knowledge of the abstract history of _all_
      locations. *)
      "history" ∷ full_map bumpers_name abs_history_name (DfracOwn 1) abs_hists ∗
      "#historyFragments" ∷
        ([∗ map] ℓ ↦ abs_hist ∈ abs_hists,
          [∗ map] t ↦ encσ ∈ abs_hist, frag_entry bumpers_name abs_history_name ℓ t encσ) ∗
      (* Knowledge of all the predicates. *)
      "full_predicates" ∷ own_all_full_preds (DfracOwn 1) predicates_full ∗
      "read_predicates" ∷ own_all_read_preds (DfracOwn 1) predicates_read ∗
      "pers_predicates" ∷ own_all_pers_preds (DfracOwn 1) predicates_pers ∗
      (* All the encoded orders *)
      "allOrders" ∷ own_all_preorders preorders_name orders ∗

      (* the authoritative resource exposes to the program logic *)
      (* "globalPView" ∷ own pview_lb_name (● global_pview) ∗ *)

      (* Seperation of locations. *)
      "%locsDisjoint" ∷ ⌜ na_locs ## at_locs ⌝ ∗
      "%histDomLocs" ∷ ⌜ dom abs_hists = na_locs ∪ at_locs ⌝ ∗
      "naLocs" ∷ gen_alocs_auth exclusive_locs_name na_locs ∗
      "atLocs" ∷ gen_alocs_auth shared_locs_name at_locs ∗

      (* Non-atomic locations. *)
      "%naViewsDom" ∷ ⌜ dom na_views = na_locs ⌝ ∗ (* NOTE: If this equality persists we could remove na_locs *)
      "naView" ∷ ghost_map_auth non_atomic_views_gname drop_OCV_clear (DfracOwn 1) na_views ∗

      (* Atomic locations. *)
      "%mapShared" ∷ ⌜ shared_locs_inv (restrict at_locs (map_zip_with drop_prefix phys_hists offsets)) ⌝ ∗
      (* For shared locations [interp] owns the fragment for the full history. *)
      "atLocsHistories" ∷
        ([∗ map] ℓ ↦ abs_hist ∈ (restrict at_locs abs_hists),
          know_full_encoded_history_loc ℓ 1 abs_hist) ∗

      "#ordered" ∷ ([∗ map] ℓ ↦ hist; order ∈ abs_hists; orders,
                    ⌜ increasing_map order hist ⌝) ∗

      (* TODO: persistent knowledge matches that of abstract history *)
      "%histPViewDoms" ∷ ⌜ dom global_pview ⊆ dom abs_hists ⌝ ∗

      (* The full/read predicates hold for all locations. *)
      "predsFullReadHold" ∷
        all_full_read_preds_hold phys_hists abs_hists na_views offsets predicates_full predicates_read ∗

      (* persistent predicates for all locations *)
      "predsPersHold" ∷
        all_pers_preds_hold phys_hists abs_hists global_pview offsets predicates_pers ∗

      (** * Bump-back function *)
      (* We know about all the bumpers. *)
      "allBumpers" ∷ own_all_bumpers bumpers_name bumpers ∗
      (* The bump functions are monotone. *)
      "#bumpMono" ∷ ([∗ map] ℓ ↦ order; bump ∈ orders; bumpers,
        ∀ e1 e2 e1' e2', ⌜bump e1 = Some e1'⌝ → ⌜bump e2 = Some e2'⌝ →
                         ⌜order e1 e2⌝ → ⌜order e1' e2'⌝) ∗

      "%FullBumperDoms" ∷
        ⌜ dom predicates_full = dom bumpers ⌝ ∗
      "%ReadBumperDoms" ∷
        ⌜ dom predicates_read = dom bumpers ⌝ ∗
      "%PersBumperDoms" ∷
        ⌜ dom predicates_pers = dom bumpers ⌝ ∗

      (* The predicate holds after a crash for the bumped state. *)
      "#predFullNextgen" ∷ ([∗ map] ℓ ↦ order; bump ∈ orders; bumpers,
        ∃ encp_full encp_read encp_pers,
        ⌜ predicates_full !! ℓ = Some encp_full ⌝ ∗
        ⌜ predicates_read !! ℓ = Some encp_read ⌝ ∗
        ⌜ predicates_pers !! ℓ = Some encp_pers ⌝ ∗
        ■ (know_protocol_enc ℓ encp_full encp_read encp_pers order bump -∗
           ∀ encσ_p v_p encσ_f v_f MsgV_f,
             ⌜ order encσ_p encσ_f ∨ encσ_p = encσ_f ⌝ -∗
             encoded_predicate_holds encp_pers encσ_p v_p (∅, ∅, ∅) -∗
             encoded_predicate_holds encp_full encσ_f v_f MsgV_f -∗
             (* first case: crash at [encσ_f] *)
             (∀ encσ_f',
                ⌜ bump encσ_f = Some encσ_f' ⌝ ==∗
                ∃ P_full' P_pers',
                  encp_full encσ_f' v_f ≡ Some P_full' ∗ encp_pers encσ_f' v_f ≡ Some P_pers' ∗
                  (nextgen_flush (⎡ crashed_in_enc ℓ encσ_f ⎤ -∗ P_full' ∗ P_pers': dPropO Σ)) MsgV_f) ∧
             (* second case: crash at [encσ_c ⊏ encσ_f] *)
             (∀ encσ_c encσ_c' v_c MsgV_c,
                ⌜ bump encσ_c = Some encσ_c' ⌝ -∗
                ⌜ order encσ_p encσ_c ∨ encσ_p = encσ_c ⌝ -∗
                ⌜ order encσ_c encσ_f ⌝ -∗
                encoded_predicate_holds encp_read encσ_c v_c MsgV_c ==∗
                ∃ P_full' P_pers',
                  encp_full encσ_c' v_c ≡ Some P_full' ∗ encp_pers encσ_c' v_c ≡ Some P_pers' ∗
                  (nextgen_flush (⎡ crashed_in_enc ℓ encσ_c ⎤ -∗ P_full' ∗ P_pers': dPropO Σ)) MsgV_c))) ∗

      "#predReadNextgen" ∷ ([∗ map] ℓ ↦ pred_read; bumper ∈ predicates_read; bumpers,
        ∀ e e' v TV, ■ (⌜ bumper e = Some e' ⌝ -∗ encoded_predicate_holds pred_read e v TV -∗
                        ∃ (P: dPropO Σ), pred_read e' v ≡ Some P ∗ (nextgen_flush (P: dProp Σ)) TV)) ∗

      (* we don't need the other half for [p_full] restoration during recovery. *)
      "#predFullReadSplit" ∷ ([∗ map] ℓ ↦ pred_full; pred_read ∈ predicates_full; predicates_read,
        ∀ e v TV, ■ (encoded_predicate_holds pred_full e v TV -∗ encoded_predicate_holds pred_read e v TV)) ∗

      (* Bumpers map valid input to valid output. *)
      "%bumperBumpToValid" ∷
        ⌜ map_Forall
            (λ _ bumper, ∀ e e', bumper e = Some e' → is_Some (bumper e'))
            bumpers⌝ ∗
      (* All the abstract state are "valid" inputs to the bumpers. *)
      "#bumperSome" ∷ ([∗ map] ℓ ↦ abs_hist; bumper ∈ abs_hists; bumpers,
        ⌜ map_Forall (λ _ e, is_Some (bumper e)) abs_hist ⌝) ∗

      (* additional knowledge for protocol recovery. *)
      "#locsOffsets" ∷ ([∗ map] ℓ ↦ offset ∈ offsets, offset_loc ℓ offset) ∗
      "#locsProtocols" ∷ ([∗ map] ℓ ↦ order; bump ∈ orders; bumpers,
        ∃ encp_full encp_read encp_pers,
          ⌜ predicates_full !! ℓ = Some encp_full ⌝ ∗
          ⌜ predicates_read !! ℓ = Some encp_read ⌝ ∗
          ⌜ predicates_pers !! ℓ = Some encp_pers ⌝ ∗
          know_protocol_enc ℓ encp_full encp_read encp_pers order bump).

  Global Instance highExtraStateInterp : extraStateInterp Σ := {
    extra_state_interp := interp;
  }.
End state_interpretation.

Opaque interp.
