From iris.proofmode Require Import proofmode.
From iris_named_props Require Import named_props.

From iris.algebra Require Import auth gset.
From self Require Import extra view_slice.
From self.high.lib Require Import increasing_map.

From self.nextgen Require Import nextgen_promises.
From self.base Require Import primitive_laws generational_resources.
From self.high Require Export dprop predicates generational_resources wrappers.

From self.lang Require Import lang.

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

Section state_interpretation.
  Context `{nvmHighGS}.

  Implicit Types (TV : thread_view).

  (* Definition pred_post_crash_implication {ST} *)
  (*            (ϕ : ST → val → dProp Σ) bumper : dProp Σ := *)
  (*   □ ∀ s v, ϕ s v -∗ <PCF> ϕ (bumper s) v. *)

  (** This is our analog to the state interpretation in the Iris weakest
  precondition. We keep this in our crash weakest precondition ensuring that it
  holds before and after each step. **)

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
      in the abstract history correspond to the physical history. This ensures
      that at a crash we know that the value recovered after a crash has a
      corresponding abstract value.
       * TODO: attempt to simplify this part by using [↦fh]. *)
      "ptsMap" ∷ ([∗ map] ℓ ↦ hist ∈ phys_hists, ℓ ↦fh hist) ∗
      "offsets" ∷ crashed_at_offset (MaxNat <$> offsets) ∗
      (* Yixuan: I revived this assertion because we no longer have [oldViewsDiscarded],
       * which was used to infer the domains of two maps. *)
      "%offsetsDom" ∷ ⌜ dom phys_hists = dom offsets ⌝ ∗

      "physHist" ∷ auth_map_map_auth phy_history_name phys_hists ∗

      (* Ownership over the full knowledge of the abstract history of _all_
      locations. *)
      "history" ∷ full_map bumpers_name abs_history_name (DfracOwn 1) abs_hists ∗
      "#historyFragments" ∷
        ([∗ map] k1 ↦ mi ∈ abs_hists,
          [∗ map] k2 ↦ v ∈ mi, frag_entry bumpers_name abs_history_name k1 k2 v) ∗
      (* Knowledge of all the predicates. *)
      "full_predicates" ∷ own_all_full_preds (DfracOwn 1) predicates_full ∗
      "read_predicates" ∷ own_all_read_preds (DfracOwn 1) predicates_read ∗
      "pers_predicates" ∷ own_all_pers_preds (DfracOwn 1) predicates_pers ∗
      (* All the encoded orders *)
      "allOrders" ∷ own_all_preorders preorders_name orders ∗

      (* the duplicable resource to connect with baseSpirea *)
      "#globalPViewPersisted" ∷ persisted global_pview ∗

      (* the authoritative resource exposes to the program logic *)
      (* "globalPView" ∷ own pview_lb_name (● global_pview) ∗ *)

      (* Seperation of locations. *)
      "%locsDisjoint" ∷ ⌜ na_locs ## at_locs ⌝ ∗
      "%histDomLocs" ∷ ⌜ dom abs_hists = na_locs ∪ at_locs ⌝ ∗
      "naLocs" ∷ gen_alocs_auth exclusive_locs_name na_locs ∗
      "atLocs" ∷ gen_alocs_auth shared_locs_name at_locs ∗

      (* Non-atomic locations. *)
      "%naViewsDom" ∷ ⌜ dom na_views = na_locs ⌝ ∗ (* NOTE: If this equality persists we could remove na_locs *)
      "naView" ∷ ghost_map_auth non_atomic_views_gname loc_map_rel (DfracOwn 1) na_views ∗

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
        ([∗ map] ℓ ↦ phys_hist;abs_hist ∈ phys_hists;abs_hists,
          ∃ predFull predRead offset,
            ⌜predicates_full !! ℓ = Some predFull ⌝ ∗
            ⌜predicates_read !! ℓ = Some predRead ⌝ ∗
            ⌜ offsets !! ℓ = Some offset ⌝ ∗
            (* The predicate holds for "exclusive-write" message in the history. *)
            ([∗ map] t ↦ msg; encS ∈ phys_hist; abs_hist,
               if (decide (offset ≤ t ∧ phys_hist !! (S t) = None)) then (* full predicate *)
                 encoded_predicate_holds
                   predFull
                   encS
                   msg.(msg_val)
                   ((default msg.(msg_store_view) (na_views !! ℓ)), msg.(msg_persisted_after_view), ∅)
               else (* read predicate *)
                 encoded_predicate_holds
                   predRead
                   encS
                   msg.(msg_val)
                   ((default msg.(msg_store_view) (na_views !! ℓ)), msg.(msg_persisted_after_view), ∅)
        )) ∗

      (* persistent predicates for all locations *)
      "predsPersHold" ∷
        ([∗ map] ℓ ↦ phys_hist;abs_hist ∈ phys_hists;abs_hists,
          ∃ pred_pers (t: nat) encS msg,
            ⌜ predicates_pers !! ℓ = Some pred_pers ⌝ ∗
            (* It seems like the timestamp in [persisted] assertion is before
               offset, we need to add it here *)
            ⌜ offsets_add offsets global_pview !! ℓ = Some t ∨ (global_pview !! ℓ = None ∧ offsets !! ℓ = Some t) ⌝ ∗
            ⌜ abs_hist !! t = Some encS ⌝ ∗
            ⌜ phys_hist !! t = Some msg ⌝ ∗
            encoded_predicate_holds
              pred_pers
              encS
              msg.(msg_val)
              ((default msg.(msg_store_view) (na_views !! ℓ)), msg.(msg_persisted_after_view), ∅)) ∗

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

      (* Yixuan: I'm trying the alternative model where we simply remember that protocols exist for all locations *)

      (* TODO: add back protocol knowledges *)
      (* (* The predicate holds after a crash for the bumped state. *) *)
      (* "#predFullPostCrash" ∷ ([∗ map] ℓ ↦ pred_full; bump ∈ predicates_full; bumpers, *)
      (*   ∃ pred_read pred_pers order, *)
      (*   ⌜ predicates_read !! ℓ = Some pred_read ⌝ ∗ *)
      (*   ⌜ predicates_pers !! ℓ = Some pred_pers ⌝ ∗ *)
      (*   ⌜ orders !! ℓ = Some order ⌝ ∗ *)
      (*   □ (∀ e_p v_p (hG : nvmDeltaG) TV, *)
      (*     encoded_predicate_holds pred_pers e_p v_p (TV, hG) -∗ *)
      (*     (* first case: crash at [e_f] *) *)
      (*     (∀ e_f e_f' v_f, encoded_predicate_holds pred_full e_f v_f (TV, hG) -∗ ⌜ bump e_f = Some e_f' ⌝ -∗ *)
      (*              ∃ P_full' P_pers', pred_full e_f' v_f ≡ Some P_full' ∗ pred_pers e_f' v_f ≡ Some P_pers' ∗ *)
      (*                                 (post_crash_flush (P_full' ∗ P_pers': dPropO Σ)) (TV, hG)) ∧ *)
      (*     (* second case: crash at [e_c ⊏ e_f] *) *)
      (*     (∀ e_f e_c e_c' v_f v_c (P_full: dPropO Σ), *)
      (*        pred_full e_f v_f ≡ Some P_full -∗ *)
      (*        ∃ P_obj: dProp Σ, (<obj> (P_full -∗ <obj> P_obj)) (TV, hG) ∗ *)
      (*                          (P_obj (TV, hG) -∗ *)
      (*                           ⌜ bump e_c = Some e_c' ⌝ -∗ ⌜ order e_p e_c ∨ e_p = e_c ⌝ -∗ ⌜ order e_c e_f ⌝ -∗ *)
      (*                           encoded_predicate_holds pred_read e_c v_c (TV, hG) -∗ *)
      (*                           ∃ P_full' P_pers', pred_full e_c' v_c ≡ Some P_full' ∗ pred_pers e_c' v_c ≡ Some P_pers' ∗ *)
      (*                                              (post_crash_flush (P_full' ∗ P_pers': dPropO Σ)) (TV, hG))))) ∗ *)

      (* "#predReadPostCrash" ∷ ([∗ map] ℓ ↦ pred_read; bump ∈ predicates_read; bumpers, *)
      (*   ∀ e e' v TV hG, □ (⌜ bump e = Some e' ⌝ -∗ encoded_predicate_holds pred_read e v (TV, hG) -∗ *)
      (*                      ∃ (P: dPropO Σ), pred_read e' v ≡ Some P ∗ (post_crash_flush (P: dProp Σ)) (TV, hG))) ∗ *)

      (* "#predFullReadSplit" ∷ ([∗ map] ℓ ↦ pred_full; pred_read ∈ predicates_full; predicates_read, *)
      (*   ∀ e v i, □ (encoded_predicate_holds pred_full e v i -∗ encoded_predicate_holds pred_read e v i)) ∗ *)

      (* Bumpers map valid input to valid output. *)
      "%bumperBumpToValid" ∷
        ⌜ map_Forall
            (λ _ bumper, ∀ e e', bumper e = Some e' → is_Some (bumper e'))
            bumpers⌝ ∗
      (* All the abstract state are "valid" inputs to the bumpers. *)
      "#bumperSome" ∷ ([∗ map] ℓ ↦ abs_hist; bumper ∈ abs_hists; bumpers,
        ⌜ map_Forall (λ _ e, is_Some (bumper e)) abs_hist ⌝).

  Global Instance highExtraStateInterp : extraStateInterp Σ := {
    extra_state_interp := interp;
  }.
End state_interpretation.

Opaque interp.
