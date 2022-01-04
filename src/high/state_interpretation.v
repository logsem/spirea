From iris.proofmode Require Import base.
From iris.algebra Require Import auth gset.
From iris_named_props Require Import named_props.

From self Require Import extra.
From self.algebra Require Import ghost_map.
From self.base Require Import primitive_laws.
From self.high Require Export dprop resources post_crash_modality increasing_map.

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
    intros map ? ?.
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

Definition shared_locs_inv (locs : gmap loc (gmap time message)) :=
  map_map_Forall
    (λ (ℓ : loc) (t : time) (msg : message),
      (* For shared locations the two persist views are equal. This enforces
      that shared locations can only be written to using release store and
      RMW operations. *)
      msg.(msg_store_view) !!0 ℓ = t ∧
      msg.(msg_persist_view) = msg.(msg_persisted_after_view))
    locs.

Section state_interpretation.
  Context `{nvmFixedG Σ, hGD : nvmDeltaG Σ}.

  Implicit Types (TV : thread_view).

  Definition pred_post_crash_implication {ST}
             (ϕ : ST → val → _ → dProp Σ) bumper : dProp Σ :=
    □ ∀ (hD : nvmDeltaG Σ) s v, ϕ s v hD -∗ <PCF> hD', ϕ (bumper s) v hD'.

  (** This is our analog to the state interpretation in the Iris weakest
  precondition. We keep this in our crash weakest precondition ensuring that it
  holds before and after each step. **)
  Definition interp : iProp Σ :=
    (∃ (phys_hists : gmap loc (gmap time message))
       (abs_hists : gmap loc (gmap time positive))
       (predicates : gmap loc (positive → val → option (nvmDeltaG Σ → dProp Σ)))
       (CV : view)
       (orders : gmap loc (relation2 positive))
       (bumpers : gmap loc (positive → option positive))
       (na_locs : gset loc)
       (at_locs : gset loc)
       (na_views : gmap loc view),
      (* We keep the points-to predicates to ensure that we know that the keys
      in the abstract history correspond to the physical history. This ensures
      that at a crash we know that the value recovered after a crash has a
      corresponding abstract value. *)
      "ptsMap" ∷ ([∗ map] ℓ ↦ hist ∈ phys_hists, ℓ ↦h hist) ∗
      "physHist" ∷ auth_map_map_auth know_phys_history_name phys_hists ∗
      "#crashedAt" ∷ crashed_at CV ∗

      (* Ownership over the full knowledge of the abstract history of _all_
      locations. *)
      "history" ∷ own_full_history abs_history_name know_abs_history_name abs_hists ∗
      (* Knowledge of all the predicates. *)
      "predicates" ∷ own predicates_name (● preds_to_ra predicates) ∗
      (* All the encoded orders *)
      "allOrders" ∷ own_all_preorders preorders_name orders ∗

      (* Seperation of locations. *)
      "%locsDisjoint" ∷ ⌜ na_locs ## at_locs ⌝ ∗
      "%histDomLocs" ∷ ⌜ dom _ abs_hists = na_locs ∪ at_locs ⌝ ∗
      "exclusiveLocs" ∷ own exclusive_locs_name (● na_locs) ∗
      "sharedLocs" ∷ own shared_locs_name (● at_locs) ∗

      (* Non-atomic locations. *)
      "%naViewsDom" ∷ ⌜ dom _ na_views = na_locs ⌝ ∗ (* NOTE: If this equality persists we could remove na_locs *)
      "naView" ∷ ghost_map_auth non_atomic_views_gname (DfracOwn 1) na_views ∗

      (* Shared locations. *)
      "%mapShared" ∷ ⌜ shared_locs_inv (restrict at_locs phys_hists) ⌝ ∗
      (* For shared locations [interp] owns the fragment for the full history. *)
      "sharedLocsHistories" ∷
        ([∗ map] ℓ ↦ abs_hist ∈ (restrict at_locs abs_hists),
          know_full_encoded_history_loc ℓ abs_hist) ∗

      "#ordered" ∷ ([∗ map] ℓ ↦ hist; order ∈ abs_hists; orders,
                    ⌜increasing_map order hist⌝) ∗

      (* The predicates hold for all the atomic locations. *)
      "predsHold" ∷
        ([∗ map] ℓ ↦ phys_hist;abs_hist ∈ phys_hists;abs_hists,
          ∃ pred,
            ⌜predicates !! ℓ = Some pred⌝ ∗
            (* The predicate holds for each message in the history. *)
            ([∗ map] t ↦ msg; encS ∈ phys_hist; abs_hist,
               encoded_predicate_holds
                 pred
                 encS
                 msg.(msg_val)
                 ((default msg.(msg_store_view) (na_views !! ℓ)), msg.(msg_persisted_after_view), ∅))) ∗

      (** * Bump-back function *)
      (* We know about all the bumpers. *)
      "allBumpers" ∷ own_all_bumpers bumpers_name bumpers ∗
      (* The bump functions are monotone. *)
      "#bumpMono" ∷ ([∗ map] ℓ ↦ order; bump ∈ orders; bumpers,
        ∀ e1 e2 e1' e2', ⌜bump e1 = Some e1'⌝ → ⌜bump e2 = Some e2'⌝ →
                         ⌜order e1 e2⌝ → ⌜order e1' e2'⌝) ∗
      (* The predicate holds after a crash for the bumped state. *)
      "#predPostCrash" ∷ ([∗ map] ℓ ↦ pred; bump ∈ predicates; bumpers,
        □ (∀ (e : positive) (v : val) (hG : nvmDeltaG Σ) TV (P : nvmDeltaG Σ → dProp _) e',
          ⌜bump e = Some e'⌝ ∗ ⌜pred e v = Some P⌝ ∗ P hG TV -∗
          ∃ P', ⌜pred e' v = Some P'⌝ ∗ ((post_crash_flush P') (∅, ∅, ∅)))) ∗
      (* Bumpers map valid input to valid output. *)
      "%bumperBumpToValid" ∷
        ⌜map_Forall (λ _ bumper, ∀ e, ∃ e', bumper e = Some e' →
                                            is_Some (bumper e')) bumpers⌝ ∗
      (* All the abstract state are "valid" inputs to the bumpers. *)
      "#bumperSome" ∷ ([∗ map] ℓ ↦ abs_hist; bumper ∈ abs_hists; bumpers,
        ⌜map_Forall (λ _ e, is_Some (bumper e)) abs_hist⌝)).

  Global Instance highExtraStateInterp : extraStateInterp Σ := {
    extra_state_interp := interp;
  }.

End state_interpretation.
