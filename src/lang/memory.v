(* This module defines the memory model or the memory subsystem. *)

From stdpp Require Import countable numbers gmap.
From iris.heap_lang Require Import locations.
From iris.algebra Require Import gmap numbers.

From self Require Import extra.
From self.algebra Require Export view.
From self Require Import view_slice.
From self.lang Require Import syntax.
From self.lang Require Export thread_view.

Record message : Type := Msg {
  msg_val : val;
  msg_store_view : view;
  msg_persist_view : view;
  msg_persisted_after_view : view;
}.

Canonical Structure messageO := leibnizO message.

Notation history := (gmap time message).

Notation store := (gmap loc history).

Definition mem_config : Type := store * view.

Section consistent_cut.

  (* Removes all messages from [hist] after [t]. *)
  Definition cut_history t (hist : history) : history :=
    filter (λ '(t', ev), t' ≤ t) hist.

  Definition discard_msg_views (msg : message) : message :=
    Msg msg.(msg_val) ∅ ∅ ∅.

  (* For each location in [V] pick the message in the store that it specifies. *)
  Definition slice_of_store (V : view) (σ : store) : store :=
    (λ (hist : gmap _ _), discard_msg_views <$> hist) <$> (slice_of_hist V σ).

  Definition consistent_cut (CV : view) (σ : store) : Prop :=
    map_Forall
      (λ ℓ '(MaxNat t),
       ∃ hist msg, σ !! ℓ = Some hist ∧
                   hist !! t = Some msg ∧
                   map_Forall (λ _ msg', msg'.(msg_persisted_after_view) ⊑ CV)
                              (cut_history t hist))
      CV.

  (* Consisten cut is stronger than [valid_slice]. *)
  Lemma consistent_cut_valid_slice CV σ :
    consistent_cut CV σ → valid_slice CV σ.
  Proof.
    rewrite /valid_slice /consistent_cut.
    intros cut.
    intros ℓ [[t] hist].
    intros [cvLook storeLook]%map_lookup_zip_Some.
    eapply map_Forall_lookup_1 in cut as temp; last done.
    destruct temp as (? & ? & ? & ? & ?).
    simplify_eq.
    done.
  Qed.

  (* if [V] is a consistent cut of [σ] then the domain of [V] is included in
  [σ]. Intuitively, the recovered locations where all in the heap. *)
  Lemma consistent_cut_subseteq_dom V σ :
    consistent_cut V σ → dom (gset _) V ⊆ dom _ σ.
  Proof.
    rewrite /consistent_cut.
    intros map.
    intros ?. rewrite !elem_of_dom. intros [[t] ?].
    eapply map_Forall_lookup_1 in map; last done.
    naive_solver.
  Qed.

  Lemma consistent_cut_lookup_slice CV σ ℓ :
    consistent_cut CV σ → slice_of_store CV σ !! ℓ = None → CV !! ℓ = None.
  Proof.
    rewrite -!not_elem_of_dom.
    rewrite /slice_of_store.
    rewrite dom_fmap.
    rewrite slice_of_hist_dom.
    intros ?%consistent_cut_subseteq_dom.
    set_solver.
  Qed.

  Lemma consistent_cut_extract CV store ℓ t hist msg :
    consistent_cut CV store →
    CV !! ℓ = Some (MaxNat t) →
    store !! ℓ = Some hist →
    hist !! t = Some msg →
    msg_persisted_after_view msg ⊑ CV.
  Proof.
    rewrite /consistent_cut.
    intros cut cvLook storeLook histLook.
    destruct (cut ℓ (MaxNat t) cvLook) as (? & ? & ? & ? & map).
    apply (map t msg).
    rewrite /cut_history.
    apply map_filter_lookup_Some.
    naive_solver.
  Qed.

  Lemma slice_of_store_dom_subset CV σ :
    dom (gset _) (slice_of_store CV σ) ⊆ dom _ σ.
  Proof. rewrite /slice_of_store dom_fmap. apply slice_of_hist_dom_subset. Qed.

  Lemma slice_of_store_lookup_Some_subseteq m1 m2 CV a ℓ :
    m1 ⊆ m2 →
    slice_of_store CV m1 !! ℓ = Some a →
    slice_of_store CV m2 !! ℓ = Some a.
  Proof. Abort.

  Lemma slice_of_store_lookup_inv CV store h ℓ :
    valid_slice CV store →
    slice_of_store CV store !! ℓ = Some h →
    ∃ t hist m,
      CV !! ℓ = Some (MaxNat t) ∧
      store !! ℓ = Some hist ∧
      hist !! t = Some m ∧
      h = {[ 0 := discard_msg_views m ]}.
  Proof.
    rewrite /slice_of_store.
    intros val (hist & eq & sliceLook)%lookup_fmap_Some.
    apply slice_of_hist_lookup_inv in sliceLook
        as (t & hist' & m & bungo & ? & ? & ?); last done.
    eexists _, _, _.
    split_and!; try done.
    simplify_eq.
    rewrite map_fmap_singleton.
    done.
  Qed.

  Lemma slice_of_store_lookup_Some CV store ℓ msg hist t :
    slice_of_store CV store !! ℓ = Some hist →
    hist !! t = Some msg →
    exists t' hist' msg',
      CV !! ℓ = Some (MaxNat t') ∧
      t = 0 ∧
      store !! ℓ = Some hist' ∧
      hist' !! t' = Some msg' ∧
      msg = discard_msg_views msg' ∧
      hist = {[0 := discard_msg_views msg']}.
  Proof.
    rewrite /slice_of_store /slice_of_hist map_fmap_zip_with.
    rewrite map_fmap_zip_with.
    intros ([t'] & h & -> & ? & ?)%map_lookup_zip_with_Some histLook.
    exists t', h.
    destruct (h !! t') as [m|]; last naive_solver.
    exists m.
    rewrite map_fmap_singleton.
    rewrite map_fmap_singleton in histLook.
    apply lookup_singleton_Some in histLook.
    naive_solver.
  Qed.

  Lemma slice_of_store_lookup_Some_singleton CV store ℓ msg :
    slice_of_store CV store !! ℓ = Some {[0 := discard_msg_views msg]} →
    exists t h, CV !! ℓ = Some (MaxNat t) ∧
           store !! ℓ = Some h ∧
           (msg_val <$> h !! t) = Some (msg_val msg).
  Proof.
    rewrite /slice_of_store /slice_of_hist map_fmap_zip_with.
    rewrite map_fmap_zip_with.
    intros ([t] & h & eq & ? & ?)%map_lookup_zip_with_Some.
    exists t, h.
    split_and!; [done | done |].
    destruct (h !! t) as [m|]; last done.
    rewrite map_fmap_singleton in eq.
    destruct msg, m.
    by simplify_eq.
  Qed.

End consistent_cut.

Section memory.

  Implicit Types (v : val) (ℓ : loc) (σ : store) (V : view).

  Inductive mem_event : Type :=
  | MEvAllocN (a : memory_access) ℓ (len : nat) v
  | MEvLoad ℓ v
  | MEvStore ℓ v
  (* Acquire/release weak memory events. *)
  | MEvLoadAcquire ℓ v
  | MEvStoreRelease ℓ v
  (* RMW are special *)
  | MEvRMW ℓ (vExp vNew : val) (* read-modify-write *)
  | MEvRMWFail ℓ (v1Exp : val) (v2Exp : val) (* for failed RMWs *)
  (* Persistent memory specific. *)
  | MEvFlush ℓ
  | MEvFence
  | MEvFenceSync.

  (* Takes a value and creates an initial history for that value. *)
  Definition initial_history (a : memory_access) SV PV v : history :=
    let view_access V := match a with NA => ∅ | AT => V end
    in {[0 := Msg v (view_access SV) (view_access PV) PV]}.

  (* Convert an array into a store. *)
  Fixpoint heap_array ℓ a SV PV (vs : list val) : store :=
    match vs with
    | [] => ∅
    | v :: vs' =>
        {[ ℓ := initial_history a SV PV v ]} ∪ heap_array (ℓ +ₗ 1) a SV PV vs'
    end.

  Lemma heap_array_lookup ℓ a SV PV (vs : list val) (ow : history) (k : loc) :
    (heap_array ℓ a SV PV vs : store) !! k = Some ow ↔
    ∃ j w, (0 ≤ j)%Z ∧ k = ℓ +ₗ j ∧
            (ow = initial_history a SV PV w) ∧
            vs !! (Z.to_nat j) = (Some w).
  Proof.
    revert k ℓ; induction vs as [|v' vs IH]=> l' ℓ /=.
    { rewrite lookup_empty. naive_solver lia. }
    rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
    - intros [[-> ?] | (Hl & j & w & ? & -> & -> & ?)].
      { eexists 0, _. rewrite loc_add_0. naive_solver lia. }
      eexists (1 + j)%Z, _. rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
    - intros (j & w & ? & -> & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
      { rewrite loc_add_0; eauto. }
      right. split.
      { rewrite -{1}(loc_add_0 ℓ). intros ?%(inj (loc_add _)); lia. }
      assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
      { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
      rewrite Hj /= in Hil.
      eexists (j - 1)%Z, _. rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l.
      auto with lia.
  Qed.

  Lemma heap_array_map_disjoint (h : gmap loc history) SV PV PAV ℓ (vs : list val) :
    (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (ℓ +ₗ i) = None) →
    (heap_array ℓ SV PV PAV vs) ##ₘ h.
  Proof.
    intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
    intros (j&w&?&->&?&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
    move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
  Qed.

  (* Initializes a region of the memory starting at [ℓ] *)
  Definition state_init_heap a (ℓ : loc) (n : nat) SV PV (v : val) (σ : store) : store :=
    heap_array ℓ a SV PV (replicate n v) ∪ σ.

  (* Small-step reduction steps on the memory. *)

  Inductive mem_step : mem_config → thread_view → mem_event → mem_config → thread_view → Prop :=
  (* Allocating a new location. *)
  | MStepAllocN a σ SV FV BV ℓ (len : nat) v PV :
     (0 < len)%Z →
     (∀ idx, (0 ≤ idx)%Z → (idx < len)%Z → σ !! (ℓ +ₗ idx) = None) → (* This is a fresh segment of the heap not already in use. *)
     (* V' = <[ ℓ := 0 ]>SV → (* V' incorporates the new event in the threads view. *) This may not be needed. *)
     mem_step (σ, PV) (SV, FV, BV)
              (MEvAllocN a ℓ len v)
              (state_init_heap a ℓ len SV FV v σ, PV) (SV, FV, BV)
  (* A normal non-atomic load. *)
  | MStepLoad (σ : store) SV FV BV t (ℓ : loc) (v : val) h PV :
     σ !! ℓ = Some h →
     msg_val <$> (h !! t) = Some v →
     SV !!0 ℓ ≤ t →
     mem_step (σ, PV) (SV, FV, BV)
              (MEvLoad ℓ v)
              (σ, PV) (SV, FV, BV)
              (* (σ, PV) ((<[ ℓ := t ]>SV), FV, BV) (* This variant includes the timestamp of the loaded msg. *) *)
  (* An atomic acquire load. *)
  | MStepLoadAcquire σ SV FV BV t ℓ (v : val) MV MP _MP h PV :
     σ !! ℓ = Some h →
     h !! t = Some (Msg v MV MP _MP) →
     SV !!0 ℓ ≤ t →
     mem_step (σ, PV) (SV, FV, BV)
              (MEvLoadAcquire ℓ v)
              (σ, PV) (SV ⊔ MV, FV, BV ⊔ MP) (* An acquire incorporates both the store view and the persistent view. *)
  (* A normal non-atomic write. *)
  | MStepStore σ SV FV BV t ℓ (v : val) h V' PV :
     σ !! ℓ = Some h →
     h !! t = None → (* No event exists at t already. *)
     SV !!0 ℓ < t →
     V' = <[ℓ := MaxNat t]>SV → (* V' incorporates the new event in the threads view. *)
     mem_step (σ, PV) (SV, FV, BV)
             (MEvStore ℓ v)
             (<[ℓ := <[t := Msg v ∅ ∅ FV]>h]>σ, PV) (V', FV, BV)
  (* An atomic release write. *)
  | MStepStoreRelease σ SV FV BV t ℓ (v : val) h V' PV :
     σ !! ℓ = Some h →
     h !! t = None → (* No event exists at t already. *)
     SV !!0 ℓ < t →
     V' = <[ℓ := MaxNat t]>SV → (* V' incorporates the new event in the threads view. *)
     mem_step (σ, PV) (SV, FV, BV)
              (MEvStoreRelease ℓ v)
              (<[ℓ := <[t := Msg v V' FV FV]>h]>σ, PV) (V', FV, BV) (* A release releases both V' and FV. *)
  (* Read-modify-write instructions. *)
  | MStepRMW σ ℓ h v_i MV MP SV t SV' FV P' BV PV v_t _MP :
     σ !! ℓ = Some h →
     SV !!0 ℓ ≤ t →
     h !! t = Some (Msg v_i MV MP _MP) → (* We read an event at time [t]. *)
     (* All values that we could have reads are comparable to [v_i]. *)
     (∀ t' msg, SV !!0 ℓ ≤ t' → h !! t' = Some msg → vals_compare_safe v_i msg.(msg_val)) →
     h !! (t + 1) = None → (* The next timestamp is available, ensures that no other RMW read this event. *)
     SV' = (<[ ℓ := MaxNat (t + 1) ]>(SV ⊔ MV)) → (* SV' incorporates the new event in the threads view. *)
     P' = FV ⊔ MP →
     mem_step (σ, PV) (SV, FV, BV)
              (MEvRMW ℓ v_i v_t)
              (<[ℓ := <[t + 1 := Msg v_t SV' P' P']>h]>σ, PV) (SV', FV, BV ⊔ MP)
  | MStepRMWFail σ SV FV BV t ℓ (v_i v_t : val) MV MP _MP h PV :
     σ !! ℓ = Some h →
     h !! t = Some (Msg v_t MV MP _MP) →
     SV !!0 ℓ ≤ t →
     (* All values that we could have reads are comparable to [v_t]. *)
     (∀ t' msg, SV !!0 ℓ ≤ t' → h !! t' = Some msg → vals_compare_safe v_i msg.(msg_val)) →
     (h !! (t + 1)) = None →
     mem_step (σ, PV) (SV, FV, BV)
              (MEvRMWFail ℓ v_i v_t)
              (σ, PV) (SV ⊔ MV, FV, BV ⊔ MP) (* An acquire incorporates both the store view and the persistent view. *)
  (* Write-back instruction. *)
  | MStepFlush σ SV FV BV ℓ t PV :
     SV !!0 ℓ = t → (* An equality here is fine, the timestamps are only lower bounds anyway. *)
     mem_step (σ, PV) (SV, FV, BV)
              (MEvFlush ℓ)
              (σ, PV) (SV, FV, {[ℓ := MaxNat t]} ⊔ BV)
  (* Asynchronous fence. *)
  | MStepFence σ SV FV BV PV :
     mem_step (σ, PV) (SV, FV, BV)
              MEvFence
              (σ, PV) (SV, FV ⊔ BV, BV)
  (* Synchronous fence. *)
  | MStepFenceSync σ SV FV BV PV :
     mem_step (σ, PV) (SV, FV, BV)
              MEvFenceSync
              (σ, PV ⊔ BV) (SV, FV ⊔ BV, BV).

  (* The crash step is different from the other steps in that it does not depend
  on any current thread. We therefore define it as a separate type. *)
  Inductive crash_step : mem_config → mem_config → Prop :=
  | MCrashStep σ p p' :
     p ⊑ p' →
     consistent_cut p' σ →
     crash_step (σ, p) (slice_of_store p' σ, view_to_zero p').

  (* It is always possible to allocate a section of memory. *)
  Lemma alloc_fresh v (len : nat) a σ p SV FV BV :
    let ℓ := fresh_locs (dom (gset loc) σ) in (* ℓ is directly after the largest allocated location. *)
    (0 < len)%Z →
    mem_step (σ, p) (SV, FV, BV)
             (MEvAllocN a ℓ len v)
             (state_init_heap a ℓ len SV FV v σ, p) (SV, FV, BV).
  Proof.
    intros. apply MStepAllocN; first done.
    intros. apply not_elem_of_dom.
    by apply fresh_locs_fresh.
  Qed.

End memory.

(** Get the largest time of any message in a given history. *)
Definition max_msg (h : history) : time :=
  max_list (elements (dom (gset time) h)).

(** Convert a [store] to a [view] by taking the largest time for of any message
for each location. We call this the "lub view" b.c., in an actual execution this
view will be the l.u.b. of all the threads views. *)
Definition max_view (heap : store) : view := MaxNat <$> (max_msg <$> heap).

Definition hist_inv lub (hist : history) : Prop :=
  (* Every history has an initial message. *)
  is_Some (hist !! 0) ∧
  (* Every view in every message is included in the lub view. *)
  (map_Forall (λ t msg, msg.(msg_store_view) ⊑ lub) hist).

(* Every store view in every message is included in [lub]. *)
Definition valid_heap_lub lub (s : store) : Prop :=
  map_Forall (λ _ hist, hist_inv lub hist) s.

Definition valid_heap store : Prop := valid_heap_lub (max_view store) store.
