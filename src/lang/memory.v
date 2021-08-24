(* This module defines the memory model or the memory subsystem. *)

From stdpp Require Import countable numbers gmap.
From iris.heap_lang Require Export locations.
From iris.algebra Require Export gmap numbers.

From self Require Import extra.
From self.algebra Require Export view.
From self.lang Require Export syntax.

Definition valid_slice {A} (V : view) (σ : gmap loc (gmap time A)) :=
  map_Forall (λ ℓ hist, ∃ t, V !! ℓ = Some (MaxNat t) ∧ is_Some (hist !! t)) σ.

(* For each location in [p] pick the message in the store that it specifies. *)
Definition slice_of_hist {A} (V : view) (σ : gmap loc (gmap time A)) :
  gmap loc (gmap time A) :=
  map_zip_with
    (λ '(MaxNat t) hist,
      match hist !! t with
        Some s => {[ 0 := s ]}
      | None => ∅ (* The None branch here is never taken. *)
      end)
    V σ.

Section slice_of_hist_props.
  Context {A : Type}.
  Implicit Types (hists : gmap loc (gmap time A)).

  Lemma slice_of_hist_dom_subset p hists :
    dom (gset loc) (slice_of_hist p hists) ⊆ dom (gset loc) hists.
  Proof.
    rewrite /slice_of_hist.
    intros l.
    rewrite !elem_of_dom.
    intros [? look].
    apply map_lookup_zip_with_Some in look.
    destruct look as (? & ? & ? & ? & ?).
    eexists _. done.
  Qed.

End slice_of_hist_props.

Record message : Type := Msg {
  msg_val : val;
  msg_store_view : view;
  msg_persist_view : view;
  msg_persisted_after_view : view;
}.

Notation thread_view := (view * view * view)%type.

(* Convert a message to a thread_view corresponding to what is stored in the
message. *)
Definition msg_to_tv (m : message) : thread_view :=
  (m.(msg_store_view), m.(msg_persist_view), ∅).

Definition store_view (tv : thread_view) : view := (tv.1).1.
Definition flush_view (tv : thread_view) : view := (tv.1).2.
Definition wb_buffer_view (tv : thread_view) : view := (tv.2).

Global Instance store_view_mono : Proper ((⊑) ==> (⊑)) store_view.
Proof. solve_proper. Qed.
Global Instance flush_view_mono : Proper ((⊑) ==> (⊑)) flush_view.
Proof. solve_proper. Qed.
Global Instance wb_buffer_view_mono : Proper ((⊑) ==> (⊑)) wb_buffer_view.
Proof. solve_proper. Qed.

Notation history := (gmap time message).

Notation store := (gmap loc history).

Definition mem_config : Type := store * view.

Section memory.

  Implicit Types (v : val) (ℓ : loc) (σ : store) (p : view).

  Inductive mem_event : Type :=
  | MEvAllocN ℓ (len : nat) v
  | MEvLoad ℓ v
  | MEvStore ℓ v
  (* Acquire/release weak memory events. *)
  | MEvLoadAcquire ℓ v
  | MEvStoreRelease ℓ v
  (* RMW are special *)
  | MEvRMW ℓ (vExp vNew : val) (* read-modify-write *)
  | MEvLoadEx ℓ (vExp : val) (* for failed RMWs *)
  (* Persistent memory specific. *)
  | MEvWB ℓ
  | MEvFence
  | MEvFenceSync.

  (* Takes a value and creates an initial history for that value. *)
  Definition initial_history P v : history := {[0 := Msg v ∅ ∅ P]}.

  (* Convert an array into a store. *)
  Fixpoint heap_array (l : loc) P (vs : list val) : store :=
    match vs with
    | [] => ∅
    | v :: vs' => {[ l := initial_history P v ]} ∪ heap_array (l +ₗ 1) P vs'
    end.

  Lemma heap_array_lookup (l : loc) P (vs : list val) (ow : history) (k : loc) :
    (heap_array l P vs : store) !! k = Some ow ↔
    (* True ↔ *)
    ∃ j w, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ (ow = {[0 := Msg w ∅ ∅ P]}) ∧ vs !! (Z.to_nat j) = (Some w).
  Proof.
    revert k l; induction vs as [|v' vs IH]=> l' l /=.
    { rewrite lookup_empty. naive_solver lia. }
    rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
    - intros [[-> ?] | (Hl & j & w & ? & -> & -> & ?)].
      { eexists 0, _. rewrite loc_add_0. naive_solver lia. }
      eexists (1 + j)%Z, _. rewrite loc_add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
    - intros (j & w & ? & -> & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
      { rewrite loc_add_0; eauto. }
      right. split.
      { rewrite -{1}(loc_add_0 l). intros ?%(inj (loc_add _)); lia. }
      assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
      { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
      rewrite Hj /= in Hil.
      eexists (j - 1)%Z, _. rewrite loc_add_assoc Z.add_sub_assoc Z.add_simpl_l.
      auto with lia.
  Qed.

  Lemma heap_array_map_disjoint (h : gmap loc history) P (l : loc) (vs : list val) :
    (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
    (heap_array l P vs) ##ₘ h.
  Proof.
    intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
    intros (j&w&?&->&?&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
    move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
  Qed.

  (* Initializes a region of the memory starting at [ℓ] *)
  Definition state_init_heap (ℓ : loc) (n : nat) P (v : val) (σ : store) : store :=
    heap_array ℓ P (replicate n v) ∪ σ.

  (* Small-step reduction steps on the memory. *)

  Inductive mem_step : mem_config → thread_view → mem_event → mem_config → thread_view → Prop :=
  (* Allocating a new location. *)
  | MStepAllocN σ SV P B ℓ (len : nat) v p :
     (0 < len)%Z → (* (∀ i, (0 ≤ i)%Z → (i < n)%Z → σ.(heap) !! (l +ₗ i) = None) → *)
     (∀ idx, (0 ≤ idx)%Z → (idx < len)%Z → σ !! (ℓ +ₗ idx) = None) → (* This is a fresh segment of the heap not already in use. *)
     (* V' = <[ ℓ := 0 ]>SV → (* V' incorporates the new event in the threads view. *) This may not be needed. *)
     mem_step (σ, p) (SV, P, B)
              (MEvAllocN ℓ len v)
              (state_init_heap ℓ len P v σ, p) (SV, P, B)
              (* (<[ℓ := {[ 0 := Msg v V' P ]}]>σ, p) (V', P, B) *)
  (* A normal non-atomic load. *)
  | MStepLoad (σ : store) SV P B t (ℓ : loc) (v : val) h p :
     σ !! ℓ = Some h →
     msg_val <$> (h !! t) = Some v →
     ((SV !!0 ℓ)) ≤ t →
     mem_step (σ, p) (SV, P, B)
              (MEvLoad ℓ v)
              (σ, p) (SV, P, B)
              (* (σ, p) ((<[ ℓ := t ]>SV), P, B) (* This variant includes the timestamp of the loaded msg. *) *)
  (* An atomic acquire load. *)
  | MStepLoadAcquire σ SV P B t ℓ (v : val) MV MP _MP h p :
     σ !! ℓ = Some h →
     (h !! t) = Some (Msg v MV MP _MP) →
     (SV !!0 ℓ) ≤ t →
     mem_step (σ, p) (SV, P, B)
              (MEvLoadAcquire ℓ v)
              (σ, p) (SV ⊔ MV, P, B ⊔ MP) (* An acquire incorporates both the store view and the persistent view. *)
  (* A normal non-atomic write. *)
  | MStepStore σ SV P B t ℓ (v : val) h V' p :
     σ !! ℓ = Some h →
     (h !! t) = None → (* No event exists at t already. *)
     (SV !!0 ℓ) < t →
     V' = <[ℓ := MaxNat t]>SV → (* V' incorporates the new event in the threads view. *)
     mem_step (σ, p) (SV, P, B)
             (MEvStore ℓ v)
             (<[ℓ := <[t := Msg v ∅ ∅ P]>h]>σ, p) (V', P, B)
  (* An atomic release write. *)
  | MStepStoreRelease σ SV P B t ℓ (v : val) h V' p :
     σ !! ℓ = Some h →
     (h !! t) = None → (* No event exists at t already. *)
     (SV !!0 ℓ) < t →
     V' = <[ℓ := MaxNat t]>SV → (* V' incorporates the new event in the threads view. *)
     mem_step (σ, p) (SV, P, B)
              (MEvStoreRelease ℓ v)
              (<[ℓ := <[t := Msg v V' P P]>h]>σ, p) (V', P, B) (* A release releases both V' and P. *)
  (* Read-modify-write instructions. *)
  | MStepRMW σ ℓ h v MV MP S t S' P P' B p v' _MP :
     σ !! ℓ = Some h →
     (S !!0 ℓ) ≤ t →
     (h !! t) = Some (Msg v MV MP _MP) → (* We read an event at time [t]. *)
     (* All values that we could have reads are comparable to [v]. *)
     (∀ t' msg, S !!0 ℓ ≤ t' → h !! t' = Some msg → vals_compare_safe msg.(msg_val) v) →
     (h !! (t + 1)) = None → (* The next timestamp is available, ensures that no other RMW read this event. *)
     S' = (<[ ℓ := MaxNat (t + 1) ]>(S ⊔ MV)) → (* S' incorporates the new event in the threads view. *)
     P' = P ⊔ MP →
     mem_step (σ, p) (S, P, B)
              (MEvRMW ℓ v v')
              (<[ℓ := <[t := Msg v S' P' P']>h]>σ, p) (S', P, B ⊔ MP)
  | MStepRMWFail σ S P B t ℓ (v : val) MV MP _MP h p :
     σ !! ℓ = Some h →
     (h !! t) = Some (Msg v MV MP _MP) →
     (S !!0 ℓ) ≤ t →
     (∀ t' msg, S !!0 ℓ ≤ t' → h !! t' = Some msg → vals_compare_safe msg.(msg_val) v) →
     mem_step (σ, p) (S, P, B)
              (MEvLoadEx ℓ v)
              (σ, p) (S ⊔ MV, P, B ⊔ MP) (* An acquire incorporates both the store view and the persistent view. *)
  (* Write-back instruction. *)
  | MStepWB σ SV P B ℓ t p :
     (* σ !! ℓ = Some h → *)
     (SV !!0 ℓ) = t → (* An equality here is fine, the timestamps are only lower bounds anyway. *)
     mem_step (σ, p) (SV, P, B)
              (MEvWB ℓ)
              (σ, p) (SV, P, <[ℓ := MaxNat t]>B)
  (* Asynchronous fence. *)
  | MStepFence σ SV P B p :
     mem_step (σ, p) (SV, P, B)
              MEvFence
              (σ, p) (SV, P ⊔ B, B)
  (* Synchronous fence. *)
  | MStepFenceSync σ SV P B p :
     mem_step (σ, p) (SV, P, B)
              MEvFenceSync
              (σ, p ⊔ B) (SV, P ⊔ B, B).

  (* Removes all messages from [hist] after [t]. *)
  Definition cut_history t (hist : history) : history :=
    filter (λ '(t', ev), t' ≤ t) hist.

  Definition discard_msg_views (msg : message) : message :=
    Msg msg.(msg_val) ∅ ∅ ∅.

  (* For each location in [p] pick the message in the store that it specifies. *)
  Definition slice_of_store (p : view) (σ : store) : store :=
    (λ (hist : gmap _ _), discard_msg_views <$> hist) <$> (slice_of_hist p σ).

  (* Note: This could be defined with the help of [valid_slice]. *)
  Definition consistent_cut (p : view) (σ : store) : Prop :=
    map_Forall
      (λ ℓ '(MaxNat t),
       ∃ hist msg, σ !! ℓ = Some hist ∧
                   hist !! t = Some msg ∧
                   map_Forall (λ _ msg', msg'.(msg_persisted_after_view) ⊑ p)
                              (cut_history t hist))
      p.

  (* The crash step is different from the other steps in that it does not depend
  on any current thread. We therefore define it as a separate type. *)
  Inductive crash_step : mem_config → mem_config → Prop :=
  | MCrashStep σ p p' :
     p ⊑ p' →
     consistent_cut p' σ →
     crash_step (σ, p) (slice_of_store p' σ, view_to_zero p').

  (* It is always possible to allocate a section of memory. *)
  Lemma alloc_fresh v (len : nat) σ p SV P B :
    let ℓ := fresh_locs (dom (gset loc) σ) in (* ℓ is directly after the largest allocated location. *)
    (0 < len)%Z →
    mem_step (σ, p) (SV, P, B)
             (MEvAllocN ℓ len v)
             (state_init_heap ℓ len P v σ, p) (SV, P, B).
  Proof.
    intros. apply MStepAllocN; first done.
    intros. apply not_elem_of_dom.
    by apply fresh_locs_fresh.
  Qed.

  (* if [p] is a consistent cut of [σ] then the domain of [p] is included in
  [σ]. Intuitively, the recovered locations where all in the heap. *)
  Lemma consistent_cut_subseteq_dom p σ :
    consistent_cut p σ → dom (gset _) p ⊆ dom _ σ.
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
    rewrite -!not_elem_of_dom. rewrite /slice_of_store.
    rewrite dom_fmap.
    rewrite /slice_of_hist.
    rewrite map_zip_with_dom.
    intros ?%consistent_cut_subseteq_dom. set_solver.
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
    intros ([t'] & h & -> & ? & ?)%map_lookup_zip_with_Some histLook.
    exists t', h.
    destruct (h !! t') as [|m]; last naive_solver.
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
    intros ([t] & h & eq & ? & ?)%map_lookup_zip_with_Some.
    exists t, h.
    split_and!; [done | done |].
    destruct (h !! t) as [|m]; last done.
    rewrite map_fmap_singleton in eq.
    destruct msg, m.
    by simplify_eq.
  Qed.

End memory.

(* A few lattice rules for thread_view. *)

Lemma thread_view_le_l (tv1 tv2 : thread_view) : tv1 ⊑ tv1 ⊔ tv2.
Proof.
  destruct tv1 as [[??]?], tv2 as [[??]?].
  repeat split; apply view_le_l.
Qed.

Lemma thread_view_le_r (tv1 tv2 : thread_view) : tv1 ⊑ tv2 ⊔ tv1.
Proof.
  destruct tv1 as [[??]?], tv2 as [[??]?].
  repeat split; apply view_le_r.
Qed.
