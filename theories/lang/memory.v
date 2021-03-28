(* This module defines the memory model or the memory subsystem. *)

From stdpp Require Import countable numbers gmap.
From iris.heap_lang Require Export locations.
From iris.algebra Require Export gmap numbers.

From self.algebra Require Export view.
From self.lang Require Export syntax.

Record message : Type := Msg {
  msg_val : val;
  msg_store_view : view;
  msg_persist_view : view;
}.

Notation thread_view := (view * view * view)%type.

Definition store_view (tv : thread_view) : view := (tv.1).1.
Definition persist_view (tv : thread_view) : view := (tv.1).2.
Definition wb_buffer_view (tv : thread_view) : view := (tv.2).

Global Instance store_view_mono : Proper ((⊑) ==> (⊑)) store_view.
Proof. solve_proper. Qed.
Global Instance persist_view_mono : Proper ((⊑) ==> (⊑)) persist_view.
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
  | MEvRMW ℓ (vOld vNew : val) (* read-modify-write *)
  (* FIXME: Probably also need event for failed RMW. *)
  (* Persistent memory specific. *)
  | MEvWB ℓ
  | MEvFence
  | MEvFenceSync.

  (* Takes a value and creates an initial history for that value. *)
  Definition initial_history P v : history := {[0 := Msg v ∅ P]}.

  (* Convert an array into a store. *)
  Fixpoint heap_array (l : loc) P (vs : list val) : store :=
    match vs with
    | [] => ∅
    | v :: vs' => {[l := initial_history P v]} ∪ heap_array (l +ₗ 1) P vs'
    end.

  Lemma heap_array_lookup (l : loc) P (vs : list val) (ow : history) (k : loc) :
    (heap_array l P vs : store) !! k = Some ow ↔
    (* True ↔ *)
    ∃ j w, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ (ow = {[0 := Msg w ∅ P]}) ∧ vs !! (Z.to_nat j) = (Some w).
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
  | MStepAllocN σ V P B ℓ (len : nat) v p :
     (0 < len)%Z → (* (∀ i, (0 ≤ i)%Z → (i < n)%Z → σ.(heap) !! (l +ₗ i) = None) → *)
     (∀ idx, (0 ≤ idx)%Z → (idx < len)%Z → σ !! (ℓ +ₗ idx) = None) → (* This is a fresh segment of the heap not already in use. *)
     (* V' = <[ ℓ := 0 ]>V → (* V' incorporates the new event in the threads view. *) This may not be needed. *)
     mem_step (σ, p) (V, P, B)
              (MEvAllocN ℓ len v)
              (state_init_heap ℓ len P v σ, p) (V, P, B)
              (* (<[ℓ := {[ 0 := Msg v V' P ]}]>σ, p) (V', P, B) *)
  (* A normal non-atomic load. *)
  | MStepLoad (σ : store) V P B t (ℓ : loc) (v : val) h p :
     σ !! ℓ = Some h →
     msg_val <$> (h !! t) = Some v →
     ((V !!0 ℓ)) ≤ t →
     mem_step (σ, p) (V, P, B)
              (MEvLoad ℓ v)
              (σ, p) (V, P, B)
              (* (σ, p) ((<[ ℓ := t ]>V), P, B) (* This variant includes the timestamp of the loaded msg. *) *)
  (* A normal non-atomic write. *)
  | MStepStore σ V P B t ℓ (v : val) h V' p :
     σ !! ℓ = Some h →
     (h !! t) = None → (* No event exists at t already. *)
     (V !!0 ℓ) < t →
     V' = <[ℓ := MaxNat t]>V → (* V' incorporates the new event in the threads view. *)
     mem_step (σ, p) (V, P, B)
             (MEvStore ℓ v)
             (<[ℓ := <[t := Msg v ∅ P]>h]>σ, p) (V', P, B)
  (* An atomic acquire load. *)
  | MStepLoadAcquire σ V P B t ℓ (v : val) MV MP h p :
     σ !! ℓ = Some h →
     (h !! t) = Some (Msg v MV MP) →
     (V !!0 ℓ) ≤ t →
     mem_step (σ, p) (V, P, B)
              (MEvLoadAcquire ℓ v)
              (σ, p) (V ⊔ MV, P ⊔ MP, B) (* An acquire incorporates both the store view and the persistent view. *)
  (* An atomic release write. *)
  | MStepStoreRelease σ V P B t ℓ (v : val) h V' p :
     σ !! ℓ = Some h →
     (h !! t) = None → (* No event exists at t already. *)
     (V !!0 ℓ) < t →
     V' = <[ℓ := MaxNat t]>V → (* V' incorporates the new event in the threads view. *)
     mem_step (σ, p) (V, P, B)
              (MEvStoreRelease ℓ v)
              (<[ℓ := <[t := Msg v V' P]>h]>σ, p) (V', P, B) (* A release releases both V' and P. *)
  (* Read-modify-write instructions. *)
  | MStepRMW σ ℓ h v MV MP V t V' P P' B p v' :
     σ !! ℓ = Some h →
     (h !! t) = Some (Msg v MV MP) → (* We read an event at time [t]. *)
     (V !!0 ℓ) ≤ t →
     (h !! (t + 1)) = None → (* The next timestamp is available, ensures that no other RMW read this event. *)
     V' = (<[ ℓ := MaxNat (t + 1) ]>(V ⊔ MV)) → (* V' incorporates the new event in the threads view. *)
     P' = P ⊔ MP →
     mem_step (σ, p) (V, P, B)
              (MEvRMW ℓ v v')
              (<[ℓ := <[t := Msg v V' P']>h]>σ, p) (V', P', B)
  (* Write-back instruction. *)
  | MStepWB σ V P B ℓ t h p :
     σ !! ℓ = Some h →
     (V !!0 ℓ) = t → (* An equality here _should_ be fine, the timestamps are only lower bounds anyway? *)
     mem_step (σ, p) (V, P, B)
              (MEvWB ℓ)
              (σ, p) (V, P, <[ℓ := MaxNat t]>B)
  (* Asynchronous fence. *)
  | MStepFence σ V P B p :
     mem_step (σ, p) (V, P, B)
              MEvFence
              (σ, p) (V, P ⊔ B, ∅)
  (* Synchronous fence. *)
  | MStepFenceSync σ V P B p :
     mem_step (σ, p) (V, P, B)
              MEvFenceSync
              (σ, p ⊔ B) (V, P ⊔ B, ∅).

  (* Removes all events from histories after the view. *)
  Definition cut_history p σ : store :=
    map_imap (λ ℓ h, let t' := p !!0 ℓ in Some (filter (λ '(t, ev), t ≤ t') h)) σ.

  Definition consistent_cut p σ : Prop :=
    map_Forall (λ ℓ h, map_Forall (λ _ ev, (msg_persist_view ev) ⊑ p) h) (cut_history p σ).

  (* The crash step is different from the other steps in that it does not depend
  on any current thread. We therefore define it as a separate type. *)
  Inductive crash_step : mem_config → mem_config → Prop :=
  | MCrashStep σ p p' :
     p ⊑ p' →
     consistent_cut p' σ →
     crash_step (σ, p) (cut_history p' σ, p').

  (* It is always possible to allocate a section of memory. *)
  Lemma alloc_fresh v (len : nat) σ p V P B :
    let ℓ := fresh_locs (dom (gset loc) σ) in (* ℓ is directly after the largest allocated location. *)
    (0 < len)%Z →
    mem_step (σ, p) (V, P, B)
             (MEvAllocN ℓ len v)
             (state_init_heap ℓ len P v σ, p) (V, P, B).
  Proof.
    intros. apply MStepAllocN; first done.
    intros. apply not_elem_of_dom.
    by apply fresh_locs_fresh.
  Qed.

End memory.
