(* This module defines the memory model or the memory subsystem. *)

From stdpp Require Import countable numbers gmap.
From iris.heap_lang Require Import locations.
From iris.algebra Require Import gmap numbers.

From self Require Import extra.
From self.algebra Require Export view.
From self.lang Require Import syntax.

(** A valid slice of a history is a view that for each location specifies a
timestamp that exists in the history. Note that in this definition the view may
contain more locations than the history and vice versa. The requirement only
applies to locations present in both. *)
Definition valid_slice {A} (V : view) (σ : gmap loc (gmap time A)) :=
  map_Forall (λ ℓ '(MaxNat t, hist), is_Some (hist !! t)) (map_zip V σ).

(* For each location in [V] pick the message in the store that it specifies. *)
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

  Lemma valid_slice_lookup V ℓ t hists hist :
    valid_slice V hists →
    V !! ℓ = Some (MaxNat t) →
    hists !! ℓ = Some hist →
    is_Some (hist !! t).
  Proof.
    rewrite /valid_slice.
    intros val vLook histsLook.
    eapply map_Forall_lookup_1 in val.
    2: { apply map_lookup_zip_with_Some. eexists _, _. done. }
    done.
  Qed.

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

  Lemma slice_of_hist_lookup_Some CV hists hist ℓ t s :
    CV !! ℓ = Some (MaxNat t) →
    hists !! ℓ = Some hist →
    hist !! t = Some s →
    slice_of_hist CV hists !! ℓ = Some {[0 := s]}.
  Proof.
    intros ?? eq.
    rewrite /slice_of_hist.
    apply map_lookup_zip_with_Some.
    eexists (MaxNat _), _.
    split_and!; try done.
    rewrite eq.
    done.
  Qed.

  Lemma slice_of_hist_lookup_inv CV hists h ℓ :
    valid_slice CV hists →
    slice_of_hist CV hists !! ℓ = Some h →
    ∃ t hist m,
      CV !! ℓ = Some (MaxNat t) ∧
      hists !! ℓ = Some hist ∧
      hist !! t = Some m ∧
      h = {[ 0 := m ]} .
  Proof.
    rewrite /slice_of_hist.
    intros val ([t] & hist & hl & cvLook & histsLook)%map_lookup_zip_with_Some.
    eapply map_Forall_lookup_1 in val.
    2: { apply map_lookup_zip_with_Some. eexists _, _. done. }
    destruct val as [a histLook].
    rewrite histLook in hl.
    naive_solver.
  Qed.

  Lemma slice_of_hist_Some V hists ℓ t hist :
    valid_slice V hists →
    V !! ℓ = Some (MaxNat t) →
    hists !! ℓ = Some hist →
    ∃ (a : A), hist !! t = Some a ∧
      slice_of_hist V hists !! ℓ = Some {[ 0 := a ]}.
  Proof.
    intros val vLook histsLook.
    eapply valid_slice_lookup in val as [a look]; try done.
    exists a. split; first done.
    eapply slice_of_hist_lookup_Some; done.
  Qed.

  Lemma valid_slice_mono_l V hists1 hists2 :
    hists1 ⊆ hists2 → valid_slice V hists2 → valid_slice V hists1.
  Proof.
    intros sub.
    apply map_Forall_subseteq.
    apply map_zip_with_mono; done.
  Qed.

  Lemma valid_slice_transfer {B} V hists1 (hists2 : gmap loc (gmap time B)) :
    dom (gset _) hists1 = dom _ hists2 →
    (∀ ℓ h1 h2, hists1 !! ℓ = Some h1 → hists2 !! ℓ = Some h2 → dom (gset _) h1 = dom _ h2) →
    valid_slice V hists1 → valid_slice V hists2.
  Proof.
    intros eq look val.
    intros ℓ [[t] hist2].
    intros [vLook ?]%map_lookup_zip_Some.
    assert (is_Some (hists1 !! ℓ)) as [hist1 ?].
    { apply elem_of_dom. rewrite eq. apply elem_of_dom. done. }
    apply elem_of_dom.
    erewrite <- look; try done.
    apply elem_of_dom.
    eapply valid_slice_lookup in val; done.
  Qed.

End slice_of_hist_props.

Record message : Type := Msg {
  msg_val : val;
  msg_store_view : view;
  msg_persist_view : view;
  msg_persisted_after_view : view;
}.

Canonical Structure messageO := leibnizO message.

Notation thread_view := (view * view * view)%type.

Instance thread_view_bottom : Bottom thread_view := ε.

(* Convert a message to a thread_view corresponding to what is stored in the
message. *)
Definition msg_to_tv (m : message) : thread_view :=
  (m.(msg_store_view), m.(msg_persist_view), ∅).

Notation store_view tv := (tv.1).1.
Notation flush_view tv := (tv.1).2.
Notation wb_buffer_view tv := (tv.2).

Notation history := (gmap time message).

Notation store := (gmap loc history).

Definition mem_config : Type := store * view.

Section consistent_cut.

  (* Removes all messages from [hist] after [t]. *)
  Definition cut_history t (hist : history) : history :=
    filter (λ '(t', ev), t' ≤ t) hist.

  Definition discard_msg_views (msg : message) : message :=
    Msg msg.(msg_val) ∅ ∅ ∅.

  (* For each location in [p] pick the message in the store that it specifies. *)
  Definition slice_of_store (p : view) (σ : store) : store :=
    (λ (hist : gmap _ _), discard_msg_views <$> hist) <$> (slice_of_hist p σ).

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
    rewrite dom_map_zip_with.
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

  Implicit Types (v : val) (ℓ : loc) (σ : store) (p : view).

  Inductive mem_event : Type :=
  | MEvAllocN (a : memory_access) ℓ (len : nat) v
  | MEvLoad ℓ v
  | MEvStore ℓ v
  (* Acquire/release weak memory events. *)
  | MEvLoadAcquire ℓ v
  | MEvStoreRelease ℓ v
  (* RMW are special *)
  | MEvRMW ℓ (vExp vNew : val) (* read-modify-write *)
  | MEvLoadEx ℓ (vExp : val) (* for failed RMWs *)
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
    ∃ j w, (0 ≤ j)%Z ∧ k = ℓ +ₗ j ∧ (ow = initial_history a SV PV w) ∧ vs !! (Z.to_nat j) = (Some w).
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
  | MStepAllocN a σ SV PV BV ℓ (len : nat) v p :
     (0 < len)%Z → (* (∀ i, (0 ≤ i)%Z → (i < n)%Z → σ.(heap) !! (ℓ +ₗ i) = None) → *)
     (∀ idx, (0 ≤ idx)%Z → (idx < len)%Z → σ !! (ℓ +ₗ idx) = None) → (* This is a fresh segment of the heap not already in use. *)
     (* V' = <[ ℓ := 0 ]>SV → (* V' incorporates the new event in the threads view. *) This may not be needed. *)
     mem_step (σ, p) (SV, PV, BV)
              (MEvAllocN a ℓ len v)
              (state_init_heap a ℓ len SV PV v σ, p) (SV, PV, BV)
  (* A normal non-atomic load. *)
  | MStepLoad (σ : store) SV PV BV t (ℓ : loc) (v : val) h p :
     σ !! ℓ = Some h →
     msg_val <$> (h !! t) = Some v →
     (SV !!0 ℓ) ≤ t →
     mem_step (σ, p) (SV, PV, BV)
              (MEvLoad ℓ v)
              (σ, p) (SV, PV, BV)
              (* (σ, p) ((<[ ℓ := t ]>SV), PV, BV) (* This variant includes the timestamp of the loaded msg. *) *)
  (* An atomic acquire load. *)
  | MStepLoadAcquire σ SV PV BV t ℓ (v : val) MV MP _MP h p :
     σ !! ℓ = Some h →
     (h !! t) = Some (Msg v MV MP _MP) →
     (SV !!0 ℓ) ≤ t →
     mem_step (σ, p) (SV, PV, BV)
              (MEvLoadAcquire ℓ v)
              (σ, p) (SV ⊔ MV, PV, BV ⊔ MP) (* An acquire incorporates both the store view and the persistent view. *)
  (* A normal non-atomic write. *)
  | MStepStore σ SV PV BV t ℓ (v : val) h V' p :
     σ !! ℓ = Some h →
     (h !! t) = None → (* No event exists at t already. *)
     (SV !!0 ℓ) < t →
     V' = <[ℓ := MaxNat t]>SV → (* V' incorporates the new event in the threads view. *)
     mem_step (σ, p) (SV, PV, BV)
             (MEvStore ℓ v)
             (<[ℓ := <[t := Msg v ∅ ∅ PV]>h]>σ, p) (V', PV, BV)
  (* An atomic release write. *)
  | MStepStoreRelease σ SV PV BV t ℓ (v : val) h V' p :
     σ !! ℓ = Some h →
     (h !! t) = None → (* No event exists at t already. *)
     (SV !!0 ℓ) < t →
     V' = <[ℓ := MaxNat t]>SV → (* V' incorporates the new event in the threads view. *)
     mem_step (σ, p) (SV, PV, BV)
              (MEvStoreRelease ℓ v)
              (<[ℓ := <[t := Msg v V' PV PV]>h]>σ, p) (V', PV, BV) (* A release releases both V' and PV. *)
  (* Read-modify-write instructions. *)
  | MStepRMW σ ℓ h v MV MP SV t S' PV P' BV p v' _MP :
     σ !! ℓ = Some h →
     (SV !!0 ℓ) ≤ t →
     (h !! t) = Some (Msg v MV MP _MP) → (* We read an event at time [t]. *)
     (* All values that we could have reads are comparable to [v]. *)
     (∀ t' msg, SV !!0 ℓ ≤ t' → h !! t' = Some msg → vals_compare_safe msg.(msg_val) v) →
     (h !! (t + 1)) = None → (* The next timestamp is available, ensures that no other RMW read this event. *)
     S' = (<[ ℓ := MaxNat (t + 1) ]>(SV ⊔ MV)) → (* S' incorporates the new event in the threads view. *)
     P' = PV ⊔ MP →
     mem_step (σ, p) (SV, PV, BV)
              (MEvRMW ℓ v v')
              (<[ℓ := <[t := Msg v S' P' P']>h]>σ, p) (S', PV, BV ⊔ MP)
  | MStepRMWFail σ SV PV BV t ℓ (v : val) MV MP _MP h p :
     σ !! ℓ = Some h →
     (h !! t) = Some (Msg v MV MP _MP) →
     (SV !!0 ℓ) ≤ t →
     (∀ t' msg, SV !!0 ℓ ≤ t' → h !! t' = Some msg → vals_compare_safe msg.(msg_val) v) →
     mem_step (σ, p) (SV, PV, BV)
              (MEvLoadEx ℓ v)
              (σ, p) (SV ⊔ MV, PV, BV ⊔ MP) (* An acquire incorporates both the store view and the persistent view. *)
  (* Write-back instruction. *)
  | MStepFlush σ SV PV BV ℓ t p :
     (* σ !! ℓ = Some h → *)
     (SV !!0 ℓ) = t → (* An equality here is fine, the timestamps are only lower bounds anyway. *)
     mem_step (σ, p) (SV, PV, BV)
              (MEvFlush ℓ)
              (σ, p) (SV, PV, {[ℓ := MaxNat t]} ⊔ BV)
  (* Asynchronous fence. *)
  | MStepFence σ SV PV BV p :
     mem_step (σ, p) (SV, PV, BV)
              MEvFence
              (σ, p) (SV, PV ⊔ BV, BV)
  (* Synchronous fence. *)
  | MStepFenceSync σ SV PV BV p :
     mem_step (σ, p) (SV, PV, BV)
              MEvFenceSync
              (σ, p ⊔ BV) (SV, PV ⊔ BV, BV).

  (* The crash step is different from the other steps in that it does not depend
  on any current thread. We therefore define it as a separate type. *)
  Inductive crash_step : mem_config → mem_config → Prop :=
  | MCrashStep σ p p' :
     p ⊑ p' →
     consistent_cut p' σ →
     crash_step (σ, p) (slice_of_store p' σ, view_to_zero p').

  (* It is always possible to allocate a section of memory. *)
  Lemma alloc_fresh v (len : nat) a σ p SV PV BV :
    let ℓ := fresh_locs (dom (gset loc) σ) in (* ℓ is directly after the largest allocated location. *)
    (0 < len)%Z →
    mem_step (σ, p) (SV, PV, BV)
             (MEvAllocN a ℓ len v)
             (state_init_heap a ℓ len SV PV v σ, p) (SV, PV, BV).
  Proof.
    intros. apply MStepAllocN; first done.
    intros. apply not_elem_of_dom.
    by apply fresh_locs_fresh.
  Qed.

End memory.

(* A few lattice rules for thread_view. *)

Lemma thread_view_sqsubseteq_antisym (TV1 TV2 : thread_view) :
  TV1 ⊑ TV2 → TV2 ⊑ TV1 → TV1 = TV2.
Proof.
  destruct TV1 as [[??]?]. destruct TV2 as [[??]?]. intros [[??] ?] [[??] ?].
  rewrite 2!pair_equal_spec.
  auto using view_sqsubseteq_antisym.
Qed.

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
