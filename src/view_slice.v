(* This module defines the memory model or the memory subsystem. *)

From stdpp Require Import countable numbers gmap.
From iris.heap_lang Require Import locations.
From iris.algebra Require Import gmap numbers.

From self Require Import extra map_extra.
From self.algebra Require Export view.
From self.lang Require Import syntax.

Section map_slice.
  Context {A : Type}.
  Implicit Types (hists : gmap loc (gmap time A)).

  (** A valid slice of a history is a view that for each location specifies a
  timestamp that exists in the history. Note that in this definition the view may
  contain more locations than the history and vice versa. The requirement only
  applies to locations present in both. *)
  Definition valid_slice (V : view) (σ : gmap loc (gmap time A)) :=
    map_Forall (λ ℓ '(MaxNat t, hist), is_Some (hist !! t)) (map_zip V σ).

  Definition slice_hist {A} (V : view) (σ : gmap loc (gmap time A)) :
      gmap loc (option A) :=
    map_zip_with (λ '(MaxNat t) hist, hist !! t) V σ.

End map_slice.

(* For each location in [V] pick the message in the store that it specifies. *)
Definition slice_of_hist {A} (V : view) (σ : gmap loc (gmap time A)) :
    gmap loc (gmap time A) :=
  from_option (λ s, {[ 0 := s ]}) ∅ <$> (slice_hist V σ).

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

  Lemma slice_hist_dom_subset p hists :
    dom (slice_hist p hists) ⊆ dom hists.
  Proof.
    rewrite /slice_of_hist.
    intros l.
    rewrite !elem_of_dom.
    intros [? look].
    apply map_lookup_zip_with_Some in look.
    destruct look as (? & ? & ? & ? & ?).
    eexists _. done.
  Qed.

  Lemma slice_hist_lookup_Some CV hists hist ℓ t s :
    CV !! ℓ = Some (MaxNat t) →
    hists !! ℓ = Some hist →
    hist !! t = Some s →
    slice_hist CV hists !! ℓ = Some (Some s).
  Proof.
    intros ?? eq.
    rewrite /slice_of_hist.
    apply map_lookup_zip_with_Some.
    eexists (MaxNat _), _.
    split_and!; done.
  Qed.

  Lemma slice_hist_lookup_inv CV hists h ℓ :
    valid_slice CV hists →
    slice_hist CV hists !! ℓ = Some h →
    ∃ t hist m,
      CV !! ℓ = Some (MaxNat t) ∧
      hists !! ℓ = Some hist ∧
      hist !! t = Some m ∧
      h = Some m.
  Proof.
    rewrite /slice_of_hist.
    intros val ([t] & hist & hl & cvLook & histsLook)%map_lookup_zip_with_Some.
    eapply map_Forall_lookup_1 in val.
    2: { apply map_lookup_zip_with_Some. eexists _, _. done. }
    destruct val as [a histLook].
    rewrite histLook in hl.
    naive_solver.
  Qed.

  Lemma slice_hist_Some V hists ℓ t hist :
    valid_slice V hists →
    V !! ℓ = Some (MaxNat t) →
    hists !! ℓ = Some hist →
    ∃ (a : A), hist !! t = Some a ∧
      slice_hist V hists !! ℓ = Some (Some a).
  Proof.
    intros val vLook histsLook.
    eapply valid_slice_lookup in val as [a look]; try done.
    exists a. split; first done.
    eapply slice_hist_lookup_Some; done.
  Qed.

  Lemma slice_of_hist_None CV hists ℓ :
    slice_of_hist CV hists !! ℓ = None ↔
    CV !! ℓ = None ∨ hists !! ℓ = None.
  Proof.
    rewrite /slice_of_hist. rewrite map_fmap_zip_with.
    apply map_lookup_zip_with_None.
  Qed.

  Lemma slice_of_hist_dom p hists :
    dom (slice_of_hist p hists) =
      dom p ∩ dom hists.
  Proof.
    rewrite /slice_of_hist dom_fmap_L dom_map_zip_with_L. done.
  Qed.

  Lemma slice_of_hist_dom_subset p hists :
    dom (slice_of_hist p hists) ⊆ dom hists.
  Proof. rewrite /slice_of_hist dom_fmap_L. apply slice_hist_dom_subset. Qed.

  Lemma slice_of_hist_lookup_Some CV hists hist ℓ t s :
    CV !! ℓ = Some (MaxNat t) →
    hists !! ℓ = Some hist →
    hist !! t = Some s →
    slice_of_hist CV hists !! ℓ = Some {[0 := s]}.
  Proof.
    intros ?? eq. rewrite /slice_of_hist lookup_fmap.
    erewrite slice_hist_lookup_Some; done.
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
    intros val (? & ? & slice)%lookup_fmap_Some.
    pose proof (slice_hist_lookup_inv _ _ _ _ val slice).
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
    dom hists1 = dom hists2 →
    (∀ ℓ h1 h2, hists1 !! ℓ = Some h1 → hists2 !! ℓ = Some h2 → dom h1 = dom h2) →
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

Section drop_prefix.
  Context {A : Type}.

  (* Shift everything in [h] down by [t] and remove everything that is below
  [t]. *)
  Definition drop_prefix (h : gmap time A) (t : time) : gmap time A :=
    map_fold (λ k v m, if decide (t ≤ k) then <[(k - t) := v]>m else m) ∅ h.

  Lemma drop_prefix_lookup t h k :
    drop_prefix h t !! k = h !! (k + t).
  Proof.
    rewrite /drop_prefix.
    apply (map_fold_ind (λ mr h, mr !! k = h !! (k + t))); first done.
    intros ????? IH.
    destruct (decide (i = k + t)) as [eq|neq].
    - rewrite decide_True; last lia.
      rewrite -eq.
      assert (i - t = k) as -> by lia.
      rewrite !lookup_insert.
      done.
    - rewrite lookup_insert_ne; last done. rewrite -IH.
      destruct (decide (t ≤ i)); last done.
      rewrite lookup_insert_ne; [done|lia].
  Qed.

  Lemma drop_prefix_zero h : drop_prefix h 0 = h.
  Proof.
    apply map_eq. intros ?. rewrite drop_prefix_lookup.
    replace (i + 0) with i by lia.
    done.
  Qed.

  Lemma drop_prefix_lookup_Some t (a : A) (h : gmap time A) (k : time) :
    drop_prefix h t !! k = Some a ↔
    h !! (k + t) = Some a.
  Proof. rewrite drop_prefix_lookup. done. Qed.

  Lemma drop_prefix_lookup_Some_2 t (a : A) h k :
    h !! (k + t) = Some a →
    drop_prefix h t !! k = Some a.
  Proof. apply drop_prefix_lookup_Some. Qed.

  Lemma drop_prefix_insert t1 t2 a h :
    <[t2 := a]>(drop_prefix h t1) = drop_prefix (<[t2 + t1 := a]> h) t1.
  Proof.
    apply map_eq. intros i. rewrite drop_prefix_lookup.
    destruct (decide (i = t2)) as [->|neq].
    - rewrite !lookup_insert. done.
    - rewrite lookup_insert_ne; last congruence.
      rewrite lookup_insert_ne; last lia.
      apply drop_prefix_lookup.
  Qed.

  Lemma drop_prefix_drop_above x m t (a : A) :
   drop_prefix (drop_above x m) x !! t = Some a →
   t = 0 ∧ m !! (t + x) = Some a.
  Proof.
    intros look%drop_prefix_lookup_Some.
    apply map_filter_lookup_Some in look as (? & ?).
    split; [lia | done].
  Qed.

End drop_prefix.

Lemma drop_prefix_fmap {A B} (f : A → B) h t :
  drop_prefix (f <$> h) t = f <$> (drop_prefix h t).
Proof.
  apply map_eq. intros ?.
  rewrite lookup_fmap.
  rewrite !drop_prefix_lookup.
  apply lookup_fmap.
Qed.

Definition offsets_add : gmap loc nat → view → gmap loc nat :=
  map_zip_with (λ (n : nat) '(MaxNat m), n + m).

Lemma valid_slice_drop_prefix {A} CV (h : gmap loc (gmap nat A)) offsets :
  valid_slice CV (map_zip_with drop_prefix h offsets) ↔
    valid_slice (MaxNat <$> offsets_add offsets CV) h.
Proof.
  rewrite /valid_slice.
  split.
  - intros H ℓ [[t] hist] (? & ? & [= <- <-] & look & ?)%map_lookup_zip_with_Some.
    apply lookup_fmap_Some in look as (? & [= ->] & look).
    rewrite /offsets_add.
    apply map_lookup_zip_with_Some in look as (tO & [cT] & -> & ? & cvLook).
    eassert _ as temp. {
      eapply map_Forall_lookup_1; first apply H.
      apply map_lookup_zip_with_Some.
      eexists _, _. split; first done.
      split; first done.
      apply map_lookup_zip_with_Some.
      eexists _, _. done. }
    destruct temp as [? look].
    rewrite drop_prefix_lookup in look.
    setoid_rewrite (comm Nat.add) in look.
    naive_solver.
  - intros H ℓ [[t] hist] (? & ? & [= <- <-] & cvLook & look)%map_lookup_zip_with_Some.
    apply map_lookup_zip_with_Some in look as (? & ? & -> & ? & ?).
    eassert _ as temp. {
      eapply map_Forall_lookup_1; first apply H.
      apply map_lookup_zip_with_Some.
      eexists _, _. split; first done.
      split; last done.
      apply lookup_fmap_Some.
      eexists _. split; first done.
      apply map_lookup_zip_with_Some.
      eexists _, _. split; first done. done. }
    destruct temp as [? look].
    eexists _. rewrite drop_prefix_lookup. rewrite (comm Nat.add). done.
Qed.

Definition drop_all_above {A} (offsets : gmap loc nat)
           (abs_hists : gmap loc (gmap time A)) :=
  map_zip_with (λ offset h, drop_above offset h) offsets abs_hists.

Lemma drop_all_above_lookup_Some {A} (offsets : gmap loc nat)
      (abs_hists : gmap loc (gmap time A)) ℓ h :
  drop_all_above offsets abs_hists !! ℓ = Some h →
  ∃ offset hist,
    h = drop_above offset hist ∧
    offsets !! ℓ = Some offset ∧
    abs_hists !! ℓ = Some hist.
Proof. apply map_lookup_zip_with_Some. Qed.

Section drop_all_above.
  Context {A : Type}.
  Implicit Types (hists : gmap loc (gmap time A)).

  Lemma slice_of_hist_drop CV hists (offsets : gmap loc nat) :
    slice_of_hist CV (map_zip_with drop_prefix hists offsets) =
    map_zip_with drop_prefix (drop_all_above (offsets_add offsets CV) hists) (offsets_add offsets CV).
  Proof.
    apply map_eq. intros ℓ.
    rewrite /slice_of_hist. rewrite lookup_fmap. rewrite /slice_hist.
    rewrite map_lookup_zip_with.
    rewrite map_lookup_zip_with.
    rewrite map_lookup_zip_with.
    rewrite /drop_all_above.
    rewrite map_lookup_zip_with.
    rewrite /offsets_add.
    rewrite map_lookup_zip_with.

    destruct (CV !! ℓ);
      destruct (offsets !! ℓ);
      destruct (hists !! ℓ); simpl; try reflexivity.
    f_equiv.
    destruct m as [t].
    apply map_eq. intros i.
    rewrite drop_prefix_lookup.
    rewrite drop_prefix_lookup.

    destruct (decide (i = 0)) as [->|neq].
    * rewrite drop_above_lookup_t.
      rewrite Nat.add_0_l Nat.add_comm.
      destruct (g !! (n + t)) eqn:look; done.
    * rewrite drop_above_lookup_gt; last lia.
      destruct (g !! (t + n)) eqn:look; simpl;
        rewrite ?lookup_singleton_ne; done.
  Qed.

  Lemma map_zip_with_drop_prefix_fmap (f : A → A) histss (offsets : gmap loc nat) :
    map_zip_with drop_prefix ((λ hist, f <$> hist) <$> histss) offsets =
      (λ hist, f <$> hist) <$> (map_zip_with drop_prefix histss offsets).
  Proof.
    rewrite map_zip_with_fmap_1.
    rewrite map_fmap_zip_with.
    (* We can't rewrite under the binder with [drop_prefix_fmap] :'( for some
    reason. So we get rid of the binder. *)
    apply map_eq. intros i.
    rewrite !map_lookup_zip_with.
    destruct (histss !! i); destruct (offsets !! i); simpl; try done.
    rewrite drop_prefix_fmap.
    done.
  Qed.

End drop_all_above.
