(* This module defines the memory model or the memory subsystem. *)

From stdpp Require Import countable numbers gmap.
From iris.heap_lang Require Import locations.
From iris.algebra Require Import gmap numbers.

From self Require Import extra.
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
    dom (gset loc) (slice_hist p hists) ⊆ dom (gset loc) hists.
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
    dom (gset loc) (slice_of_hist p hists) =
      dom (gset loc) p ∩ dom (gset loc) hists.
  Proof.
    rewrite /slice_of_hist dom_fmap_L dom_map_zip_with_L. done.
  Qed.

  Lemma slice_of_hist_dom_subset p hists :
    dom (gset loc) (slice_of_hist p hists) ⊆ dom (gset loc) hists.
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

Section drop_prefix.
  Context {A : Type}.

  (* Shift everything in [h] down by [t] and remove everything that is below
  [t]. *)
  (* TODO: Consider definition of this that uses filter and map (over keys). *)
  Definition drop_prefix (h : gmap time A) (t : time) : gmap time A :=
    map_fold (λ k v m, if decide (t ≤ k) then <[(k - t) := v]>m else m) ∅ h.

  Lemma drop_prefix_zero h : drop_prefix h 0 = h.
  Proof.
    rewrite /drop_prefix.
    induction h as [|i x m IH] using map_ind; first done.
    rewrite map_fold_insert_L; last done.
    - simpl. rewrite IHh. replace (i - 0) with i by lia. done.
    - intros. simpl. rewrite !Nat.sub_0_r. apply insert_commute. done.
  Qed.

  Lemma drop_prefix_lookup_Some t (a : A) (h : gmap time A) (k : time) :
    drop_prefix h t !! k = Some a →
    h !! (k + t) = Some a.
  Proof.
    (* rewrite /drop_prefix. *)
    (* induction h as [|i x m IH] using map_ind; first done. *)
    (* rewrite map_fold_insert_L; last done. *)
    (* - simpl. rewrite IHh. replace (i - 0) with i by lia. done. *)
    (* - intros. simpl. rewrite !Nat.sub_0_r. apply insert_commute. done. *)
  Admitted.

End drop_prefix.
