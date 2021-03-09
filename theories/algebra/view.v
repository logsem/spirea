From stdpp Require Import countable numbers gmap.
From iris.heap_lang Require Export locations.
From iris.algebra Require Import auth gmap numbers.

Notation time := nat.

Notation view := (gmap loc time).

Instance join_view : Join view := (union_with (λ (x1 x2 : nat), Some (x1 `max` x2))).

Instance subseteq_view : SqSubsetEq view :=
  λ v w, ∀ k t, v !! k = Some t → ∃ t', w !! k = Some t' ∧ t ≤ t'.

Lemma view_lt (V W : view) : V ⊑ W ↔ ∃ V', V ⊔ V' = W.
Proof.
Admitted.

Infix "!!0" := (λ m i, default 0 (m !! i)) (at level 80).

(* Resource algebra for views. *)
Definition viewUR := gmapUR loc max_natUR.

Definition view_to_ra (v : view) : viewUR := MaxNat <$> v.

Global Instance view_core_id (v : viewUR) : CoreId v.
Proof. apply _. Qed.

Lemma view_to_ra_injective V U : view_to_ra V ≡ view_to_ra U → V = U.
Proof.
  intros H.
  apply map_eq.
  intros ℓ.
  pose proof (H ℓ) as Heq%leibniz_equiv.
  rewrite !lookup_fmap in Heq.
  destruct (V !! ℓ), (U !! ℓ); try done.
  by inversion Heq.
Qed.

Lemma view_to_ra_surjective U : ∃ V, view_to_ra V ≡ U.
Proof.
  exists (max_nat_car <$> U). intros K.
  rewrite /view_to_ra. rewrite !lookup_fmap.
  destruct (U !! K) as [[n]|] eqn:Eq; rewrite Eq; done.
Qed.

(* Check view_to_ra_surjective. *)

Lemma view_to_ra_op V W : view_to_ra V ⋅ view_to_ra W = view_to_ra (V ⊔ W).
Proof.
  apply leibniz_equiv.
  intros K.
  rewrite /view_to_ra.
  rewrite lookup_op.
  rewrite !lookup_fmap.
  rewrite lookup_union_with.
  destruct (V !! K), (W !! K); done.
Qed.

(* NOTE: The other direction should hold as well. *)
Lemma view_to_ra_incl V W : view_to_ra V ≼ view_to_ra W → V ⊑ W.
Proof.
  intros [U Heq%leibniz_equiv].
  (* apply view_to_ra_surjective in U. *) (* Why does this now work? *)
  pose proof (view_to_ra_surjective U) as [V' Heq'%leibniz_equiv].
  rewrite <- Heq' in Heq.
  apply view_lt.
  rewrite view_to_ra_op in Heq.
  eexists _.
  apply view_to_ra_injective.
  rewrite Heq.
  done.
Qed.