From stdpp Require Import countable numbers gmap.
From iris.heap_lang Require Export locations.
From iris.algebra Require Export gmap numbers.

Notation time := nat.

(* A view is a finite map from locations to natural numbers. A view is a monoid
  with the empty map as the unit and point-wise max as the operation. To get
  this monoid structure very easily we use the camera of finite maps and the
  max_nat camera. We will use this definition in, for instance, the memory model
  where the full camera structure is not needed. But, this approach simplifies
  things greatly. *)
Notation view := (gmap loc max_nat).

Notation viewUR := (gmapUR loc max_natUR).

Implicit Types (V W : view) (ℓ : loc).

(* Definition maybe_max mx my :=
  match mx, my withtime
  | Some x, Some y => Some (x `max` y)
  | _, _ => None end). *)

Instance join_view : Join view :=
  λ a b, a ⋅ b.
  (* (merge (λ (x1 x2 : nat), Some (x1 `max` x2))). *)

(* Instance join_view : Join view := (union_with (λ (x1 x2 : nat), Some (x1 `max` x2))). *)

Instance subseteq_view : SqSubsetEq view := λ v w, v ≼ w.
  (* λ v w, v ⊔ w = w. *)
  (* λ v w, ∀ k t, v !! k = Some t → ∃ t', w !! k = Some t' ∧ t ≤ t'. *)

Lemma subseteq_view_incl V W : (V ⊑ W) = (V ≼ W).
Proof. done. Qed.

Global Instance subseteq_view_assoc : Assoc (=) (join_view).
Proof. apply _. Qed.

(* Global Instance subseteq_view_transitive' : Transitive (subseteq_view).
Proof.
  intros V1 V2 V3. rewrite /subseteq_view.
  intros H H'. rewrite -H'. rewrite assoc. rewrite H. done.
Qed. *)

(* Lemma view_lt (V W : view) : V ⊑ W ↔ ∃ V', V ⊔ V' = W.
Proof.
Admitted. *)

Infix "!!0" := (λ m i, default 0 (max_nat_car <$> (m !! i))) (at level 80).

Lemma view_lt_lt V W ℓ : V ⊑ W → (V !!0 ℓ) ≤ (W !!0 ℓ).
Proof.
  rewrite subseteq_view_incl lookup_included.
  intros le.
  pose proof (le ℓ) as le.
  move: le.
  destruct (V !! ℓ) as [[t]|] eqn:eq, (W !! ℓ) as [[t'']|] eqn:eq'; simpl; try lia.
  - rewrite eq. rewrite eq'.
    rewrite Some_included_total.
    rewrite max_nat_included.
    done.
  - rewrite eq. rewrite eq'.
    rewrite option_included.
    intros [?|[? [? (_ & ? & _)]]]; done.
Qed.

(* Definition view_to_ra (v : view) : view := (@id view). *)
  (* MaxNat <$> v. *)

Global Instance view_core_id (v : view) : CoreId v.
Proof. apply _. Qed.

(* Lemma view_to_ra_injective V U : view_to_ra V ≡ view_to_ra U → V = U.
Proof.
  intros H.
  apply map_eq.
  intros ℓ.
  pose proof (H ℓ) as Heq%leibniz_equiv.
  rewrite !lookup_fmap in Heq.
  destruct (V !! ℓ), (U !! ℓ); try done.
  by inversion Heq.
Qed. *)

(* Lemma view_to_ra_surjective U : ∃ V, view_to_ra V ≡ U.
Proof.
  exists (max_nat_car <$> U). intros K.
  rewrite /view_to_ra. rewrite !lookup_fmap.
  destruct (U !! K) as [[n]|] eqn:Eq; rewrite Eq; done.
Qed. *)

(* Check view_to_ra_surjective. *)

(* Lemma view_to_ra_op V W : view_to_ra V ⋅ view_to_ra W = view_to_ra (V ⊔ W).
Proof.
  apply leibniz_equiv.
  intros K.
  rewrite /view_to_ra.
  rewrite lookup_op.
  rewrite !lookup_fmap.
  rewrite lookup_union_with.
  destruct (V !! K), (W !! K); done.
Qed. *)

(* NOTE: The other direction should hold as well. *)
(* Lemma view_to_ra_incl V W : view_to_ra V ≼ view_to_ra W → V ⊑ W.
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
Qed. *)
