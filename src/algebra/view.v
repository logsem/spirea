(* In this we define [view] type which is both a unital resource algebra and a
lattice. We use the lattice notation from stdpp. *)

From stdpp Require Import tactics countable numbers gmap.
From iris.heap_lang Require Export locations.
From iris.algebra Require Export gmap numbers.

From self Require Import extra.

Notation time := nat (only parsing).

(* A view is a finite map from locations to natural numbers. A view is a monoid
  with the empty map as the unit and point-wise max as the operation. To get
  this monoid structure very easily we use the camera of finite maps and the
  max_nat camera. We will use this definition in, for instance, the memory model
  where the full camera structure is not needed. But, this approach simplifies
  things greatly. *)
Notation view := (gmap loc max_nat).

Notation viewO := (gmapO loc max_natO).

Notation viewUR := (gmapUR loc max_natUR).

Implicit Types (V W : view) (ℓ : loc).

Instance join_view : Join view :=
  λ a b, a ⋅ b.

Instance subseteq_view : SqSubsetEq view := λ v w, v ≼ w.

Lemma view_join V W : (V ⊔ W) = (V ⋅ W).
Proof. done. Qed.

Definition view_add (V1 V2 : view) : view :=
  let to_nat (n : option max_nat) := from_option max_nat_car 0 n in
  merge (λ n1 n2, Some (MaxNat (to_nat n1 + to_nat n2))) V1 V2.

Infix "`view_add`" := view_add (at level 50, left associativity).

Lemma subseteq_view_incl V W : (V ⊑ W) = (V ≼ W).
Proof. done. Qed.

Global Instance subseteq_view_assoc : Assoc (=) (join_view).
Proof. apply _. Qed.

Global Instance subseteq_view_comm : Comm (=) (join_view).
Proof. apply _. Qed.

Global Instance join_mono : Proper ((⊑@{view}) ==> (⊑) ==> (⊑)) (⊔).
Proof. solve_proper. Qed.

Global Instance view_core_id (v : view) : CoreId v.
Proof. apply _. Qed.

(* A view is always valid. *)
Lemma view_valid V : ✓ V.
Proof. intros k. case (V !! k); done. Qed.

Instance view_join_bot_l : LeftId (=) (∅ : view) (⊔).
Proof.
  intros ?. rewrite view_join. apply leibniz_equiv. by rewrite left_id.
Qed.
Instance list_join_bot_r : RightId (=) (∅ : view) (⊔).
Proof. intros ?. rewrite (comm (⊔)). by rewrite left_id. Qed.

Lemma lookup_join (V1 V2 : view) t1 t2 ℓ :
  V1 !! ℓ = Some (MaxNat t1) →
  V2 !! ℓ = Some (MaxNat t2) →
  (V1 ⊔ V2) !! ℓ = Some (MaxNat (t1 `max` t2)).
Proof. intros l1 l2. rewrite lookup_op. rewrite l1 l2. done. Qed.

Definition lookup_zero (V : view) l := default 0 (max_nat_car <$> (V !! l)).

Notation "m !!0 l" := (lookup_zero m l) (at level 50).

Lemma lookup_zero_lub V1 V2 ℓ : ((V1 ⊔ V2) !!0 ℓ) = (V1 !!0 ℓ) `max` (V2 !!0 ℓ).
  rewrite /lookup_zero. rewrite view_join. rewrite lookup_op.
  destruct (V1 !! ℓ) eqn:eq1; rewrite eq1;
  destruct (V2 !! ℓ) eqn:eq2; rewrite eq2; try done.
  simpl. lia.
Qed.

Lemma view_lookup_zero_empty ℓ : ((∅ : view) !!0 ℓ) = 0.
Proof. rewrite /lookup_zero. by rewrite lookup_empty. Qed.

Lemma lookup_zero_singleton ℓ t : ({[ ℓ := MaxNat t ]} : view) !!0 ℓ = t.
Proof. rewrite /lookup_zero. rewrite lookup_singleton. done. Qed.

Lemma lookup_zero_insert ℓ t (V : view) : (<[ℓ := MaxNat t]>V) !!0 ℓ = t.
Proof. rewrite /lookup_zero. rewrite lookup_insert. done. Qed.

Lemma view_empty_least V : ∅ ⊑ V.
Proof.
  rewrite subseteq_view_incl.
  apply: ucmra_unit_least.
Qed.

Lemma lookup_zero_gt_zero V ℓ : 0 ≤ V !!0 ℓ.
Proof. rewrite /lookup_zero. destruct (V !! ℓ); lia. Qed.

Lemma lookup_zero_None_zero V ℓ : V !! ℓ = None -> V !!0 ℓ = 0.
Proof. rewrite /lookup_zero. intros ->. done. Qed.

Lemma view_included V W :
  V ⊑ W ↔ (∀ i : loc, V !! i ≼ W !! i).
Proof. rewrite subseteq_view_incl lookup_included. done. Qed.

(* A convenient condition for showing that one view is included in another. *)
Lemma view_le_lookup V W :
  (∀ ℓ t, V !! ℓ = Some (MaxNat t) → ∃ t', W !! ℓ = Some (MaxNat t') ∧ t ≤ t') ↔
  V ⊑ W.
Proof.
  rewrite view_included. split.
  * intros H ℓ.
    case (V !! ℓ) as [[t]|] eqn:look.
    - destruct (H ℓ t) as [t' [eq le]]; first done.
      rewrite eq Some_included_total max_nat_included. done.
    - assert (@None (ofe_car (cmra_ofeO max_natR)) = (ε : option max_nat)) as ->;
        first done.
      apply ucmra_unit_least.
  * intros incl ℓ t look.
    specialize (incl ℓ).
    rewrite look in incl.
    destruct (W !! ℓ) as [[t']|].
    - exists t'. split; first done.
      rewrite Some_included_total max_nat_included in incl.
      done.
    - apply option_not_included_None in incl. done.
Qed.

Global Instance view_lt_lt : Proper ((⊑) ==> (=) ==> (≤)) (lookup_zero).
Proof.
  intros V V' le ℓ ? <-.
  rewrite view_included in le.
  specialize (le ℓ).
  move: le.
  rewrite /lookup_zero.
  destruct (V !! ℓ) as [[t]|] eqn:eq, (V' !! ℓ) as [[t'']|] eqn:eq'; simpl; try lia.
  - rewrite Some_included_total.
    rewrite max_nat_included.
    done.
  - by intros ?%option_not_included_None.
Qed.

Lemma view_le_dom_subseteq V W : V ⊑ W → dom V ⊆ dom W.
Proof. rewrite subseteq_view_incl. intros ?. apply dom_included. done. Qed.

Lemma view_le_look ℓ V W t :
  V !! ℓ = Some (MaxNat t) → V ⊑ W → ∃ t', W !! ℓ = Some (MaxNat t') ∧ t ≤ t'.
Proof.
  intros look incl.
  destruct (W !! ℓ) as [[t']|] eqn:eq.
  - exists t'. split; first done.
    pose proof (view_lt_lt V W incl ℓ ℓ) as le.
    rewrite /lookup_zero in le.
    rewrite eq in le.
    rewrite look in le.
    by apply le.
  - move: incl.
    rewrite subseteq_view_incl.
    rewrite lookup_included.
    intros l. move: (l ℓ).
    rewrite look eq.
    rewrite option_included.
    intros [?|[? [? (_ & ? & _)]]]; done.
Qed.

Lemma option_max_nat_included (on on' om : option max_nat) :
  on ≼ om → on' ≼ om → on ⋅ on' ≼ om.
Proof.
  destruct on, on', om; auto.
  - rewrite !Some_included_total.
    destruct m, m0, m1.
    rewrite max_nat_op !max_nat_included. simpl. lia.
  - rewrite option_included.
    intros [[=]|(? & ? & _ & [=] & _)].
Qed.

Lemma view_join_id V : V ⊔ V = V.
Proof.
  apply map_eq. intros ℓ.
  rewrite lookup_op.
  case (V !! ℓ) as [[t]|] eqn:eq; rewrite eq; last done.
  rewrite -Some_op. rewrite max_nat_op. rewrite Nat.max_id. done.
Qed.

Lemma view_le_l V W : V ⊑ V ⊔ W.
Proof.
  rewrite subseteq_view_incl. rewrite view_join.
  eapply (cmra_included_l V).
Qed.

Lemma view_le_r V W : V ⊑ W ⊔ V.
Proof. rewrite comm. apply view_le_l. Qed.

Lemma view_le_lub_l V W U : V ⊑ W → V ⊑ W ⊔ U.
Proof. intros H. etrans. apply H. apply view_le_l. Qed.

Lemma view_le_lub_r V W U : V ⊑ W → V ⊑ U ⊔ W.
Proof. intros H. etrans. apply H. apply view_le_r. Qed.

(* NOTE: Perhaps this lema could be an instance of some [Proper] thing. *)
Lemma view_lub_le V V' W :
  V ⊑ W → V' ⊑ W → (V ⊔ V') ⊑ W.
Proof.
  rewrite !subseteq_view_incl view_join.
  rewrite !lookup_included.
  intros Vle V'le.
  intros ℓ.
  rewrite lookup_op.
  apply option_max_nat_included; done.
Qed.

Lemma view_insert_le' V V' ℓ t :
  V ⊑ V' → (V !!0 ℓ) ≤ t → V ⊑ <[ℓ := MaxNat t]> V'.
Proof.
  rewrite /lookup_zero.
  intros sub le.
  rewrite subseteq_view_incl.
  rewrite lookup_included.
  intros ℓ'.
  destruct (decide (ℓ = ℓ')).
  - subst. rewrite lookup_insert.
    destruct (V !! ℓ') as [[m]|] eqn:eq; simpl.
    * rewrite eq. simpl in *. apply Some_included_2. apply max_nat_included. done.
    * rewrite eq.
      replace (None) with (ε : option max_nat); last done.
      apply ucmra_unit_least.
  - rewrite lookup_insert_ne; last done.
    by apply lookup_included.
Qed.

Lemma view_insert_le V ℓ t :
  (V !!0 ℓ) ≤ t → V ⊑ <[ℓ := MaxNat t]>V.
Proof. by apply view_insert_le'. Qed.

Lemma view_insert_op V ℓ t :
  (V !!0 ℓ) ≤ t → (V ⊔ {[ℓ := MaxNat t]}) = (<[ℓ := MaxNat t]> V).
Proof.
  rewrite /lookup_zero.
  intros le. rewrite view_join.
  apply map_eq. intros ℓ'.
  rewrite lookup_op.
  destruct (decide (ℓ = ℓ')).
  - subst. rewrite lookup_singleton.
    rewrite lookup_insert.
    destruct (V !! ℓ') as [[m]|] eqn:eq; rewrite eq; last done.
    rewrite -Some_op. rewrite max_nat_op.
    f_equiv. f_equiv. simpl in le. lia.
  - rewrite lookup_singleton_ne; last done.
    rewrite right_id.
    rewrite lookup_insert_ne; done.
Qed.

Lemma Some_MaxNat_included t t' : Some (MaxNat t) ≼ Some (MaxNat t') ↔ t ≤ t'.
Proof. by rewrite Some_included_total max_nat_included. Qed.

Lemma view_le_singleton ℓ t V :
  {[ ℓ := MaxNat t ]} ⊑ V ↔ ∃ t', V !! ℓ = Some (MaxNat t') ∧ t ≤ t'.
Proof.
  split.
  - rewrite subseteq_view_incl lookup_included.
    intros H. specialize H with ℓ.
    move: H. rewrite lookup_singleton.
    destruct (V !! ℓ) as [[t']|] eqn:eq; rewrite eq; intros H.
    + exists t'. split; first done. by apply Some_MaxNat_included.
    + by apply option_not_included_None in H.
  - intros H.
    apply view_le_lookup=> i t' look.
    apply lookup_singleton_Some in look.
    naive_solver.
Qed.

Definition view_to_zero V := (const (MaxNat 0)) <$> V.

Global Instance view_to_zero_mono : Proper ((⊑) ==> (⊑)) view_to_zero.
Proof.
  rewrite /view_to_zero.
  intros ?? le.
  apply view_le_lookup.
  intros ℓ t look.
  apply lookup_fmap_Some in look.
  destruct look as ([t2] & [= eq] & look).
  edestruct view_le_look as (t'' & look' & lt); [apply look|apply le|].
  exists 0. rewrite lookup_fmap look' -eq. done.
Qed.

Lemma view_to_zero_lookup V ℓ t :
  V !! ℓ = Some t →
  view_to_zero V !! ℓ = Some (MaxNat 0).
Proof.
  intros look. rewrite /view_to_zero.
  rewrite lookup_fmap. rewrite look. done.
Qed.

Lemma view_sqsubseteq_antisym V W : V ⊑ W → W ⊑ V → V = W.
Proof.
  rewrite !subseteq_view_incl.
  rewrite !lookup_included.
  intros sub1 sub2.
  apply map_eq.
  intros ℓ.
  specialize (sub1 ℓ).
  specialize (sub2 ℓ).
  apply option_included_total in sub1.
  apply option_included_total in sub2.
  destruct sub1 as [eq1 | ([a] & [b] & c & ? & ?)];
  destruct sub2 as [eq2 | ([e] & [f] & g & ? & ?)].
  - by rewrite eq1 eq2.
  - naive_solver.
  - naive_solver.
  - rewrite H1.
    rewrite g.
    setoid_rewrite max_nat_included in H0.
    setoid_rewrite max_nat_included in H2.
    f_equiv.
    f_equiv.
    simpl in *.
    simplify_eq.
    lia.
Qed.

Lemma view_to_zero_singleton ℓ t :
  view_to_zero {[ ℓ := t ]} = {[ ℓ := MaxNat 0 ]}.
Proof. rewrite /view_to_zero. rewrite map_fmap_singleton. done. Qed.

(* Instances of the lattice type classes for products. *)

Global Instance join_prod `{!Join A, !Join B} : Join (A * B) :=
  λ '(a, b) '(a', b'), (a ⊔ a', b ⊔ b').

Global Instance subseteq_prod `{!SqSubsetEq A, !SqSubsetEq B} : SqSubsetEq (A * B) :=
  λ '(a, b) '(a', b'), a ⊑ a' ∧ b ⊑ b'.

Lemma subseteq_prod' `{SqSubsetEq A, SqSubsetEq B} (a a' : A) (b b' : B) :
  (a, b) ⊑ (a', b') = (a ⊑ a' ∧ b ⊑ b').
Proof. done. Qed.

(* Projections are monotone. *)
Global Instance fst_mono `{!SqSubsetEq A, !SqSubsetEq B} : Proper ((⊑) ==> (⊑)) (@fst A B).
Proof. intros [??] [??] [??]. done. Qed.

(* Projections are monotone. *)
Global Instance snd_mono `{!SqSubsetEq A, !SqSubsetEq B} : Proper ((⊑) ==> (⊑)) (@snd A B).
Proof. intros [??] [??] [??]. done. Qed.

Instance pair_preorder `{!SqSubsetEq A, !SqSubsetEq B, !PreOrder (⊑@{A}),
                         !PreOrder (⊑@{B})} : PreOrder (⊑@{A * B}).
Proof.
  constructor.
  - intros [??]. rewrite subseteq_prod'. done.
  - intros [??] [??] [??]. rewrite !subseteq_prod'. intros [??] [??].
    split; etrans; done.
Qed.

Instance prod_subseteq_trans `{!SqSubsetEq A, !SqSubsetEq B, !Transitive (⊑@{A}),
                               !Transitive (⊑@{B})} : Transitive (⊑@{A * B}).
Proof.
  rewrite /Transitive.
  intros [??] [??] [??] [??] [??].
  split; etrans; done.
Qed.

Global Instance prod_join_assoc `{!Join A, !Join B, !Assoc (=@{A}) (⊔),
      !Assoc (=@{B}) (⊔)} : Assoc (=@{A * B}) (⊔).
Proof.
  intros [??] [??] [??]. cbv. rewrite assoc. rewrite assoc. done.
Qed.

Global Instance prod_join_comm `{!Join A, !Join B, !Comm (=@{A}) (⊔),
      !Comm (=@{B}) (⊔)} : Comm (=@{A * B}) (⊔).
Proof.
  intros [a b] [? ?]. cbv. rewrite (comm _ a) (comm _ b). done.
Qed.

(* Subtract a view from another. *)
Definition view_sub (V1 V2 : view) : view :=
  map_imap (λ ℓ t, Some (MaxNat (max_nat_car t - (V2 !!0 ℓ)))) V1.
  (* let to_nat (n : option max_nat) := from_option max_nat_car 0 n in *)
  (* merge (λ n1 n2, (λ n, MaxNat (max_nat_car n - to_nat n2)) <$> n1) V1 V2. *)

Infix "`view_sub`" := view_sub (at level 50, left associativity).

Lemma view_sub_lookup V1 V2 ℓ :
  (V1 `view_sub` V2) !! ℓ =
    (λ t, MaxNat $ (max_nat_car t) - (V2 !!0 ℓ)) <$> V1 !! ℓ.
Proof.
  rewrite /view_sub. rewrite map_lookup_imap /lookup_zero.
  destruct (V1 !! ℓ); destruct (V2 !! ℓ); done.
Qed.

Lemma view_sub_lookup_Some V1 V2 t ℓ :
  (V1 `view_sub` V2) !! ℓ = Some (MaxNat t) →
  ∃ t2, V1 !! ℓ = Some (MaxNat t2) ∧ t = t2 - (V2 !!0 ℓ).
Proof.
  rewrite view_sub_lookup /lookup_zero.
  destruct (V1 !! ℓ) as [[t1]|]; destruct (V2 !! ℓ) as [[t2]|]; naive_solver.
Qed.

Lemma view_sub_mono V1 V2 V3 :
  V1 ⊑ V2 → V1 `view_sub` V3 ⊑ V2 `view_sub` V3.
Proof.
  rewrite -!view_le_lookup.
  intros H ℓ t (t2 & look1 & ?)%view_sub_lookup_Some.
  rewrite view_sub_lookup.
  destruct (H ℓ _ look1) as (? & look2 & ?).
  eexists _.
  rewrite look2 /=. split; first done.
  lia.
Qed.

Lemma view_sub_empty V :
  V `view_sub` ∅ = V.
Proof.
  apply map_eq. intros ℓ. rewrite view_sub_lookup.
  destruct (V !! ℓ) as [[t]|]; last done. simpl.
  rewrite view_lookup_zero_empty.
  f_equiv. f_equiv. lia.
Qed.

Lemma view_sub_greater V1 V2 :
  V1 ⊑ V2 → V1 `view_sub` V2 = view_to_zero V1.
Proof.
  rewrite -view_le_lookup => H.
  apply map_eq => ℓ.
  rewrite view_sub_lookup /view_to_zero.
  rewrite lookup_fmap.
  destruct (V1 !! ℓ) as [[t]|] eqn:look; simpl; last done.
  f_equiv. f_equiv.
  rewrite /lookup_zero.
  destruct (H ℓ _ look) as (? & -> & ?).
  simpl. lia.
Qed.

Lemma view_to_zero_dom_eq V1 V2 :
  dom V1 = dom V2 →
  view_to_zero V1 = view_to_zero V2.
Proof. unfold view_to_zero. rewrite -2!gset_to_gmap_dom. intros ->. done.
Qed.

Lemma view_sub_dom_eq V1 V2 :
  dom (V1 `view_sub` V2) = dom V1.
Proof.
  unfold view_sub.
  apply dom_imap_L.
  intros ?. rewrite elem_of_dom /is_Some. naive_solver.
Qed.

(* Lemma view_add_lookup V1 V2 ℓ : *)
(*   dom V1 = dom V2 → *)
(*   (V1 `view_add` V2) !! ℓ = *)
(*   Some MaxNat (V1 !!0 ℓ + (V2 !!0 ℓ)). *)
(* Proof. *)
(* Qed. *)

#[global]
Instance view_add_mono : Proper ((⊑) ==> (⊑) ==> (⊑)) view_add.
Proof.
  unfold Proper, respectful.
  setoid_rewrite <- view_le_lookup.
  intros VL1 ? le1 VL2 ? le2.
  intros ℓ ?.
  unfold view_add.
  rewrite 2!lookup_merge.
  destruct (VL1 !! ℓ) as [[?]|] eqn:look1;
    destruct (VL2 !! ℓ) as [[?]|] eqn:look2; simpl; try done.
    - edestruct le1 as (? & -> & ?); first done.
      edestruct le2 as (? & -> & ?); first done. simpl.
      intros [= <-]. eexists _. split; first done. lia.
    - edestruct le1 as (? & -> & ?); first done.
      intros [= <-]. eexists _. split; first done. simpl.
      destruct (y0 !! ℓ); lia.
    - edestruct le2 as (? & -> & ?); first done. simpl.
      intros [= <-]. destruct (y !! ℓ); eexists _; split; done || (simpl; lia).
Qed.

Lemma view_add_view_zero V1 :
  V1 `view_add` (view_to_zero V1) = V1.
Proof.
  apply map_eq. intros ℓ.
  rewrite lookup_merge /view_to_zero lookup_fmap.
  destruct (V1 !! ℓ) as [[t]|]; simpl; last reflexivity.
  f_equiv. f_equiv. lia.
Qed.

Instance view_add_assoc : Assoc (=) view_add.
Proof.
  intros x y z.
  apply map_eq. intros ℓ.
  rewrite !lookup_merge.
  destruct (x !! ℓ); destruct (y !! ℓ); destruct (z !! ℓ);
    simpl; f_equiv; f_equiv; lia.
Qed.

Instance view_add_comm : Comm (=) view_add.
Proof.
  intros x y. apply map_eq. intros ℓ. rewrite !lookup_merge.
  destruct (x !! ℓ); destruct (y !! ℓ); simpl; f_equiv; f_equiv; lia.
Qed.

(* Lemma view_add_empty V : *)
(*   ∅ `view_add` V = V. *)
(* Proof. Qed. *)

(* Global Instance pair_join_mono `{!Join A, !Join B, !SqSubsetEq A, !SqSubsetEq B} : Proper ((⊑@{A * B}) ==> (⊑) ==> (⊑)) (⊔). *)
(* Proof. *)
(*   Check pointwise_relation. *)
(*   intros [??] [??] ? ? ? ?. *)
  (* solve_proper.
Qed. *)

(* Global Instance foo_mono : *)
(*   Proper (pointwise_relation _ (=) ==> (⊆) ==> (⊆)) (⊑). *)
(* Proof. intros f g ? X Y. set_unfold; naive_solver. Qed. *)

#[export] Hint Rewrite (insert_empty (M := gmap loc) (A := max_nat)) : view_simpl.
#[export] Hint Rewrite (lookup_singleton (M := gmap loc) (A := max_nat)) : view_simpl.
#[export] Hint Rewrite (view_lookup_zero_empty) : view_simpl.
#[export] Hint Rewrite (left_id ∅ (⊔)) : view_simpl.
#[export] Hint Rewrite (right_id ∅ (⊔)) : view_simpl.
#[export] Hint Rewrite (lookup_singleton_ne (A := max_nat)) using assumption : view_simpl. (* FIXME: This hint doesn't seem to work. *)

Ltac simpl_view := autorewrite with view_simpl.
