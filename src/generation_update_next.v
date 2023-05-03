From Equations Require Import Equations.

From iris.algebra Require Import functions gmap agree excl csum max_prefix_list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

From iris_named_props Require Import named_props.

From self Require Import hvec extra basic_nextgen_modality gen_trans
  gen_single_shot gen_pv.

Import uPred.

(** A copy of [option] to work arround universe inconsistencies that arrise if
we use [option]. *)
Inductive option2 (A : Type) : Type :=
  | Some2 : A -> option2 A
  | None2 : option2 A.

Arguments Some2 {A} a.
Arguments None2 {A}.

(*
Inductive list2 (A : Type) : Type :=
 | nil2 : list2 A
 | cons2 : A -> list2 A -> list2 A.

Arguments nil2 {A}.
Arguments cons2 {A} a l.

Fixpoint list2_lookup {A} (l : list2 A) (n : nat) : option2 A :=
  match n, l with
    | O, cons2 x _ => Some2 x
    | S n, cons2 _ l => list2_lookup l n
    | _, _ => None2
  end.

Local Infix "!!2" := list2_lookup (at level 50, left associativity).
 *)

Section types.

  (** A transformation over the carrier of the camera [A]. *)
  Definition cmra_to_trans A := cmra_car A → cmra_car A.

  (** A predicate over a transformation over [A]. *)
  Definition cmra_to_pred A := (cmra_to_trans A) → Prop.

  Definition pred_over_ty {n} (DS : ivec n Type) (A : Type) :=
    iimpl id DS ((A → A) → Prop).

  (* A curried predicate over the cameras [DS] and [A]. *)
  Definition pred_over {n} (DS : ivec n cmra) (A : cmra) :=
    iimpl id (ivec_map cmra_to_trans DS) ((A → A) → Prop).

  (* This results in the type:
     [(max_nat → max_nat) → (excl () → excl ()) → (nat → nat) → Prop] *)
  Compute (pred_over [max_natR; exclR unitO] natR).

  Definition True_pred {n} {DS : ivec n cmra} {A} : pred_over DS A :=
    hcurry (λ _ _, True).

End types.

Definition trans_for n (DS : ivec n cmra) := hvec n (cmra_to_trans <$> DS).

Notation preds_for n ls := (hvec n (cmra_to_pred <$> ls)).

(* trans_for does not give universe issue. *)
Definition test_exist {Σ} {n : nat} {DS : ivec n cmra} : iProp Σ :=
  ∃ (ts : trans_for n DS), ⌜ True ⌝.

(* Notation trans_for_old := (hvec cmra_to_trans). *)

(* trans_for_old _does_ give universe issue. The root cause is the way the
 * [cmra] appears in the type. In [trans_for] the occurence of [cmra_car]
 * prevents the universe issue somehow. *)
(* Definition test_exist {Σ} {n : nat} {DS : ivec cmra n} : iProp Σ := *)
(*   ∃ (ts : trans_for n DS), ⌜ True ⌝. *)

(* The functor in [Σ] at index [i] applied to [iProp]. *)
Notation R Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPropO Σ)).
(* The functor in [Σ] at index [i] applied to [iPreProp]. *)
Notation Rpre Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ)).
Notation T Σ i := (R Σ i → R Σ i).

Local Definition map_unfold {Σ} {i : gid Σ} : R Σ i -n> Rpre Σ i :=
  rFunctor_map _ (iProp_fold, iProp_unfold).
Local Definition map_fold {Σ} {i : gid Σ} : Rpre Σ i -n> R Σ i :=
  rFunctor_map _ (iProp_unfold, iProp_fold).

Lemma map_unfold_inG_unfold {Σ A} {i : inG Σ A} :
  map_unfold ≡ own.inG_unfold (i := i).
Proof. done. Qed.

Lemma map_fold_unfold {Σ} {i : gid Σ} (a : R Σ i) :
  map_fold (map_unfold a) ≡ a.
Proof.
  rewrite /map_fold /map_unfold -rFunctor_map_compose -{2}[a]rFunctor_map_id.
  apply (ne_proper (rFunctor_map _)); split=> ?; apply iProp_fold_unfold.
Qed.

Lemma map_unfold_op {Σ} {i : gid Σ} (a b : R Σ i)  :
  map_unfold a ⋅ map_unfold b ≡ map_unfold (a ⋅ b).
Proof. rewrite cmra_morphism_op. done. Qed.

Lemma map_unfold_validN {Σ} {i : gid Σ} n (x : R Σ i) :
  ✓{n} (map_unfold x) ↔ ✓{n} x.
Proof.
  split; [|apply (cmra_morphism_validN _)].
  move=> /(cmra_morphism_validN map_fold). by rewrite map_fold_unfold.
Qed.

Lemma map_unfold_validI {Σ} {i : gid Σ} (a : R Σ i) :
  ✓ map_unfold a ⊢@{iPropI Σ} ✓ a.
Proof. apply valid_entails=> n. apply map_unfold_validN. Qed.

(** Transport an endo map on a camera along an equality in the camera. *)
Definition cmra_map_transport {A B : cmra}
    (Heq : A = B) (f : A → A) : (B → B) :=
  eq_rect A (λ T, T → T) f _ Heq.

Lemma cmra_map_transport_cmra_transport {A B : cmra}
    (f : A → A) a (Heq : A = B) :
  (cmra_map_transport Heq f) (cmra_transport Heq a) =
  (cmra_transport Heq (f a)).
Proof. destruct Heq. simpl. reflexivity. Qed.

Global Instance cmra_map_transport_proper {A B : cmra}
    (f : A → A) (Heq : A = B) :
  (Proper ((≡) ==> (≡)) f) →
  (Proper ((≡) ==> (≡)) (cmra_map_transport Heq f)).
Proof. naive_solver. Qed.

(* Resources for generational ghost state. *)

(* Resource algebra for the dependency relation in promises. *)
(* Q: Do we need to store both R and P or only R?? *)
Section dependency_relation_cmra.
  Context {n : nat}.

  Canonical Structure pred_over_tyO (A : Type) (DS : ivec n Type) :=
    leibnizO (pred_over_ty DS A).
  Canonical Structure pred_overO (A : cmra) (DS : ivec n cmra) :=
    leibnizO (pred_over DS A).

  Definition promises (A : Type) (DS : ivec n Type) :=
    max_prefix_list (pred_over_ty DS A).
  Definition promisesR (A : cmra) (DS : ivec n cmra) :=
    max_prefix_listR (pred_overO A DS).

  Definition promisesUR (A : cmra) (DS : ivec n cmra) :=
    max_prefix_listUR (pred_over DS A).

  (* Authorative promises. *)
  Definition auth_promises {A : cmra} {DS : ivec n cmra}
    (ps : list (pred_over DS A)) : auth (max_prefix_list (pred_over DS A)) :=
    ● (to_max_prefix_list ps).
  Definition auth_promises_ty {A : Type} {DS : ivec n Type}
    (ps : list (pred_over_ty DS A)) : auth (promises A DS) :=
    ● (to_max_prefix_list ps).

  (* Fragmental promises. *)
  Definition frag_promises {A : Type} {DS : ivec n Type}
    (ps : list (pred_over_ty DS A)) : auth (promises A DS) :=
    ◯ (to_max_prefix_list ps).

End dependency_relation_cmra.

(** The transformations [ts] satisfies the predicates [ps]. *)
Equations preds_hold {n} {DS : ivec n cmra}
    (ps : preds_for n DS) (ts : trans_for n DS) : Prop :=
  @preds_hold _ (icons _ DS') (hcons p ps') (hcons t ts') := p t ∧ preds_hold ps' ts';
  @preds_hold _ (inil) hnil hnil := True.
Global Transparent preds_hold.

Lemma preds_hold_alt {n DS} (ps : preds_for n DS) (ts : trans_for n DS) :
  preds_hold ps ts ↔ ∀ (i : fin n), (hvec_lookup_fmap ps i) (hvec_lookup_fmap ts i).
Proof.
  split.
  - intros holds i.
    induction i as [?|?? IH] eqn:eq.
    * dependent elimination DS.
      dependent elimination ts.
      dependent elimination ps.
      destruct holds as [pred ?].
      apply pred.
    * dependent elimination DS.
      dependent elimination ts.
      dependent elimination ps.
      rewrite preds_hold_equation_2 in holds.
      destruct holds as [? holds].
      apply (IH  _ _ _ holds t).
      done.
  - intros i.
    induction DS as [|??? IH].
    * dependent elimination ts.
      dependent elimination ps.
      done.
    * dependent elimination ts.
      dependent elimination ps.
      rewrite preds_hold_equation_2.
      split. { apply (i 0%fin). }
      apply IH.
      intros i'.
      apply (i (FS i')).
Qed.

Section dependency_relation_extra.
  Context {n} {A : cmra} {DS : ivec n cmra}.
  Implicit Types (R : pred_over DS A) (P : (A → A) → Prop).

  Definition rel_stronger (R1 R2 : pred_over DS A) :=
    ∀ (ts : trans_for n DS) (t : A → A),
      huncurry R1 ts t → huncurry R2 ts t.

  Definition rel_weaker (R1 R2 : pred_over DS A) := rel_stronger R2 R1.

  Definition pred_stronger (P1 P2 : (A → A) → Prop) :=
    ∀ (t : A → A), P1 t → P2 t.

  Definition rel_implies_pred R P : Prop :=
    ∀ (ts : trans_for n DS) (t : A → A), huncurry R ts t → P t.

  (* Notation preds_for n ls := (hvec cmra_to_pred n ls). *)

  Definition pred_prefix_list_for (all : list (pred_over DS A)) R :=
    (* The given promise [R] is the last promise out of all promises. *)
    last all = Some R ∧
    (* The list of promises increases in strength. *)
    ∀ i j (Ri Rj : pred_over DS A),
      i ≤ j → all !! i = Some Ri → all !! j = Some Rj → rel_weaker Ri Rj.

  (* Includes [P] as well. *)
  Definition pred_prefix_list_for' (all : list (pred_over DS A)) R P :=
    pred_prefix_list_for all R ∧ rel_implies_pred R P.

  Lemma pred_prefix_list_for_singleton p :
    pred_prefix_list_for (p :: []) p.
  Proof.
    split; first done.
    intros ????? [-> ->]%list_lookup_singleton_Some
      [-> ->]%list_lookup_singleton_Some.
    intros ??. done.
  Qed.

  Lemma pred_prefix_list_for'_True :
    pred_prefix_list_for' (True_pred :: []) True_pred (λ _ : A → A, True).
  Proof.
    rewrite /pred_prefix_list_for'.
    split; [apply pred_prefix_list_for_singleton | done].
  Qed.

  Lemma pred_prefix_list_for_prefix_of Rs1 Rs2 R1 R2:
    pred_prefix_list_for Rs1 R1 →
    pred_prefix_list_for Rs2 R2 →
    Rs1 `prefix_of` Rs2 →
    rel_stronger R2 R1.
  Proof.
    intros PP1 PP2 pref.
    destruct PP1 as [isLast1 _].
    destruct PP2 as [isLast2 weaker].
    rewrite last_lookup in isLast1.
    rewrite last_lookup in isLast2.
    eapply weaker; last done.
    - apply le_pred. apply prefix_length. eassumption.
    - eapply prefix_lookup; done.
  Qed.

End dependency_relation_extra.

Definition generational_cmra {n} A (DS : ivec n Type) : Type :=
  option (agree (A → A)) * (* Agreement on transformation into generation *)
  GTS (A → A) * (* Facilitates choice of transformation out of generation *)
  option A * (* Ownership over A *)
  option (agree (list gname)) * (* Gname of dependencies, we don't need to
                                 * store their [gid] as that is static. *)
  gen_pv (auth (promises A DS)) (* List of promises *).

(* Notation for [prodR] as the product below would otherwise get horrible to
 * write. *)
Local Infix "*R*" := prodR (at level 50, left associativity).

Definition generational_cmraR {n} (A : cmra) (DS : ivec n cmra) : cmra :=
  optionR (agreeR (leibnizO (A → A))) *R*
  GTSR (A → A) *R*
  optionR A *R*
  optionR (agreeR (leibnizO (list gname))) *R*
  gen_pvR (authR (promisesR A DS)).

Local Infix "*M*" := prod_map (at level 50, left associativity).

(* The generational transformation function for the encoding of each ownership
over a generational camera. *)
Definition gen_cmra_trans {n} {A : cmra} (DS : ivec n cmra)
    (f : A → A) : generational_cmraR A DS → generational_cmraR A DS :=
  (const (Some (to_agree f)) : _ → optionR (agreeR (leibnizO (A → A)))) *M*
  (GTS_floor : (GTSR (A → A)) → (GTSR (A → A))) *M*
  (fmap f : optionR A → optionR A) *M*
  id *M*
  gen_pv_trans.

Global Instance gen_trans_const {A : ofe} (a : A) :
  GenTrans (const (Some (to_agree a))).
Proof.
  split; first apply _.
  - done.
  - intros. simpl. rewrite (core_id). done.
  - intros ??. simpl.
    rewrite -Some_op.
    rewrite agree_idemp.
    done.
Qed.

Global Instance gen_generation_gen_trans {n} {A : cmra} {DS : ivec n cmra} (f : A → A)
  `{!Proper (equiv ==> equiv) f} :
  GenTrans f → GenTrans (gen_cmra_trans DS f).
Proof. apply _. Qed.

Global Instance gen_generation_proper {n} {A : cmra} (DS : ivec n cmra) (f : A → A) :
  Proper ((≡) ==> (≡)) f →
  Proper ((≡) ==> (≡)) (gen_cmra_trans DS f).
Proof.
  intros ? [[??]?] [[??]?] [[??]?]. simpl in *.
  rewrite /gen_cmra_trans.
  solve_proper.
Qed.

(* Working with the 5-tuple is sometimes annoying. Then these lemmas help. *)
Lemma prod_valid_1st {Σ}
  {A B C D E : cmra} (a : A) (b : B) (c : C) (d : D) (e : E) f g h i j :
  ✓ ((a, b, c, d, e) ⋅ (f, g, h, i, j)) ⊢@{iProp Σ} ✓ (a ⋅ f).
Proof. rewrite 4!prod_validI. simpl. iIntros "[[[[$ _] _] _] _]". Qed.

Lemma prod_valid_2st {Σ}
  {A B C D E : cmra} (a : A) (b : B) (c : C) (d : D) (e : E) f g h i j :
  ✓ ((a, b, c, d, e) ⋅ (f, g, h, i, j)) ⊢@{iProp Σ} ✓ (b ⋅ g).
Proof. rewrite 4!prod_validI. simpl. iIntros "[[[[_ $] _] _] _]". Qed.

Lemma prod_valid_3th {Σ}
  {A B C D E : cmra} (a : A) (b : B) (c : C) (d : D) (e : E) f g h i j :
  ✓ ((a, b, c, d, e) ⋅ (f, g, h, i, j)) ⊢@{iProp Σ} ✓ (c ⋅ h).
Proof. rewrite 4!prod_validI. simpl. iIntros "[[[_ $] _] _]". Qed.

Lemma prod_valid_4th {Σ}
  {A B C D E : cmra} (a : A) (b : B) (c : C) (d : D) (e : E) f g h i j :
  ✓ ((a, b, c, d, e) ⋅ (f, g, h, i, j)) ⊢@{iProp Σ} ✓ (d ⋅ i).
Proof. rewrite 4!prod_validI. iIntros "[[_ $] _]". Qed.

Lemma prod_valid_5th {Σ}
  {A B C D E : cmra} (a : A) (b : B) (c : C) (d : D) (e : E) f g h i j :
  ✓ ((a, b, c, d, e) ⋅ (f, g, h, i, j)) ⊢@{iProp Σ} ✓ (e ⋅ j).
Proof. rewrite 4!prod_validI. iIntros "[_ $]". Qed.

(*
(** If [i : gid Σ] is a generational camera and [Θ : InnerCmras] then [Θ i] is the inner camera for [i] in the sense that R Σ i = generational_cmraR  *)
Definition InnerCmras Σ : Type := gid Σ → cmra.
 *)

(** For every entry in [Ω] we store this record of information. The equality
 * [gti_look] is the "canonical" equality we will use to show that the resource
 * [R Σ i] has the proper form. Using this equality is necesarry as we
 * otherwise end up with different equalities of this form that we then do not
 * know to be equal. *)
Record gen_cmra_data (Σ : gFunctors) (i : gid Σ) := {
  gcd_cmra : cmra;
  gcd_n : nat;
  gcd_deps : ivec gcd_n cmra;
  gcd_deps_ids : ivec gcd_n (gid Σ);
  gti_look : generational_cmraR gcd_cmra gcd_deps = R Σ i;
}.

Arguments gcd_cmra {_} {_}.
Arguments gcd_n {_} {_}.
Arguments gcd_deps {_} {_}.
Arguments gcd_deps_ids {_} {_}.
Arguments gti_look {_} {_}.
(* Arguments gti_valid {_} {_}. *)

(* NOTE: [gen_cmra_data] contains a [cmra] and hence we use [option2] as using
 * [option] would give a universe inconsistency. *)
Definition gen_cmras_data Σ := ∀ (i : gid Σ), option2 (gen_cmra_data Σ i).

Definition omega_wf_at {Σ} (map : gen_cmras_data Σ) id : Prop :=
  match map id with
  | None2 => True
  | Some2 gcd =>
      ∀ idx, ∃ gcd2,
        let id2 := gcd.(gcd_deps_ids) !!! idx in
        map id2 = Some2 gcd2 ∧
        gcd2.(gcd_cmra) = gcd.(gcd_deps) !!! idx
  end.

(** [Ω] is internally consistent with itself. *)
Definition omega_wf {Σ} (Ω : gen_cmras_data Σ) : Prop :=
  ∀ id, omega_wf_at Ω id.

(** [gGenCmras] contains a partial map from the type of cameras into a "set"
of valid transformation function for that camera. *)
Class gGenCmras (Σ : gFunctors) := {
  gc_map : ∀ (i : gid Σ), option2 (gen_cmra_data Σ i);
  (* Storing this wf-ness criteria for the whole map may be too strong. If this
  * gives problems we can wiggle this requirement around to somewhere else. *)
  gc_map_wf : omega_wf gc_map;
}.

Global Arguments gc_map {_} {_}.

#[export] Hint Mode gGenCmras +.

(** Lookup the camera in [Ω] at the index [i] *)
Definition Oc {Σ} (Ω : gGenCmras Σ) i : cmra :=
  match Ω.(gc_map) i with
  | Some2 gcd => gcd.(gcd_cmra)
  | None2 => unit
  end.

(** Lookup the number of depenencies in [Ω] at the index [i] *)
Definition On {Σ} (Ω : gGenCmras Σ) i : nat :=
  match Ω.(gc_map) i with
  | Some2 gcd => gcd.(gcd_n)
  | None2 => 0
  end.

(** Lookup the number of depenencies in [Ω] at the index [i] *)
Definition Oids {Σ} (Ω : gGenCmras Σ) i : ivec (On Ω i) (gid Σ).
Proof.
  rewrite /On.
  destruct Ω.(gc_map) as [gcd|].
  - apply gcd.(gcd_deps_ids).
  - apply inil.
Defined.

(** Lookup the dependency cameras in [Ω] at the index [i] *)
Definition Ocs {Σ} (Ω : gGenCmras Σ) i : ivec (On Ω i) cmra.
Proof.
  rewrite /On.
  destruct Ω.(gc_map) as [gcd|].
  - apply gcd.(gcd_deps).
  - apply inil.
Defined.

(** Lookup the dependency cameras in [Ω] at the index [i] *)
Definition Oeq {Σ} (Ω : gGenCmras Σ) i :
  option2 (generational_cmraR (Oc Ω i) (Ocs Ω i) = R Σ i).
Proof.
  rewrite /On /Oc /Ocs.
  destruct Ω.(gc_map) as [gcd|].
  - constructor. apply gcd.(gti_look).
  - apply None2.
Defined.

Lemma Ocs_Oids_distr `{Ω : gGenCmras} id (idx : fin (On Ω id)) :
  (* omega_wf_at Ω id → *)
  Ocs Ω id !!! idx = Oc Ω (Oids Ω id !!! idx).
Proof.
  specialize (gc_map_wf id).
  revert idx.
  rewrite /omega_wf_at /omega_wf_at /Oids /Oc /Ocs /On.
  destruct (gc_map id) eqn:eq.
  - intros idx wf.
    destruct (wf idx) as (gcd2 & -> & ->).
    reflexivity.
  - intros i. inversion i.
Qed.

(** Lookup the dependency cameras in [Ω] at the index [i] *)
(* Definition Ocs'' {Σ} (Ω : gGenCmras Σ) i : ivec (On Ω i) cmra := Ocs' Ω i. *)

Class genInG {n} (Σ : gFunctors) Ω (A : cmra) (DS : ivec n cmra) := GenInG {
  genInG_inG : inG Σ (generational_cmraR A DS);
  genInG_inG_deps : ∀ i d, DS !!! i = d → inG Σ (generational_cmraR A DS);
  (* genInG_id : gid Σ; *)
  (* genInG_apply := rFunctor_apply (gFunctors_lookup Σ genInG_id); *)
  genInG_gti : gen_cmra_data Σ (inG_id genInG_inG);
  genInG_gen_trans : Ω.(gc_map) (inG_id genInG_inG) = Some2 genInG_gti;
  genInG_gti_typ : A = genInG_gti.(gcd_cmra);
  (* genInG_prf : A = genInG_apply (iPropO Σ) _; *)
  (* genInG_gen_trans2 : *)
  (*   genInG_gti.(gti_valid) = *)
  (*     (gen_transport (gen_cmra_eq genInG_gti_typ genInG_gti.(gti_look)) (lift g)); *)
}.

Existing Instance genInG_inG.

(* Knowledge that [A] is a resource, with the information about its dependencies
hidden in the dependent pair. *)
Class genInSelfG (Σ : gFunctors) Ω (A : cmra) := GenInG2 {
  genInSelfG_n : nat;
  genInSelfG_DS : ivec genInSelfG_n cmra;
  genInSelfG_gen : genInG Σ Ω A (genInSelfG_DS);
}.

Existing Instance genInSelfG_gen.
(* Global Arguments genInG_id {_ _ _ _} _. *)
(* Global Program Instance genInG_inG {n} {DS : ivec n cmra} `{i : !genInG Σ A DS} : *)
(*       inG Σ (generational_cmraR A) := *)
(*   {| *)
(*     inG_id := genInG_id i; *)
(*     inG_prf := genInG_prf; (* gen_cmra_eq genInG2_gti_typ genInG2_gti.(gti_look); *) *)
(*   |}. *)

(*
How to represent the dependencies?

We need
- To be able to store both a collection of ..
  - .. the types of the dependencies [A : Type, ..]
  - .. transformation functions matching the types of the dependencis [t : A → A, ..]
  - .. predicates over the transformation functions.
- We need to be able to map over the types.
- To be able to do an ∧ or a ∗ over the transformation functions.
*)

Section transmap.
  Context `{Σ : gFunctors, Ω : gGenCmras Σ}.

  (** A [TransMap] contains transformation functions for a subset of ghost
   * names. We use one to represent the transformations that a user has picked.
   * the entries that we have picked generational transformations for. *)
  Definition TransMap : Type := ∀ i, gmap gname (Oc Ω i → Oc Ω i).

  Implicit Types (transmap : TransMap).

  #[global]
  Instance transmap_subseteq : SubsetEq TransMap :=
    λ p1 p2, ∀ i, p1 i ⊆ p2 i.

  #[global]
  Instance transmap_subseteq_reflexive : Reflexive transmap_subseteq.
  Proof. intros ??. done. Qed.

  #[global]
  Instance transmap_subseteq_transitive : Transitive transmap_subseteq.
  Proof. intros ??? H1 H2 ?. etrans. - apply H1. - apply H2. Qed.

  #[global]
  Instance transmap_subseteq_preorder : PreOrder transmap_subseteq.
  Proof. constructor; apply _. Qed.

  #[global]
  Instance transmap_subseteq_antisym : AntiSymm eq transmap_subseteq.
  Proof. intros ?? H1 H2. (* apply function_extensionality. lol jk. *) Abort.

  #[global]
  Instance transmap_union : Union TransMap :=
    λ p1 p2 i, p1 i ∪ p2 i.

  Lemma transmap_union_subseteq_l transmap1 transmap2 :
    transmap1 ⊆ transmap1 ∪ transmap2.
  Proof. intros ?. apply map_union_subseteq_l. Qed.

  (** Every pick in [transmap] is a valid generational transformation and satisfies
  the conditions for that cmra in [Ω]. *)
  Definition transmap_valid (transmap : TransMap) :=
    ∀ i γ t, transmap i !! γ = Some t → GenTrans t.

  (** Build a global generational transformation based on the transformations
   * in [transmap]. *)
  Definition build_trans (transmap : TransMap) : (iResUR Σ → iResUR Σ) :=
    λ (m : iResUR Σ) (i : gid Σ),
      match Oeq Ω i with
      | Some2 eq =>
        map_imap (λ γ (a : Rpre Σ i),
        (* If the map of transmap contains a transformation then we apply the
         * transformation. If no pick exists then we return the elemment
         * unchanged. Hence, we default to the identity transformation. *)
        match transmap i !! γ with
        | Some picked_gt =>
            let trans := cmra_map_transport eq (gen_cmra_trans _ (picked_gt))
            in Some $ map_unfold $ trans $ map_fold a
        | None => Some a
        end) (m i)
      | None2 => m i
      end.

  Lemma core_Some_pcore {A : cmra} (a : A) : core (Some a) = pcore a.
  Proof. done. Qed.

  #[global]
  Lemma build_trans_generation transmap :
    transmap_valid transmap → GenTrans (build_trans transmap).
  Proof.
    intros transmapGT.
    rewrite /build_trans.
    split.
    - rewrite /Proper.
      intros ??? eq i γ.
      specialize (eq i γ).
      destruct (Oeq Ω i); last apply eq.
      rewrite 2!map_lookup_imap.
      destruct (y i !! γ) as [b|] eqn:look1; rewrite look1; rewrite look1 in eq; simpl.
      2: { apply dist_None in eq. rewrite eq. done. }
      (* destruct eq as [a b eq'|hipo] eqn:qqq; simpl. 2: { } last done. *)
      apply dist_Some_inv_r' in eq as (a & look2 & eq).
      apply symmetry in eq.
      rewrite look2.
      destruct (transmap i !! γ) eqn:look.
      * apply transmapGT in look as [gt ?]. simpl.
        admit.
        (* Trivial but Coq is stupid. *)
        (* solve_proper. *)
      * solve_proper.
    - intros ?? Hval.
      intros i γ.
      destruct (Oeq Ω i); last apply Hval.
      rewrite !map_lookup_imap. simpl.
      specialize (Hval i γ).
      destruct (a i !! γ) eqn:eq; rewrite eq /=; last done.
      rewrite eq in Hval.
      destruct (transmap i !! γ) as [pick|] eqn:eq2.
      * apply Some_validN.
        apply: cmra_morphism_validN.
        apply Some_validN.
        specialize (transmapGT i γ pick eq2) as [??].
        rewrite /cmra_map_transport.
        admit.
        (* apply generation_valid. *)
        (* apply: cmra_morphism_validN. *)
        (* apply Hval. *)
      * done.
    - move=> m /=.
      rewrite cmra_pcore_core.
      simpl.
      f_equiv.
      intros i γ.
      rewrite lookup_core.
      destruct (Oeq Ω i). 2: { rewrite lookup_core. reflexivity. }
      rewrite 2!map_lookup_imap.
      rewrite lookup_core.
      destruct (m i !! γ) as [a|] eqn:look; rewrite look; simpl; last done.
      simpl.
      rewrite core_Some_pcore.
      destruct (transmap i !! γ) as [pick|] eqn:pickLook; simpl.
      * rewrite core_Some_pcore.
        rewrite -cmra_morphism_pcore.
        specialize (transmapGT i γ pick pickLook) as ?.
        admit.
        (* rewrite -generation_pcore. *)
        (* rewrite -(cmra_morphism_pcore map_fold). *)
        (* (* rewrite -cmra_morphism_pcore. *) *)
        (* destruct (pcore a); try done. *)
      * rewrite core_Some_pcore.
        destruct (pcore a); done.
    - intros m1 m2.
      intros i γ.
      rewrite 2!discrete_fun_lookup_op.
      destruct (Oeq Ω i); last reflexivity.
      rewrite !map_lookup_imap.
      rewrite 2!lookup_op.
      rewrite !map_lookup_imap.
      destruct (transmap i !! γ) as [pick|] eqn:pickLook.
      * specialize (transmapGT i γ pick pickLook) as ?.
        destruct (m1 i !! γ) eqn:eq1; destruct (m2 i !! γ) eqn:eq2;
          rewrite eq1 eq2; simpl; try done.
        rewrite -Some_op.
        admit.
        (* rewrite -cmra_morphism_op -generation_op -cmra_morphism_op. *)
        (* done. *)
      * destruct (m1 i !! γ) eqn:eq1; destruct (m2 i !! γ) eqn:eq2;
          rewrite eq1 eq2; simpl; try done.
  Admitted.

  (** A map of picks that for the resource at [idx] and the ghost name [γ] picks
  the generational transformation [t]. *)
  Definition transmap_singleton i (γ : gname)
      (t : Oc Ω i → Oc Ω i) : TransMap :=
    λ j, match decide (i = j) with
           left Heq =>
             (eq_rect _ (λ i, gmap gname (Oc Ω i → _)) {[ γ := t ]} _ Heq)
         | right _ => ∅
         end.

  Definition transmap_singleton_lookup idx γ (f : Oc Ω idx → Oc Ω idx) :
    transmap_singleton idx γ f idx !! γ = Some f.
  Proof.
    rewrite /transmap_singleton.
    case (decide (idx = idx)); last by congruence.
    intros eq'.
    assert (eq' = eq_refl) as ->.
    { rewrite (proof_irrel eq' eq_refl). done. }
    simpl.
    apply lookup_singleton.
  Qed.

  Definition transmap_singleton_dom_index_eq idx γ f :
    dom (transmap_singleton idx γ f idx) = {[ γ ]}.
  Proof.
    rewrite /transmap_singleton.
    case (decide (idx = idx)); last congruence.
    intros [].
    simpl.
    apply dom_singleton_L.
  Qed.

  Definition transmap_singleton_dom_index_neq idx γ f idx' :
    idx ≠ idx' →
    dom (transmap_singleton idx γ f idx') = ∅.
  Proof.
    intros neq.
    rewrite /transmap_singleton.
    case (decide (idx = idx')); first congruence.
    intros ?.
    apply dom_empty_L.
  Qed.

  Definition gen_f_singleton_lookup_Some idx' idx γ γ' f (f' : Oc Ω idx' → _) :
    (transmap_singleton idx γ f) idx' !! γ' = Some f' →
    ∃ (eq : idx' = idx),
      γ = γ' ∧
      f = match eq in (_ = r) return (Oc Ω r → Oc Ω r) with eq_refl => f' end.
  Proof.
    rewrite /transmap_singleton.
    case (decide (idx = idx')); last first.
    { intros ?. rewrite lookup_empty. inversion 1. }
    intros ->.
    simpl.
    intros [-> ->]%lookup_singleton_Some.
    exists eq_refl.
    done.
  Qed.

End transmap.

Arguments TransMap {Σ} _. (* : clear implicits. *)

(** Information about a promise _except_ for any information concerning its
 * dependencies. This lets us talk about a promise without having to talk
 * about it's depencencies (and their dependencies, and their dependencies,
 * and so on recursively). *)
Record promise_self_info {Σ} Ω := MkPromiseSelfInfo {
  psi_id : gid Σ; (* The index of the RA in the global RA. *)
  psi_γ : gname; (* Ghost name for the promise. *)
  psi_pred : cmra_to_pred (Oc Ω psi_id);
}.

Arguments psi_id {_ _}.
Arguments psi_γ {_ _}.
(* Arguments psi_gcd {_ _}. *)
(* Arguments psi_gcd_lookup {_ _}. *)
Arguments psi_pred {_ _}.

(* Definition deps_to_trans n (deps : ivec n promise_self_info) := *)
(*   hvec (λ dep, T Σ dep.(psi_id)) n deps. *)

  (* Definition deps_to_gnames {n} (deps : ivec n promise_self_info) := *)
  (*   ivec_map (λ dep, dep.(psi_γ)) deps. *)

  (* (** The transformations [ts] satisfies the predicates [ps]. *) *)
  (* Equations deps_preds_hold {n} *)
  (*     (deps : ivec n promise_self_info) *)
  (*     (ts : deps_to_trans n deps) : Prop := *)
  (*   | inil, hnil := True *)
  (*   | icons d deps', hcons t ts' := d.(psi_pred) t ∧ deps_preds_hold deps' ts'. *)
  (* (* Global Transparent deps_preds_hold. *) *)

(*   Lemma deps_preds_hold_alt {n} *)
(*       (deps : ivec n promise_self_info) *)
(*       (ts : hvec (λ dep, T Σ dep.(psi_id)) n deps) : *)
(*     deps_preds_hold deps ts ↔ ∀ i, (deps !!! i).(psi_pred) (ts 👀 i). *)
(*   Proof. *)
(*     split. *)
(*     - intros holds i. *)
(*       induction i as [hi|ho] eqn:eq. *)
(*       * dependent elimination ts. *)
(*         destruct holds as [pred ?]. *)
(*         apply pred. *)
(*       * dependent elimination deps. *)
(*         dependent elimination ts. *)
(*         rewrite deps_preds_hold_equation_2 in holds. *)
(*         destruct holds as [? holds]. *)
(*         apply (IHt _ _ holds t). *)
(*         done. *)
(*     - intros i. *)
(*       induction deps. *)
(*       * dependent elimination ts. done. *)
(*       * dependent elimination ts. *)
(*         rewrite deps_preds_hold_equation_2. *)
(*         split. { apply (i 0%fin). } *)
(*         apply IHdeps. *)
(*         intros i'. *)
(*         apply (i (FS i')). *)
(*   Qed. *)
(* End promises. *)

(** Inside the model of the [nextgen] modality we need to store a list of all
 * known promises. To this end, [promise_info] is a record of all the
 * information that is associated with a promise. Note that we use
 * [promise_self_info] for the dependencies, this cuts off what would
 * otherwise be an inductive record - simplifying things at the cost of some
 * power.
 *
 * NOTE: We can not store cameras directly in [promise_info] as that leads to
 * universe issues (in particular, any Iris existential quantification over
 * something involing a [cmra] fails. We hence store all cameras in [Ω] and
 * look up into it). *)
Record promise_info_at {Σ} (Ω : gGenCmras Σ) id := {
  (* We have the generational cmra data for this index, this contains all
   * static info about the promise dependency for this index. *)
  pi_deps_γs : ivec (On Ω id) gname;
  pi_deps_preds : preds_for (On Ω id) (Ocs Ω id);
  (* Dynamic information that changes per promise *)
  (* The predicate that relates our transformation to those of the dependencies. *)
  (* NOTE: Maybe store the rel in curried form? *)
  pi_rel : pred_over (Ocs Ω id) (Oc Ω id);
  (* A predicate that holds for the promise's own transformation whenever
   * [pi_rel] holds. A "canonical" choice could be: [λ t, ∃ ts, pi_rel ts t]. *)
  pi_pred : cmra_to_pred (Oc Ω id);
  pi_rel_to_pred : ∀ (ts : trans_for (On Ω id) (Ocs Ω id)) t,
    huncurry pi_rel ts t → pi_pred t;
  pi_witness : ∀ (ts : trans_for (On Ω id) (Ocs Ω id)),
    preds_hold pi_deps_preds ts → ∃ t, huncurry pi_rel ts t;
}.

Record promise_info {Σ} (Ω : gGenCmras Σ) := MkPromiseInfo {
  (* We need to know the specific ghost location that this promise is about *)
  pi_id : gid Σ; (* The index of the RA in the global RA *)
  pi_γ : gname; (* Ghost name for the promise *)
  (* With this coercion the inner [promise_info_at] record behaves as if it was
   * included in [promise_info] directly. *)
  pi_at :> promise_info_at Ω pi_id;
}.

(* Check that we can existentially quantify over [promise_info] without
 * universe inconsistencies. *)
#[local] Definition promise_info_universe_test {Σ} {Ω : gGenCmras Σ} : iProp Σ :=
  ∃ (ps : promise_info Ω), True.

Arguments MkPromiseInfo {_ _}.

Arguments pi_id {_ _}.
Arguments pi_γ {_ _}.
Arguments pi_at {_ _}.

Arguments pi_deps_γs {_ _ _}.
Arguments pi_deps_preds {_ _ _}.
Arguments pi_rel {_ _ _}.
Arguments pi_pred {_ _ _}.
Arguments pi_rel_to_pred {_ _ _}.
Arguments pi_witness {_ _ _}.

Definition lookup_fmap_Ocs `{Ω : gGenCmras Σ} {f id}
    (cs : hvec (On Ω id) (f <$> Ocs Ω id)) i : f (Oc Ω (Oids Ω id !!! i)) :=
  eq_rect _ _ (hvec_lookup_fmap cs i) _ (Ocs_Oids_distr _ _).

Definition pi_get_dep {Σ} {Ω : gGenCmras Σ} (pi : promise_info Ω) n : promise_self_info Ω :=
  let id := Oids Ω pi.(pi_id) !!! n in
  let γ := pi.(pi_deps_γs) !!! n in
  let pred : cmra_to_pred (Oc Ω id) := lookup_fmap_Ocs pi.(pi_deps_preds) n in
  MkPromiseSelfInfo  _ _ id γ pred.

Section promise_info.
  Context `{Ω : gGenCmras Σ}.

  Implicit Types (prs : list (promise_info Ω)).
  Implicit Types (promises : list (promise_info Ω)).
  Implicit Types (pi : promise_info Ω).

  (** Convert a [promise_info] into a [promise_self_info] by discarding fields
   * about dependencies. *)
  Definition promise_info_to_self pi :=
    {| psi_id := pi_id pi; psi_γ := pi_γ pi; psi_pred := pi_pred pi |}.

  Definition promises_different p1 p2 :=
    p1.(pi_id) ≠ p2.(pi_id) ∨ p1.(pi_γ) ≠ p2.(pi_γ).

  Definition promises_self_different p1 p2 :=
    p1.(psi_id) ≠ p2.(psi_id) ∨ p1.(psi_γ) ≠ p2.(psi_γ).

  Definition res_trans_transport {id1 id2}
      (eq : id1 = id2) (t : R Σ id1 → R Σ id1) : (R Σ id2 → R Σ id2) :=
    eq_rect _ (λ id, _) t _ eq.

  Definition res_pred_transport {id1 id2} (eq : id1 = id2)
      (t : (R Σ id1 → R Σ id1) → Prop) : ((R Σ id2 → R Σ id2) → Prop) :=
    eq_rect _ (λ id, _) t _ eq.

  Definition gcd_transport {id1 id2}
      (eq : id1 = id2) (gcd : gen_cmra_data Σ id1) : gen_cmra_data Σ id2 :=
    eq_rect _ (λ id, _) gcd _ eq.

  (* Definition pred_gcd_transport {p_d ps} *)
  (*     (eq1 : p_d.(psi_id) = ps.(pi_id)) *)
  (*     (eq2 : gcd_transport eq1 (psi_gcd p_d) = pi_gcd ps) *)
  (*     (psi_pred : cmra_to_pred (gcd_cmra (psi_gcd p_d))) : *)
  (*     (gcd_cmra (pi_gcd ps) → gcd_cmra (pi_gcd ps)) → Prop. *)
  (* Admitted. *)
  (*   (* match eq1 with *) *)
  (*   (* | eq_refl => eq_rect _ (λ id, cmra_to_pred (gcd_cmra id)) psi_pred _ eq2 *) *)
  (*   (* end. *) *)

  (** The promise [p] satisfies the dependency [p_d]. Note that the predicate
   * in [p_d] may not be the same as the one in [p]. When we combine lists of
   * promises some promises might be replaced by stronger ones. Hence we only
   * require that the predicate in [p] is stronger than the one in [p_d]. *)
  Definition promise_satisfy_dep (p_d : promise_self_info Ω) ps :=
    ∃ (eq : p_d.(psi_id) = ps.(pi_id)),
      p_d.(psi_γ) = ps.(pi_γ) ∧
      (* The predicate in [ps] is stronger than what is stated in [p_d] *)
      (* pred_stronger ps.(pi_pred) p_d.(psi_pred). *)
      pred_stronger ps.(pi_pred) (eq_rect _ (λ id, cmra_to_pred (Oc Ω id)) p_d.(psi_pred) _ eq).

  (** For every dependency in [p] the list [promises] has a sufficient
   * promise. *)
  Definition promises_has_deps pi promises :=
    ∀ idx, ∃ p2, p2 ∈ promises ∧ promise_satisfy_dep (pi_get_dep pi idx) p2.

  (** The promise [p] is well-formed wrt. the list [promises] of promises that
   * preceeded it. *)
  Definition promise_wf pi promises : Prop :=
    (∀ p2, p2 ∈ promises → promises_different pi p2) ∧
    promises_has_deps pi promises.

  (* This definition has nice computational behavior when applied to a [cons]. *)
  Fixpoint promises_wf promises : Prop :=
    match promises with
    | nil => True
    | cons p promises' => promise_wf p promises' ∧ promises_wf promises'
    end.

  (* NOTE: Not used, but should be implied by [promises_wf] *)
  Definition promises_unique promises : Prop :=
    ∀ (i j : nat) pi1 pi2, i ≠ j →
      (* promises !! i = Some p1 → promises !! j = Some p2 → *)
      pi1.(pi_id) ≠ pi2.(pi_id) ∨ pi1.(pi_γ) ≠ pi2.(pi_γ).

  Lemma promises_has_deps_cons p prs :
    promises_has_deps p prs →
    promises_has_deps p (p :: prs).
  Proof.
    intros hasDeps idx.
    destruct (hasDeps idx) as (p2 & ? & ?).
    eauto using elem_of_list_further.
  Qed.

  (* A well formed promise is not equal to any of its dependencies. *)
  Lemma promise_wf_neq_deps p promises :
    promise_wf p promises →
    ∀ (idx : fin (On Ω p.(pi_id))),
      promises_self_different (promise_info_to_self p) (pi_get_dep p idx).
      (* pi_id p ≠ dd_id (pi_get_dd p idx) ∨ pi_γ p ≠ dd_γ (pi_get_dd p idx). *)
  Proof.
    intros [uniq hasDeps] idx.
    rewrite /promises_self_different.
    destruct (hasDeps idx) as (p2 & elem & idEq & γEq & jhhi).
    rewrite idEq γEq.
    destruct (uniq _ elem) as [?|?]; auto.
  Qed.

  Lemma promises_well_formed_lookup promises (idx : nat) pi :
    promises_wf promises →
    promises !! idx = Some pi →
    promises_has_deps pi promises. (* We forget the different part for now. *)
  Proof.
    intros WF look.
    revert dependent idx.
    induction promises as [ |?? IH]; first intros ? [=].
    destruct WF as [[? hasDeps] WF'].
    intros [ | idx].
    * simpl. intros [= ->].
      apply promises_has_deps_cons.
      done.
    * intros look.
      intros d.
      destruct (IH WF' idx look d) as (? & ? & ?).
      eauto using elem_of_list_further.
  Qed.

  (* For soundness we need to be able to build a map of gts that agree with
   * picks and that satisfy all promises.

     We need to be able to extend picks along a list of promises.

     We must also be able to combine to lists of promises.
  *)

  Equations promises_lookup_at promises iid (γ : gname) : option (promise_info_at _ iid) :=
  | [], iid, γ => None
  | p :: ps', iid, γ with decide (p.(pi_id) = iid), decide (p.(pi_γ) = γ) => {
    | left eq_refl, left eq_refl => Some p.(pi_at);
    | left eq_refl, right _ => promises_lookup_at ps' p.(pi_id) γ
    | right _, _ => promises_lookup_at ps' iid γ
  }.

  (* NOTE: Not sure if this function is a good idea. *)
  Definition promises_lookup promises id γ : option (promise_info _) :=
    MkPromiseInfo id γ <$> (promises_lookup_at promises id γ).

  Lemma promises_lookup_at_Some promises id γ pia :
    promises_lookup_at promises id γ = Some pia →
    MkPromiseInfo id γ pia ∈ promises.
  Proof.
    induction promises as [|[id' γ' ?] ? IH]; first by inversion 1.
    rewrite promises_lookup_at_equation_2.
    rewrite promises_lookup_at_clause_2_equation_1.
    simpl.
    destruct (decide (id' = id)) as [->|neq].
    - destruct (decide (γ' = γ)) as [->|neq].
      * simpl.
        intros [= <-].
        apply elem_of_list_here.
      * rewrite promises_lookup_at_clause_2_clause_1_equation_2.
        intros look.
        apply elem_of_list_further.
        apply IH.
        apply look.
    - rewrite promises_lookup_at_clause_2_clause_1_equation_3.
      intros look.
      apply elem_of_list_further.
      apply IH.
      done.
  Qed.

  Definition promise_stronger {id} (pia1 pia2 : promise_info_at _ id) : Prop :=
    rel_stronger pia1.(pi_rel) pia2.(pi_rel)
    (* pred_stronger p1.(pi_pred) p2.(pi_pred) ∨ *)
    .

  (** This definition is supposed to encapsulate what ownership over the
   * resources for [prs1] and [prs2] entails. *)
  Definition promises_overlap_pred prs1 prs2 : Prop :=
    ∀ id γ p1 p2,
      promises_lookup_at prs1 id γ = Some p1 →
      promises_lookup_at prs2 id γ = Some p2 →
      promise_stronger p1 p2 ∨ promise_stronger p2 p1.

  (* (* FIXME: We need to take the strongest promise when two exist for the same *)
  (*  * idx and gname. *) *)
  (* Fixpoint merge_promises prs1 prs2 := *)
  (*   match prs1 with *)
  (*   | [] => prs2 *)
  (*   | p :: prs1' => *)
  (*     if decide (promises_lookup prs2 p.(pi_id) p.(pi_γ) = None) *)
  (*     then p :: (merge_promises prs1' prs2) *)
  (*     else merge_promises prs1' prs2 *)
  (*   end. *)

  (* Lemma merge_promises_elem p prs1 prs2 : *)
  (*   p ∈ merge_promises prs1 prs2 → *)
  (*   p ∈ prs1 ∨ p ∈ prs2. *)
  (* Proof. *)
  (* Admitted. *)

  (* How to merge promises, intuitively?
   * 1. From the first list add the suffix of promises not in the other.
   * 2. From the second list add the suffix of promises not in the other.
   * 3. The last element in both lists is now also present in the other.
   *    - If they are for the same id+γ then add the strongest.
   *    - If one of them is stronger than the one in the other list then add that one.
   *    - If they are both weaker???
   *)
  Lemma merge_promise_lists prs1 prs2 :
    promises_wf prs1 →
    promises_wf prs2 →
    ∃ prs3,
      promises_wf prs3 ∧
      (∀ pi, pi ∈ prs3 → pi ∈ prs1 ∨ pi ∈ prs2) ∧
      (∀ id γ pia1 pia2,
        promises_lookup_at prs1 id γ = Some pia1 →
        promises_lookup_at prs2 id γ = Some pia2 →
        promise_stronger pia2 pia1).
  Proof.
  Admitted.

  Lemma promises_lookup_different p p2 prs2 :
    p2 ∈ prs2 →
    promises_lookup prs2 (pi_id p) (pi_γ p) = None →
    promises_different p p2.
  Proof.
  Admitted.

  (* Lemma merge_promises_wf prs1 prs2 : *)
  (*   promises_wf prs1 → *)
  (*   promises_wf prs2 → *)
  (*   promises_wf (merge_promises prs1 prs2). *)
  (* Proof. *)
  (*   intros wf1 wf2. *)
  (*   induction prs1 as [|p prs1 IH]; first done. *)
  (*   simpl. *)
  (*   destruct (decide (promises_lookup prs2 (pi_id p) (pi_γ p) = None)) as [eq|eq]. *)
  (*   - simpl. *)
  (*     split; last (apply IH; apply wf1). *)
  (*     split. *)
  (*     * intros p2. *)
  (*       intros [in1|in2]%merge_promises_elem. *)
  (*       + apply wf1. done. *)
  (*       + eapply promises_lookup_different; done. *)
  (*     * admit. *)
  (*   - apply IH. apply wf1. *)
  (* Admitted. *)

  (* When we store picks we also need to store the promises that they are
   * related with. We store these promises in a map. This map should contain
   * promises at the "right" indices which this definition expresses. *)
  (* NOTE: Not used *)
  Definition promise_map_wf (pm : ∀ i, gmap gname _) : Prop :=
    ∀ i γ p, (pm i) !! γ = Some p → p.(pi_id) = i ∧ p.(pi_γ) = γ.

End promise_info.

Section transmap.
  Context `{Ω : gGenCmras Σ}.

  Implicit Types (transmap : TransMap Ω).
  Implicit Types (ps : list (promise_info Ω)).

  (* We need to:
    - Be able to turn a list of promises and a map of picks into a
      global transformation.
    - Say that a set of picks respects a list of promises.
    - Merge two lists of promises.
   *)

  (* Definition trans_at_deps transmap (p : promise_info Ω) *)
  (*     (trans : deps_to_trans p.(pi_n) p.(pi_deps)) := *)
  (*   ∀ idx, *)
  (*     let dep := p.(pi_deps) !!! idx *)
  (*     in transmap dep.(psi_id) !! dep.(psi_γ) = Some (trans 👀 idx). *)

  (** A vector that for every dependency in [p] contains the transition in
  * [transmap] for that dependency. *)
  Definition trans_at_deps transmap (p : promise_info Ω)
      (trans : hvec (On Ω (pi_id p)) (cmra_to_trans <$> Ocs Ω (pi_id p))) :=
    ∀ idx,
      let id := Oids Ω p.(pi_id) !!! idx in
      let γ := p.(pi_deps_γs) !!! idx in
      let t : Oc Ω id → Oc Ω id := lookup_fmap_Ocs trans idx in
      transmap id !! γ = Some t.

  (** The transformations in [transmap] satisfy the relation in [p]. *)
  Definition transmap_satisfy_rel transmap p :=
    ∃ trans t,
      transmap p.(pi_id) !! p.(pi_γ) = Some t ∧
      trans_at_deps transmap p trans ∧
      huncurry p.(pi_rel) trans t.

  (** The [transmap] respect the promises in [ps]: There is a pick for every
   * promise and all the relations in the promises are satisfied by the
   * transformations in transmap. *)
  Definition transmap_resp_promises transmap ps :=
    Forall (transmap_satisfy_rel transmap) ps.

  Definition Oc_trans_transport {id1 id2} (eq : id1 = id2)
    (o : Oc Ω id1 → _) : Oc Ω id2 → Oc Ω id2 :=
      eq_rect _ (λ id, Oc Ω id → Oc Ω id) o _ eq.

  Lemma promises_has_deps_resp_promises p idx p_d promises transmap :
    pi_get_dep p idx = p_d →
    promises_has_deps p promises →
    transmap_resp_promises transmap promises →
    ∃ t, psi_pred p_d t ∧ transmap (psi_id p_d) !! psi_γ p_d = Some t.
  Proof.
    intros look hasDeps resp.
    rewrite /transmap_resp_promises Forall_forall in resp.
    rewrite -look.
    specialize (hasDeps idx) as (p2 & Helem & eq1 & eq2 & strong).
    destruct (resp _ Helem) as (ts & (t & tmLook & ? & relHolds)).
    specialize (p2.(pi_rel_to_pred) ts t relHolds) as predHolds.
    exists (Oc_trans_transport (eq_sym eq1) t).
    split.
    * apply strong in predHolds.
      clear -predHolds. destruct eq1. simpl. done.
    * rewrite eq2. clear -tmLook. destruct eq1. apply tmLook.
  Qed.

  (* What would a more general version of this lemma look like? *)
  Lemma rew_cmra_to_pred (x : cmra) f y (eq : x = y) t :
    (eq_rect x cmra_to_pred f y eq) t = f (eq_rect_r cmra_to_trans t eq).
  Proof. destruct eq. done. Qed.

  (** If a [transmap] respects a list [promises] and growing the list with [p]
   * is well formed, then we can conjur up a list of transitions from
   * [transmap] that match the dependencies in [p] and that satisfy their
   * predicates. *)
  Lemma transmap_satisfy_wf_cons p promises transmap :
    promises_wf (p :: promises) →
    transmap_resp_promises transmap promises →
    ∃ ts,
      trans_at_deps transmap p ts ∧
      preds_hold p.(pi_deps_preds) ts.
  Proof.
    intros WF resp.
    destruct WF as [[uniq hasDeps] WF'].
    edestruct (fun_ex_to_ex_hvec_fmap (F := cmra_to_trans) (Ocs Ω (pi_id p))
      (λ i t,
        let t' := eq_rect _ _ t _ (Ocs_Oids_distr _ _) in
        let pred := hvec_lookup_fmap p.(pi_deps_preds) i in
        pred t ∧
        transmap (Oids Ω p.(pi_id) !!! i) !! (p.(pi_deps_γs) !!! i) = Some t'))
      as (ts & ?).
    { intros idx.
      specialize (promises_has_deps_resp_promises _ _ (pi_get_dep p idx) _ transmap eq_refl hasDeps resp).
      intros (t & ? & ?).
      exists (eq_rect_r _ t (Ocs_Oids_distr _ _)).
      simpl.
      split.
      * rewrite /pi_get_dep /lookup_fmap_Ocs in H.
        simpl in H.
        clear -H.
        rewrite <- rew_cmra_to_pred.
        apply H.
      * rewrite H0.
        rewrite rew_opp_r.
        done. }
    exists ts.
    split.
    - intros di. apply H.
    - apply preds_hold_alt. intros di.
      apply (H di).
  Qed.

  Equations transmap_insert_go transmap (id : gid Σ) (γ : gname) (pick : Oc Ω id → Oc Ω id)
    (id' : gid Σ) : gmap gname (Oc Ω id' → Oc Ω id') :=
  | transmap, _, γ, pick, id', with decide (id = id') => {
    | left eq_refl => <[ γ := pick ]>(transmap id')
    | right _ => transmap id'
  }.

  Definition transmap_insert transmap id γ pick : TransMap Ω :=
    transmap_insert_go transmap id γ pick.

  Lemma transmap_insert_lookup transmap id γ t  :
    (transmap_insert transmap id γ t) id !! γ = Some t.
  Proof.
    rewrite /transmap_insert.
    rewrite transmap_insert_go_equation_1.
    destruct (decide (id = id)) as [eq | neq]; last congruence.
    assert (eq = eq_refl) as ->.
    { rewrite (proof_irrel eq eq_refl). done. }
    simpl.
    rewrite lookup_insert. done.
  Qed.

  Lemma transmap_insert_lookup_ne transmap id1 γ1 t id2 γ2 :
    id1 ≠ id2 ∨ γ1 ≠ γ2 →
    (transmap_insert transmap id1 γ1 t) id2 !! γ2 = transmap id2 !! γ2.
  Proof.
    intros neq.
    rewrite /transmap_insert.
    rewrite transmap_insert_go_equation_1.
    destruct (decide (id1 = id2)) as [eq | neq2]; last done.
    destruct neq as [neq | neq]; first congruence.
    subst. simpl.
    rewrite lookup_insert_ne; done.
  Qed.

  Lemma transmap_insert_subseteq_r i γ t transmap1 transmap2 :
    transmap1 i !! γ = None →
    transmap1 ⊆ transmap2 →
    transmap1 ⊆ transmap_insert transmap2 i γ t.
  Proof.
    intros look sub.
    intros i'.
    apply map_subseteq_spec => γ' t' look'.
    destruct (decide (i = i' ∧ γ = γ')) as [[-> ->]|Hneq].
    - congruence.
    - rewrite transmap_insert_lookup_ne.
      * specialize (sub i').
        rewrite map_subseteq_spec in sub.
        apply sub.
        done.
      * apply not_and_r in Hneq; done.
  Qed.

  Lemma transmap_resp_promises_insert p promises transmap t :
    promises_wf (p :: promises) →
    transmap_resp_promises transmap promises →
    transmap_resp_promises (transmap_insert transmap (pi_id p) (pi_γ p) t) promises.
  Proof.
    intros [[uniq hasDeps] WF].
    rewrite /transmap_resp_promises !Forall_forall.
    intros impl p2 elem.
    destruct (impl _ elem) as (t' & ts & rest).
    exists t', ts.
    rewrite /trans_at_deps.
    (* NOTE: This proof might be a bit of a mess. *)
    setoid_rewrite transmap_insert_lookup_ne.
    + apply rest.
    + apply (uniq _ elem).
    + apply elem_of_list_lookup_1 in elem as (? & look).
      specialize (
        promises_well_formed_lookup promises _ p2 WF look) as hasDeps2.
      specialize (hasDeps2 idx) as (p3 & look3 & eq & eq2 & ?).
      simpl in *.
      rewrite eq2.
      destruct p3.
      specialize (uniq _ look3) as [? | ?].
      - rewrite eq. left. done.
      - right. done.
  Qed.

  Definition transmap_overlap_resp_promises transmap ps :=
    ∀ i p, ps !! i = Some p →
      transmap_satisfy_rel transmap p ∨ (transmap p.(pi_id) !! p.(pi_γ) = None).

  Lemma trans_at_deps_subseteq transmap1 transmap2 p ts :
    transmap1 ⊆ transmap2 →
    trans_at_deps transmap1 p ts →
    trans_at_deps transmap2 p ts.
  Proof.
    intros sub ta.
    intros idx. simpl.
    specialize (sub (psi_id (pi_get_dep p idx))).
    rewrite map_subseteq_spec in sub.
    specialize (ta idx).
    apply sub.
    apply ta.
  Qed.

  Lemma transmap_overlap_resp_promises_cons transmap p promises :
    transmap_overlap_resp_promises transmap (p :: promises) →
    transmap_overlap_resp_promises transmap promises.
  Proof. intros HL. intros i ? look. apply (HL (S i) _ look). Qed.

  (* Grow a transformation map to satisfy a list of promises. This works by
  * traversing the promises and using [promise_info] to extract a
  * transformation. *)
  Lemma transmap_promises_to_maps transmap promises :
    transmap_overlap_resp_promises transmap promises →
    promises_wf promises →
    ∃ (map : TransMap Ω),
      transmap_resp_promises map promises ∧
      transmap ⊆ map.
  Proof.
    induction promises as [|p promises' IH].
    - intros _. exists transmap.
      split; last done.
      apply Forall_nil_2.
    - intros HR [WF WF'].
      specialize (promise_wf_neq_deps _ _ WF) as depsDiff.
      destruct IH as (map & resp & sub).
      {  eapply transmap_overlap_resp_promises_cons. done. } { done. }
      (* We either need to use the transformation in [picks] or extract one
       * from [p]. *)
      destruct (transmap p.(pi_id) !! p.(pi_γ)) eqn:look.
      + destruct (HR 0 p) as [sat | ?]; [done | | congruence].
        destruct sat as (ts & t & transIn & hold & pRelHolds).
        exists map. (* We don't insert as map already has transformation. *)
        split; last done.
        apply Forall_cons.
        split; try done.
        eexists _, _. split_and!; last done.
        -- specialize (sub p.(pi_id)).
           rewrite map_subseteq_spec in sub.
           apply sub.
           done.
        -- eapply trans_at_deps_subseteq; done.
      + eassert _ as sat.
        { eapply transmap_satisfy_wf_cons; done. }
        destruct sat as (ts & transIn & hold).
        eassert (∃ t, _) as [t pRelHolds].
        { apply p.(pi_witness). apply hold. }
        exists (transmap_insert map p.(pi_id) p.(pi_γ) t).
        split.
        * apply Forall_cons.
          split.
          -- rewrite /transmap_satisfy_rel.
            exists ts, t.
            split. { by rewrite transmap_insert_lookup. }
            split; last done.
            intros ??.
            simpl.
            rewrite transmap_insert_lookup_ne; first apply transIn.
            apply depsDiff.
          -- apply transmap_resp_promises_insert; done.
        * apply transmap_insert_subseteq_r; done.
  Qed.

  Lemma promises_to_maps (promises : list _) :
    promises_wf promises →
    ∃ (transmap : TransMap _), transmap_resp_promises transmap promises.
  Proof.
    intros WF.
    edestruct (transmap_promises_to_maps (λ i : gid Σ, ∅)) as [m [resp a]].
    2: { done. }
    - intros ???. right. done.
    - exists m. apply resp.
  Qed.

End transmap.

(* Arguments promise_info Σ : clear implicits. *)
(* Arguments promise_self_info Σ : clear implicits. *)

Section next_gen_definition.
  Context `{Ω : gGenCmras Σ}.

  Implicit Types (picks : TransMap Ω).

  (* Every generational ghost location consists of a camera and a list of
   * cameras for the dependencies. *)

  (* If a transformation has been picked for one ghost name, then all the
   * dependencies must also have been picked. *)

  (* The resource [m] contains the agreement resources for all the picks in
   * [picks]. We need to know that a picked transformation satisfies the most
   * recent/strongest promise. We thus need the authorative part of the
   * promises. *)
  Definition res_for_picks picks (m : iResUR Σ) :=
    ∀ i,
      dom (picks i) ≡ dom (m i) ∧
      ∀ γ (a : Rpre Σ i),
        m i !! γ = Some a →
        ∃ eq ts γs (t : Oc Ω i → Oc Ω i) R Rs,
          Oeq Ω i = Some2 eq ∧
          (* BUG: [ts] is unrestricted. The transformations in [ts] should be
           * the result of looking up in [picks]. We somehow need some promise
           * info as well here to know which deps to look up. Maybe store the
           * auth in [res_for_promises]? *)
          huncurry R ts t ∧
          picks i !! γ = Some t ∧
          pred_prefix_list_for Rs R ∧
          a ≡ map_unfold (cmra_transport eq
            (ε, GTS_tok_gen_shot t, ε,
             Some (to_agree γs), gV (●□ (to_max_prefix_list Rs)))).

  Definition own_picks picks : iProp Σ :=
    ∃ m, uPred_ownM m ∗ ⌜ res_for_picks picks m ⌝.

  Definition own_promises (ps : list (promise_info Ω)) : iProp Σ :=
    (∀ p, ⌜ p ∈ ps ⌝ →
      ∃ eq Rs,
        ⌜ Oeq Ω p.(pi_id) = Some2 eq ⌝ ∧
        ⌜ pred_prefix_list_for Rs p.(pi_rel) ⌝ ∧
        uPred_ownM (discrete_fun_singleton p.(pi_id)
          {[ p.(pi_γ) := map_unfold
            (cmra_transport eq (ε, ε, ε, ε, gV (◯ (to_max_prefix_list Rs)))) ]}
        )).

  (* The global transformation [fG] respects the entries in [picks].
   * NOTE: We may not need this given how [⚡==>] now quantifies over picks and
   * not global transformations. *)
  Definition gt_resp_picks (fG : iResUR Σ → iResUR Σ) picks :=
    ∀ (m : iResUR Σ) i γ a t eq,
      Oeq Ω i = Some2 eq →
      m i !! γ = Some a → (* For every element in the old element. *)
      picks i !! γ = Some t →
      let t' := cmra_map_transport eq (gen_cmra_trans _ t)
      in (fG m) i !! γ = Some (map_unfold (t' (map_fold a))).

  Definition nextgen P : iProp Σ :=
    ∃ picks (ps : list (promise_info Ω)),
      (* We own resources for everything in [picks] and [promises]. *)
      own_picks picks ∗ own_promises ps ∗
      ⌜ promises_wf ps ⌝ ∗
      ∀ full_picks (val : transmap_valid full_picks),
        ⌜ transmap_resp_promises full_picks ps ⌝ -∗
        ⌜ picks ⊆ full_picks ⌝ -∗
        let _ := build_trans_generation full_picks val in
        ⚡={build_trans full_picks}=> P.

End next_gen_definition.

Notation "⚡==> P" := (nextgen P)
  (at level 99, P at level 200, format "⚡==>  P") : bi_scope.

Section own_picks_properties.
  Context `{Ω : gGenCmras Σ}.
  Implicit Types (picks : TransMap Ω).

  Definition merge_picks picks1 picks2 := λ i, (picks1 i) ∪ (picks2 i).

  Definition map_agree_overlap `{FinMap K M} {A} (m1 m2 : M A) :=
    ∀ (k : K) (i j : A), m1 !! k = Some i → m2 !! k = Some j → i = j.

  Lemma cmra_transport_validI {A B : cmra} (eq : A =@{cmra} B) (a : A) :
    ✓ cmra_transport eq a ⊣⊢@{iPropI Σ} ✓ a.
  Proof. destruct eq. done. Qed.

  Lemma tokens_for_picks_agree_overlap' picks1 picks2 m1 m2 :
    res_for_picks picks1 m1 →
    res_for_picks picks2 m2 →
    uPred_ownM m1 -∗
    uPred_ownM m2 -∗
    ⌜ ∀ i γ a b, (m1 i) !! γ = Some a → (m2 i) !! γ = Some b → a ≡ b ⌝.
  Proof.
    iIntros (t1 t2) "m1 m2". iIntros (i).
    iIntros (γ a1 a2 m1Look m2Look).
    specialize (t1 i) as (domEq1 & m1look).
    edestruct m1look as (gti1 & t1 & ? & ? & ? & ? & ? & ? & picks1Look & ? & eq1);
      first done.
    specialize (t2 i) as (domEq2 & m2look).
    edestruct m2look as (gti2 & t2 & ? & ? & ? & ? & ? & ? & picks2Look & ? & eq2);
      first done.
    clear m1look m2look.
    assert (gti1 = gti2) as -> by congruence.
    iCombine "m1 m2" as "m".
    iDestruct (ownM_valid with "m") as "#Hv".
    rewrite discrete_fun_validI.
    setoid_rewrite gmap_validI.
    iSpecialize ("Hv" $! i γ).
    rewrite lookup_op.
    rewrite m1Look m2Look.
    rewrite option_validI /=.
    rewrite eq1 eq2.
    simplify_eq.
    rewrite map_unfold_op.
    rewrite map_unfold_validI.
    rewrite -cmra_transport_op.
    rewrite cmra_transport_validI.
    rewrite -pair_op.
    rewrite -pair_op.
    rewrite prod_validI.
    rewrite prod_validI.
    rewrite prod_validI.
    rewrite prod_validI.
    iDestruct "Hv" as "((((_ & Hv1) & _) & Hv2) & %Hv3)".
    simpl in Hv3.
    simpl.
    rewrite GTS_tok_gen_shot_foo.
    rewrite -Some_op option_validI to_agree_op_validI.
    iDestruct "Hv1" as %->.
    rewrite gen_pv_op gen_pv_valid in Hv3.
    rewrite auth_auth_dfrac_op_valid in Hv3.
    destruct Hv3 as (? & eq & ?).
    rewrite /map_unfold.
    iDestruct "Hv2" as %hqq.
    apply leibniz_equiv in hqq.
    iPureIntro. f_equiv. f_equiv.
    rewrite hqq.
    rewrite /gV. rewrite /mk_gen_pv.
    split; try done; simpl.
    split; try done; simpl.
    rewrite eq.
    done.
  Qed.

  Lemma m_contains_tokens_for_picks_merge picks1 picks2 (m1 m2 : iResUR Σ) :
    (∀ i γ a b, (m1 i) !! γ = Some a → (m2 i) !! γ = Some b → a ≡ b) →
    res_for_picks picks1 m1 →
    res_for_picks picks2 m2 →
    res_for_picks (merge_picks picks1 picks2) (m1 ⋅ m2).
  Proof.
    intros overlap2 tok1 tok2.
    intros i.
    rewrite /merge_picks.
    rewrite dom_op.
    specialize (tok1 i) as (domEq1 & tok1).
    specialize (tok2 i) as (domEq2 & tok2).
    split.
    { rewrite -domEq1 -domEq2. rewrite dom_union. done. }
    intros γ a.
    rewrite discrete_fun_lookup_op.
    rewrite lookup_op.
    case (m1 i !! γ) eqn:look1; rewrite look1;
      case (m2 i !! γ) eqn:look2; rewrite look2.
    - specialize (overlap2 i _ _ _ look1 look2) as elemEq.
      (* Both [picks1] and [picks2] has a pick. *)
      apply tok1 in look1 as (n1 & c1 & t1 & r & rs & R1 & Rlist1 & R1holds & picksLook1 & prf1 & a1).
      apply tok2 in look2 as (n2 & c2 & t2 & ? & ? & R2 & Rlist2 & R2holds & picksLook2 & prf2 & a2).
      intros [= opEq].
      eexists n1, c1, t1, r, rs, R1.
      split; first done.
      split; first done.
      split. { erewrite lookup_union_Some_l; done. }
      split; first done.
      rewrite -opEq.
      rewrite -elemEq.
      rewrite a1.
      rewrite map_unfold_op.
      f_equiv.
      rewrite -cmra_transport_op.
      f_equiv.
      rewrite -4!pair_op.
      rewrite GTS_tok_gen_shot_idemp.
      rewrite -Some_op.
      rewrite agree_idemp.
      rewrite gen_pv_op.
      rewrite /gV.
      simpl.
      rewrite -auth_auth_dfrac_op.
      done.
    - intros [= ->].
      apply tok1 in look1 as (n & c & t & r & rs & R & Rlist & Rholds & picksLook & rest).
      eexists n, c, t, r, rs, R.
      split; first done.
      split; first done.
      split. { erewrite lookup_union_Some_l; done. }
      apply rest.
    - intros [= ->].
      apply tok2 in look2 as (n & c & t & r & rs & R & Rlist & Rholds & picksLook & rest).
      eexists n, c, t, r, rs, R.
      split; first done.
      split; first done.
      split.
      { erewrite lookup_union_r; try done.
        apply not_elem_of_dom.
        rewrite domEq1.
        rewrite not_elem_of_dom.
        done. }
      apply rest.
    - intros [=].
  Qed.

  Lemma own_picks_sep picks1 picks2 :
    own_picks picks1 -∗
    own_picks picks2 -∗
    own_picks (merge_picks picks1 picks2).
  Proof.
    iDestruct 1 as (m1) "[O1 %R1]".
    iDestruct 1 as (m2) "[O2 %R2]".
    iExists (m1 ⋅ m2).
    iDestruct (tokens_for_picks_agree_overlap' with "O1 O2") as %HI.
    { done. } { done. }
    iCombine "O1 O2" as "$".
    iPureIntro.
    apply m_contains_tokens_for_picks_merge; try done.
  Qed.

End own_picks_properties.

Section own_promises_properties.
  Context `{Ω : gGenCmras Σ}.

  Implicit Types (prs : list (promise_info Ω)).

  (* If two promise lists has an overlap then one of the overlapping promises
   * is strictly stronger than the other. *)
  Lemma own_promises_overlap prs1 prs2 :
    own_promises prs1 -∗
    own_promises prs2 -∗
    ⌜ promises_overlap_pred prs1 prs2 ⌝.
  Proof.
    iIntros "O1 O2".
    iIntros (id γ p1 p2 look1 look2).
    apply promises_lookup_at_Some in look1 as elem1.
    apply promises_lookup_at_Some in look2 as elem2.
    iSpecialize ("O1" $! _ elem1).
    iSpecialize ("O2" $! _ elem2).
    simpl.
    iDestruct "O1" as (eq ???) "O1".
    iDestruct "O2" as (eq' ???) "O2".
    assert (eq' = eq) as -> by congruence.
    iCombine "O1 O2" as "O3".
    rewrite discrete_fun_singleton_op.
    rewrite singleton_op.
    iDestruct (ownM_valid with "O3") as "#Hv".
    iClear "O3".
    rewrite discrete_fun_validI.
    setoid_rewrite gmap_validI.
    iSpecialize ("Hv" $! id γ).
    simpl.
    rewrite discrete_fun_lookup_singleton.
    rewrite lookup_singleton.
    rewrite option_validI.
    rewrite map_unfold_op.
    rewrite map_unfold_validI.
    rewrite -cmra_transport_op.
    rewrite cmra_transport_validI.
    rewrite -pair_op.
    rewrite prod_validI /=.
    iDestruct "Hv" as "[_ %Hv]". iPureIntro.
    rewrite gen_pv_op gen_pv_valid in Hv.
    rewrite auth_frag_op_valid in Hv.
    apply to_max_prefix_list_op_valid_L in Hv as [Hv|Hv].
    - right.
      eapply pred_prefix_list_for_prefix_of; done.
    - left.
      eapply pred_prefix_list_for_prefix_of; done.
  Qed.

  (* Lemma own_promises_sep prs1 prs2 : *)
  (*   own_promises prs1 -∗ *)
  (*   own_promises prs2 -∗ *)
  (*   own_promises (merge_promises prs1 prs2). *)
  (* Proof. *)
  (* Admitted. *)

End own_promises_properties.

(* In this section we prove structural rules of the nextgen modality. *)

Section nextgen_properties.
  Context {Σ : gFunctors} {Ω : gGenCmras Σ}.

  Lemma res_for_picks_empty :
    res_for_picks (λ i : gid Σ, ∅) ε.
  Proof. done. Qed.

  Lemma own_picks_empty :
    ⊢@{iProp Σ} own_picks (λ i : gid Σ, ∅).
  Proof. iExists ε. rewrite ownM_unit' left_id. iPureIntro. done. Qed.

  Lemma own_promises_empty :
    ⊢@{iProp Σ} own_promises [].
  Proof.
    rewrite /own_promises.
    iIntros (? elm).
    inversion elm.
  Qed.

  Lemma nextgen_emp_2 : emp ⊢@{iProp Σ} ⚡==> emp.
  Proof.
    iIntros "E".
    rewrite /nextgen.
    iExists (λ i, ∅), [].
    iSplitL "". { iApply own_picks_empty. }
    iSplitL "". { iApply own_promises_empty. }
    iSplit; first done.
    iIntros (full_picks ?) "? ?".
    iModIntro.
    iFrame "E".
  Qed.

  Lemma nextgen_sep_2 P Q :
    (⚡==> P) ∗ (⚡==> Q) ⊢@{iProp Σ} ⚡==> (P ∗ Q) .
  Proof.
    rewrite /nextgen.
    iIntros "[P Q]".
    iDestruct "P" as (??) "(picks1 & pr1 & %wf1 & A)".
    iDestruct "Q" as (??) "(picks2 & pr2 & %wf2 & B)".
    (* Combine the picks. *)
    iExists _, _.
    iDestruct (own_picks_sep with "picks1 picks2") as "$".
    (* Combine the promises. *)
  Admitted.

End nextgen_properties.

(* Ownership over generational ghost state. *)

Section generational_resources.
  Context {n} {A} {DS : ivec n cmra} `{!genInG Σ Ω A DS}.
  Implicit Types (R : pred_over DS A) (P : (A → A) → Prop).

  Definition gen_own_res (a : A) : generational_cmraR A DS :=
    (None, (None, None), Some a, None, ε).

  Definition gen_own (γ : gname) (a : A) : iProp Σ :=
    own γ (gen_own_res a).

  Definition gen_token_used γ : iProp Σ :=
    own γ ((None, GTS_tok_perm, None, None, ε)).

  Definition gen_picked_out γ t : iProp Σ :=
    own γ ((None, GTS_tok_gen_shot t, None, None, ε)).

  Definition gen_picked_in γ (t : A → A) : iProp Σ :=
    own γ (
      (Some (to_agree t), (None, None), None, None, ε) : generational_cmraR A DS).

  Definition gen_token γ : iProp Σ :=
    own γ ((None, GTS_tok_both, None, None, ε)).

  Definition know_deps γ (γs : ivec n gname) : iProp Σ :=
    own γ (
      (ε, ε, ε, Some (to_agree (ivec_to_list γs)), ε) : generational_cmraR A DS
    ).

  Definition token_res all : generational_cmraR A DS :=
    (None, GTS_tok_both, None, None, gPV (● (to_max_prefix_list all))).

  (** Ownership over the token and the promises for [γ]. *)
  Definition token (γ : gname) (γs : ivec n gname) R P : iProp Σ :=
    ∃ (all : list (pred_over DS A)),
      "%pred_prefix" ∷ ⌜ pred_prefix_list_for' all R P ⌝ ∗
      "auth_preds" ∷ own γ (token_res all).

  Definition used_token (γ : gname) (γs : ivec n gname) R P : iProp Σ :=
    ∃ (all : list (pred_over DS A)),
      ⌜ pred_prefix_list_for' all R P ⌝ ∗
      know_deps γ γs ∗
      own γ ((
        None,
        GTS_tok_both,
        None,
        None,
        gP (● to_max_prefix_list all) ⋅ gV (●□ to_max_prefix_list all)
      ) : generational_cmraR A DS).

  (* TODO: We need some way of converting between the relations stored in
   * [promise_info] and the relations stored by the user.
   *
   * [promise_info] stores everything in relation to Σ. User predicates mention
   * cameras directly and then have evidence (equalities) that the camera is in
   * Σ. To convert a predicate by the user into one in [promise_info] we need
   * to use all of this evidence. That is, we need to translate along all of
   * the equalities. This is a bit like in [own] where users write an element
   * of their camera and then this element is transported along the equality
   * into an element of [Σ i]. *)

  (* (** Knowledge that γ is accociated with the predicates R and P. *) *)
  (* Definition rely (γ : gname) (γs : ivec n gname) R P : iProp Σ := *)
  (*   ∃ (p : promise_info Σ) (all : list (pred_over DS A)), *)
  (*     ⌜ p.(pi_γ) = γ ⌝ ∗ *)
  (*     ⌜ p.(pi_rel) = R ⌝ ∗ *)
  (*     ⌜ p.(pi_pred) = P ⌝ ∗ *)
  (*     ⌜ deps_to_gnames (p.(pi_deps)) γs ⌝ *)
  (*     ⌜ pred_prefix_list_for' all R P ⌝ ∗ *)
  (*     own γ ((None, (None, None), None, *)
  (*             gPV (◯ to_max_prefix_list all)) : generational_cmraR A DS). *)

  (** Knowledge that γ is accociated with the predicates R and P. *)
  Definition rely (γ : gname) (γs : ivec n gname) R P : iProp Σ :=
    ∃ (all : list (pred_over DS A)),
      "%rely_pred_prefix" ∷ ⌜ pred_prefix_list_for' all R P ⌝ ∗
      "#deps" ∷ know_deps γ γs ∗
      "frag_preds" ∷ own γ (
        (ε, ε, ε, ε, gPV (◯ to_max_prefix_list all)) : generational_cmraR A DS
      ).

End generational_resources.

Definition rely_self `{i : !genInSelfG Σ Ω A}
    γ (P : (A → A) → Prop) : iProp Σ :=
  ∃ γs R, rely (DS := genInSelfG_DS) γ γs R P.

Section rules.
  Context {n : nat} {DS : ivec n cmra} `{!genInG Σ Ω A DS}.

  Lemma own_gen_alloc (a : A) γs :
    ✓ a → ⊢ |==> ∃ γ, gen_own γ a ∗ token γ γs True_pred (λ _, True%type).
  Proof.
    iIntros (Hv).
    rewrite /gen_own.
    rewrite /token.
    iMod (own_alloc (gen_own_res a ⋅ token_res (True_pred :: []))) as (γ) "[A B]".
    { split; simpl; try done.
      rewrite ucmra_unit_left_id.
      apply gen_pv_valid.
      apply auth_auth_valid.
      apply to_max_prefix_list_valid. }
    iExists γ.
    iModIntro. iFrame "A".
    iExists _. iFrame "B".
    iPureIntro.
    apply pred_prefix_list_for'_True.
  Qed.

  Lemma gen_token_split γ :
    gen_token γ ⊣⊢
    own γ (None, GTS_tok_perm, None, None, ε) ∗
    own γ (None, GTS_tok_gen, None, None, ε).
  Proof. rewrite -own_op. done. Qed.

  Lemma gen_picked_in_agree γ (f f' : A → A) :
    gen_picked_in γ f -∗ gen_picked_in γ f' -∗ ⌜ f = f' ⌝.
  Proof.
    iIntros "A B".
    iDestruct (own_valid_2 with "A B") as "val".
    iDestruct (prod_valid_1st with "val") as %val.
    iPureIntro.
    rewrite Some_valid in val.
    apply (to_agree_op_inv_L (A := leibnizO (A → A))) in val.
    done.
  Qed.

  (** Strengthen a promise. *)
  Lemma token_strengthen_promise `{∀ (i : fin n), genInSelfG Σ Ω (DS !!! i)}
      γ γs (deps_preds : preds_for n DS)
      (R_1 R_2 : pred_over DS A) (P_1 P_2 : (A → A) → Prop) :
    (* The new relation is stronger. *)
    (∀ (ts : trans_for n DS) (t : A → A),
       huncurry R_1 ts t → huncurry R_2 ts t ∧ P_2 t) →
    (* The new predicate is stronger. *)
    (∀ t, P_1 t → P_2 t) →
    (* The new relation implies the predicate. *)
    (∀ ts t, huncurry R_2 ts t → P_2 t) →
    (* Evidence that the promise is realizeable. *)
    (∀ (ts : trans_for n DS),
      preds_hold deps_preds ts → ∃ (e : A → A), (huncurry R_2) ts e) →
    (* For every dependency we own a [rely_self]. *)
    (∀ (i : fin n), rely_self (γs !!! i) (hvec_lookup_fmap deps_preds i)) -∗
    token γ γs R_1 P_1 -∗ (* Old token. *)
    token γ γs R_2 P_2. (* Updated token. *)
  Proof.
  Admitted.

  Lemma token_pick γ γs (R : pred_over DS A) P (ts : trans_for n DS) t
      `{∀ (i : fin n), genInSelfG Σ Ω (DS !!! i)} :
    huncurry R ts t →
    (∀ i, gen_picked_out (γs !!! i) (hvec_lookup_fmap ts i)) -∗
    token γ γs R P -∗ |==>
    used_token γ γs R P ∗ gen_picked_out γ t.
  Proof.
  Admitted.

  Lemma token_nextgen γ γs (R : pred_over DS A) P :
    used_token γ γs R P ⊢ ⚡==> token γ γs R P.
  Proof.
    iDestruct 1 as (? (HPL & ?)) "own".
    destruct HPL as (? & ?).

    iExists (λ i, ∅), [].
    iSplitL "". { iApply own_picks_empty. }
    iSplitL "". { iApply own_promises_empty. }
    iSplit; first done.
    iIntros (full_picks ?).
    iEval (rewrite own.own_eq) in "own".
    rewrite /own.own_def.
    (* iModIntro. *)
  Admitted.
  (*   iDestruct (uPred_own_resp_omega _ _ with "own") as (to) "(%cond & own)". *)
  (*   { done. } *)
  (*   simpl in cond. *)
  (*   destruct cond as (t & -> & cond). *)
  (*   iExists t. *)
  (*   iSplit; first done. *)
  (*   simpl. *)
  (*   rewrite /gen_picked_in. *)
  (*   rewrite -own_op. *)
  (*   rewrite own.own_eq. *)
  (*   iFrame "own". *)
  (* Qed. *)

  (* TODO: Prove this lemma. *)
  Lemma rely_nextgen γ γs (R : pred_over DS A) P `{∀ (i : fin n), genInSelfG Σ Ω (DS !!! i)} :
    rely γ γs R P
    ⊢ ⚡==> (
      rely γ γs R P ∗
      ∃ (t : A → A) (ts : trans_for n DS),
        ⌜ huncurry R ts t ∧ (* The transformations satisfy the promise *)
          P t ⌝ ∗ (* For convenience we also get this directly *)
        gen_picked_in γ t ∗
        (* The transformations for the dependencies are the "right" ones *)
        (∀ i, gen_picked_in (γs !!! i) (hvec_lookup_fmap ts i))).
  Proof.
    rewrite /rely.
    iNamed 1.
  Admitted.

  Lemma token_to_rely γ γs (R : pred_over DS A) P :
    token γ γs R P ⊢ rely γ γs R P.
  Proof. Admitted.

  Lemma token_rely_combine_pred γ γs R1 P1 R2 P2 :
    token γ γs R1 P1 -∗ rely γ γs R2 P2 -∗ ⌜ rel_stronger R1 R2 ⌝.
  Proof.
    iNamed 1.
    iNamed 1.
    (* iDestruct 1 as (prs1 prefix1) "own1". *)
    (* iDestruct 1 as (prs2 prefix2) "own2". *)
    iDestruct (own_valid_2 with "auth_preds frag_preds") as "val".
    iDestruct (prod_valid_5th with "val") as "%val".
    iPureIntro.
    move: val.
    rewrite gen_pv_op. rewrite gen_pv_valid.
    rewrite auth_both_valid_discrete.
    rewrite to_max_prefix_list_included_L.
    intros [prefix _].
    destruct pred_prefix as [? ?].
    destruct rely_pred_prefix as [? ?].
    eapply pred_prefix_list_for_prefix_of; done.
  Qed.

  Lemma know_deps_agree γ γs1 γs2 :
    know_deps γ γs1 -∗
    know_deps γ γs2 -∗
    ⌜ γs1 = γs2 ⌝.
  Proof.
    iIntros "A B".
    iDestruct (own_valid_2 with "A B") as "hv".
    iDestruct (prod_valid_4th with "hv") as "%val".
    iPureIntro.
    rewrite Some_valid in val.
    rewrite to_agree_op_valid_L in val.
    apply ivec_to_list_inj.
    apply val.
  Qed.

  Lemma rely_combine γ γs1 γs2 R1 P1 R2 P2 :
    rely γ γs1 R1 P1 -∗
    rely γ γs2 R2 P2 -∗
    ⌜ γs1 = γs2 ⌝ ∗
    ⌜ rel_stronger R1 R2 ∨ rel_stronger R2 R1 ⌝.
  Proof.
    iNamed 1.
    iDestruct 1 as (prs2 prefix2) "[deps2 preds2]".
    iDestruct (know_deps_agree with "deps deps2") as %<-.
    iDestruct (own_valid_2 with "frag_preds preds2") as "val".
    iDestruct (prod_valid_5th with "val") as "%val".
    iPureIntro.
    split; first done.
    move: val.
    rewrite gen_pv_op. rewrite gen_pv_valid.
    rewrite auth_frag_valid.
    rewrite to_max_prefix_list_op_valid_L.
    destruct rely_pred_prefix as [(isLast1 & look1) ?].
    destruct prefix2 as [(isLast2 & look2) ?].
    rewrite last_lookup in isLast1.
    rewrite last_lookup in isLast2.
    intros [prefix | prefix].
    - right.
      eapply look2; last done.
      { apply le_pred. apply prefix_length. eassumption. }
      eapply prefix_lookup; done.
    - left.
      eapply look1; last done.
      { apply le_pred. apply prefix_length. eassumption. }
      eapply prefix_lookup; done.
  Qed.

End rules.

Equations forall_fin_2 (P : fin 2 → Type) : P 0%fin * P 1%fin → ∀ (i : fin 2), P i :=
| P, p, 0%fin => fst p
| P, p, 1%fin => snd p.

(* This is a hacky way to find all the [genInSelfG] instances when there are
exactly two dependencies. It would be nicer with a solution that could iterate
over all the dependencies during type class resolution (maybe inspired by
[TCForall] for lists). *)
Global Instance genInG_forall_2 {Σ n m} {DS1 : ivec n cmra} {DS2 : ivec m cmra}
  `{!genInG Σ Ω A DS1} `{!genInG Σ Ω B DS2} :
  ∀ (i : fin 2), genInSelfG Σ Ω ([A; B]%IL !!! i).
Proof.
  apply forall_fin_2.
  split.
  - apply (GenInG2 _ _ _ n DS1 _).
  - apply (GenInG2 _ _ _ m DS2 _).
Qed.

Section test.
  Context `{max_i : !inG Σ max_natR}.
  Context `{i : !genInG Σ Ω max_natR [max_natR; max_natR] }.

  Definition a_rely :=
    rely (1%positive) [2%positive; 3%positive] (λ Ta Tb Ts, Ta = Ts ∧ Tb = Ts) (λ _, True).

  Section test.
    Variables (A : cmra) (B : cmra) (T1 : A → A) (T2 : B → B)
      (P1 : (A → A) → Prop) (P2 : (B → B) → Prop).

    Definition TS : trans_for _ [A; B] := [T1; T2]%HV.
    Definition PS : preds_for _ [A; B] := [P1; P2].
    Compute (preds_hold (DS := [A; B]) PS TS).

    Context `{!genInG Σ Ω B [] }.
    Context `{!genInG Σ Ω A [A; B] }.

    Lemma foo2 (γ : gname) (γs : ivec 2 gname) : True.
    Proof.
      pose proof (token_strengthen_promise γ γs PS) as st.
      rewrite /pred_over in st.
      rewrite /cmra_to_trans in st.
      simpl in st.
    Abort.

  End test.

  Definition a_rel (Ta : max_natR → max_natR) Tb Ts :=
    Ta = Ts ∧ Tb = Ts.

End test.
