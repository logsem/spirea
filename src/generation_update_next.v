From Equations Require Import Equations.

From iris.algebra Require Import functions gmap agree excl csum max_prefix_list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

From iris_named_props Require Import named_props.

From self Require Import hvec extra basic_nextgen_modality gen_trans
  gen_single_shot gen_pv.

Import uPred.

Section types.

  (** A transformation over the carrier of the camera [A]. *)
  Definition cmra_to_trans A := cmra_car A → cmra_car A.

  (** A predicate over a transformation over [A]. *)
  Definition cmra_to_pred A := (cmra_to_trans A) → Prop.

  Definition pred_over_ty {n} (DS : ivec n Type) (A : Type) :=
    iimpl id DS ((A → A) → Prop).

  Definition pred_over {n} (DS : ivec n cmra) A :=
    iimpl id (ivec_map cmra_to_trans DS) ((A → A) → Prop).

  Definition True_pred {n} {DS : ivec n cmra} {A} : pred_over DS A :=
    hcurry (λ _ _, True).

  (* This results in the type:
     [(max_nat → max_nat) → (excl () → excl ()) → (nat → nat) → Prop] *)
  Compute (pred_over [max_natR; exclR unitO] natR).

End types.

Definition trans_for n (DS : ivec n cmra) := hvec id n (cmra_to_trans <$> DS).

Notation preds_for := (hvec cmra_to_pred).

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
  Canonical Structure pred_overO (A : Type) (DS : ivec n cmra) :=
    leibnizO (pred_over DS A).

  Definition promises (A : Type) (DS : ivec n Type) :=
    max_prefix_list (pred_over_ty DS A).
  Definition promisesR (A : cmra) (DS : ivec n cmra) :=
    max_prefix_listR (pred_overO A DS).

  Definition promisesUR (A : cmra) (DS : ivec n cmra) :=
    max_prefix_listUR (pred_over DS A).

  (* Authorative promises. *)
  Definition auth_promises {A : Type} {DS : ivec n cmra}
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
Definition gen_generation {n} {A : cmra} (DS : ivec n cmra)
    (f : A → A) : generational_cmraR A DS → generational_cmraR A DS :=
  (const (Some (to_agree f)) : optionR (agreeR (leibnizO (A → A))) → optionR (agreeR (leibnizO (A → A)))) *M*
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
  GenTrans f → GenTrans (gen_generation DS f).
Proof. apply _. Qed.

Global Instance gen_generation_proper {n} {A : cmra} (DS : ivec n cmra) (f : A → A) :
  Proper ((≡) ==> (≡)) f →
  Proper ((≡) ==> (≡)) (gen_generation DS f).
Proof.
  intros ? [[??]?] [[??]?] [[??]?]. simpl in *.
  rewrite /gen_generation.
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

(** For every entry in [Ω] we store this record of information. The equality
 * [gti_look] is the "canonical" equality we will use to show that the resource
 * [R Σ i] has the proper form. Using this equality is necesarry as we
 * otherwise end up with different equalities of this form that we then do not
 * know to be equal. *)
Record gen_cmra_data (Σ : gFunctors) (i : gid Σ) := {
  gcd_cmra : cmra;
  gcd_n : nat;
  gcd_deps : ivec gcd_n cmra;
  gti_look : generational_cmraR gcd_cmra gcd_deps = R Σ i;
  (* gti_valid : valid_gen_trans (R Σ i); *)
}.

Arguments gcd_cmra {_} {_}.
Arguments gcd_n {_} {_}.
Arguments gcd_deps {_} {_}.
Arguments gti_look {_} {_}.
(* Arguments gti_valid {_} {_}. *)

(** A copy of [option] to work arround universe inconsistencies that arrise if
we use [option]. *)
Inductive option2 (A : Type) : Type :=
  | Some2 : A -> option2 A
  | None2 : option2 A.

Arguments Some2 {A} a.
Arguments None2 {A}.

(** [gTransforms] contains a partial map from the type of cameras into a "set"
of valid transformation function for that camera. *)
Class gTransforms {Σ : gFunctors} := {
  g_gen_infos :> ∀ (i : gid Σ), option2 (gen_cmra_data Σ i)
}.

Global Arguments g_gen_infos {_} _.

#[export] Hint Mode gTransforms +.

Class genInG {n} (Σ : gFunctors) Ω (A : cmra) (DS : ivec n cmra) := GenInG {
  genInG_inG : inG Σ (generational_cmraR A DS);
  genInG_inG_deps : ∀ i d, DS !!! i = d → inG Σ (generational_cmraR A DS);
  (* genInG_id : gid Σ; *)
  (* genInG_apply := rFunctor_apply (gFunctors_lookup Σ genInG_id); *)
  genInG_gti : gen_cmra_data Σ (inG_id genInG_inG);
  genInG_gen_trans : Ω.(g_gen_infos) (inG_id genInG_inG) = Some2 genInG_gti;
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
  Context `{Σ : gFunctors}.

  (** A [TransMap] contains transformation functions for a subset of ghost
   * names. We use one to represent the transformations that a user has picked.
   * the entries that we have picked generational transformations for. *)
  Definition TransMap : Type := ∀ i, gmap gname (T Σ i).

  Implicit Types (transmap : TransMap).

  #[global]
  Instance transmap_subseteq : SubsetEq TransMap :=
    λ p1 p2, ∀ i, p1 i ⊆ p2 i.

  #[global]
  Instance transmap_subseteq_partialorder : PartialOrder transmap_subseteq.
  Proof.
    split.
  Admitted.

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
      map_imap (λ γ a,
        (* If the map of transmap contains a transformation then we apply the
         * transformation. If no pick exists then we return the elemment
         * unchanged. Hence, we default to the identity transformation. *)
        match transmap i !! γ with
        | Some picked_gt => Some $ map_unfold $ picked_gt $ map_fold a
        | None => Some a
        end
      ) (m i).

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
      rewrite 2!map_lookup_imap.
      specialize (eq i γ).
      destruct eq as [a b eq|]; simpl; last done.
      destruct (transmap i !! γ) eqn:look.
      * apply transmapGT in look as [gt ?]. solve_proper.
      * solve_proper.
    - intros ?? Hval.
      intros i γ.
      rewrite !map_lookup_imap. simpl.
      specialize (Hval i γ).
      destruct (a i !! γ) eqn:eq; rewrite eq /=; last done.
      rewrite eq in Hval.
      destruct (transmap i !! γ) as [pick|] eqn:eq2.
      * apply Some_validN.
        apply: cmra_morphism_validN.
        apply Some_validN.
        specialize (transmapGT i γ pick eq2) as [??].
        apply generation_valid.
        apply: cmra_morphism_validN.
        apply Hval.
      * done.
    - move=> m /=.
      rewrite cmra_pcore_core.
      simpl.
      f_equiv.
      intros i γ.
      rewrite lookup_core.
      rewrite 2!map_lookup_imap.
      rewrite lookup_core.
      destruct (m i !! γ) as [a|] eqn:look; rewrite look; simpl; last done.
      simpl.
      rewrite core_Some_pcore.
      destruct (transmap i !! γ) as [pick|] eqn:pickLook; simpl.
      * rewrite core_Some_pcore.
        rewrite -cmra_morphism_pcore.
        specialize (transmapGT i γ pick pickLook) as ?.
        rewrite -generation_pcore.
        rewrite -(cmra_morphism_pcore map_fold).
        (* rewrite -cmra_morphism_pcore. *)
        destruct (pcore a); try done.
      * rewrite core_Some_pcore.
        destruct (pcore a); done.
    - intros m1 m2.
      intros i γ.
      rewrite 2!discrete_fun_lookup_op.
      rewrite !map_lookup_imap.
      rewrite 2!lookup_op.
      rewrite !map_lookup_imap.
      destruct (transmap i !! γ) as [pick|] eqn:pickLook.
      * specialize (transmapGT i γ pick pickLook) as ?.
        destruct (m1 i !! γ) eqn:eq1; destruct (m2 i !! γ) eqn:eq2;
          rewrite eq1 eq2; simpl; try done.
        rewrite -Some_op.
        rewrite -cmra_morphism_op -generation_op -cmra_morphism_op.
        done.
      * destruct (m1 i !! γ) eqn:eq1; destruct (m2 i !! γ) eqn:eq2;
          rewrite eq1 eq2; simpl; try done.
  Qed.

  (** A map of picks that for the resource at [idx] and the ghost name [γ] picks
  the generational transformation [t]. *)
  Definition transmap_singleton i (γ : gname)
      (t : R Σ i → R Σ i) : TransMap :=
    λ j, match decide (i = j) with
           left Heq =>
             (eq_rect _ (λ i, gmap gname (R Σ i → _)) {[ γ := t ]} _ Heq)
         | right _ => ∅
         end.

  Definition transmap_singleton_lookup idx γ (f : R Σ idx → R Σ idx) :
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

  Definition gen_f_singleton_lookup_Some idx' idx γ γ' f (f' : R Σ idx' → _) :
    (transmap_singleton idx γ f) idx' !! γ' = Some f' →
    ∃ (eq : idx' = idx),
      γ = γ' ∧
      f = match eq in (_ = r) return (R Σ r → R Σ r) with eq_refl => f' end.
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

Arguments TransMap Σ : clear implicits.

Section promises.
  Context `{Σ : gFunctors}.

  (** Information about a promise _except_ for any information concerning its
   * dependencies. This lets us talk about a promise without having to talk
   * about it's depencencies (and their dependencies, and their dependencies,
   * and so on recursively). *)
  Record promise_self_info := MkSelfPromiseInfo {
    psi_id : gid Σ; (* The index of the RA in the global RA. *)
    psi_γ : gname; (* Ghost name for the promise. *)
    psi_pred : T Σ psi_id → Prop;
  }.

  Definition deps_to_trans n (deps : ivec n promise_self_info) :=
    hvec (λ dep, T Σ dep.(psi_id)) n deps.

  Definition deps_to_gnames {n} (deps : ivec n promise_self_info) :=
    ivec_map (λ dep, dep.(psi_γ)) deps.

  (** The transformations [ts] satisfies the predicates [ps]. *)
  Equations deps_preds_hold {n}
      (deps : ivec n promise_self_info)
      (ts : deps_to_trans n deps) : Prop :=
    | inil, hnil := True
    | icons d deps', hcons t ts' := d.(psi_pred) t ∧ deps_preds_hold deps' ts'.
  (* Global Transparent deps_preds_hold. *)

  Lemma deps_preds_hold_alt {n}
      (deps : ivec n promise_self_info)
      (ts : hvec (λ dep, T Σ dep.(psi_id)) n deps) :
    deps_preds_hold deps ts ↔ ∀ i, (deps !!! i).(psi_pred) (ts 👀 i).
  Proof.
    split.
    - intros holds i.
      induction i as [hi|ho] eqn:eq.
      * dependent elimination ts.
        destruct holds as [pred ?].
        apply pred.
      * dependent elimination deps.
        dependent elimination ts.
        rewrite deps_preds_hold_equation_2 in holds.
        destruct holds as [? holds].
        apply (IHt _ _ holds t).
        done.
    - intros i.
      induction deps.
      * dependent elimination ts. done.
      * dependent elimination ts.
        rewrite deps_preds_hold_equation_2.
        split. { apply (i 0%fin). }
        apply IHdeps.
        intros i'.
        apply (i (FS i')).
  Qed.

  (** A record of all the information that is a associated with a promise. Note
   * that we use [promise_self_info] for the dependencies, this cuts off what
   * would otherwise be an inductive record--simplifying things at the cost of
   * some power. *)
  Record promise_info := MkPromiseInfo {
    (* "Static" info that is the same for all promises about the same id+γ *)
    pi_id : gid Σ; (* The index of the RA in the global RA. *)
    pi_γ : gname; (* Ghost name for the promise. *)
    pi_n : nat; (* The number of dependencies. *)
    pi_deps : ivec pi_n promise_self_info;
    (* Dynamic information that changes per promise *)
    (* The predicate that relates our transformation to those of the dependencies. *)
    pi_rel : deps_to_trans pi_n pi_deps → T Σ pi_id → Prop;
    (* A predicate that holds for the promise's own transformation whenever
     * [pi_rel] holds. A "canonical" choice could be: [λ t, ∃ ts, pi_rel ts t]. *)
    pi_pred : T Σ pi_id → Prop;
    pi_rel_to_pred : ∀ ts t, pi_rel ts t → pi_pred t;
    pi_witness : ∀ ts, deps_preds_hold pi_deps ts → ∃ t, pi_rel ts t;
  }.

  Implicit Types (prs : list promise_info).

  (** Convert a [promise_info] into a [promise_self_info] by discarding fields
   * about dependencies. *)
  Definition promise_info_to_self (pi : promise_info) :=
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

  (** The promise [p] satisfies the dependency [p_d]. Note that the predicate
   * in [p_d] may not be the same as the one in [p]. When we combine lists of
   * promises some promises might be replaced by stronger ones. Hence we only
   * require that the predicate in [p] is stronger than the one in [p_d]. *)
  Definition promise_satisfy_dep (p_d : promise_self_info) (p : promise_info) :=
    ∃ (eq : p.(pi_id) = p_d.(psi_id)),
      p_d.(psi_γ) = p.(pi_γ) ∧
      (* The predicate in [p] is stronger than what is stated in [p_d] *)
      pred_stronger (res_pred_transport eq p.(pi_pred)) p_d.(psi_pred).

  (** For every dependency in [p] the list [promises] has a sufficicent
   * promise. *)
  Definition promises_has_deps p (promises : list promise_info) :=
    ∀ idx, ∃ p2, p2 ∈ promises ∧ promise_satisfy_dep (p.(pi_deps) !!! idx) p2.

  (** The promise [p] is well-formed wrt. the list [promises] of promises that
   * preceeded it. *)
  Definition promise_wf p (promises : list (promise_info)) : Prop :=
    (∀ p2, p2 ∈ promises → promises_different p p2) ∧
    promises_has_deps p promises.

  (* This definition has nice computational behavior when applied to a [cons]. *)
  Fixpoint promises_wf (promises : list (promise_info)) : Prop :=
    match promises with
    | nil => True
    | cons p promises' =>
      promise_wf p promises' ∧ promises_wf promises'
    end.

  (* NOTE: Not used, but should be implied by [promises_wf] *)
  Definition promises_unique (promises : list promise_info) : Prop :=
    ∀ i j p1 p2, i ≠ j → promises !! i = Some p1 → promises !! j = Some p2 →
      p1.(pi_id) ≠ p2.(pi_id) ∨ p1.(pi_γ) ≠ p2.(pi_γ).

  Lemma promises_has_deps_cons p prs :
    promises_has_deps p prs →
    promises_has_deps p (p :: prs).
  Proof.
    intros hasDeps idx.
    destruct (hasDeps idx) as (p2 & ? & ?).
    eauto using elem_of_list_further.
  Qed.

  (* A well formed promise is not equal to any of its dependencies. *)
  Lemma promise_wf_neq_deps p (promises : list (promise_info)) :
    promise_wf p promises →
    ∀ (idx : fin (p.(pi_n))),
      (* promises_self_different (promise_info_to_self p) (pi_deps p !!! idx). *)
      pi_id p ≠ psi_id (pi_deps p !!! idx) ∨ pi_γ p ≠ psi_γ (pi_deps p !!! idx).
  Proof.
    intros [uniq hasDeps] idx.
    destruct (hasDeps idx) as (p2 & elem & i & eq & jhhi).
    destruct (uniq _ elem) as [h|h].
    - left. congruence.
    - right. congruence.
  Qed.

  Lemma promises_well_formed_lookup promises idx p :
    promises_wf promises →
    promises !! idx = Some p →
    promises_has_deps p promises. (* We forget the different part for now. *)
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

  Record promise_at id γ := mk_promise_at {
    pa_promise : promise_info;
    pa_id_eq : pa_promise.(pi_id) = id;
    pa_γ_eq : γ = pa_promise.(pi_γ);
  }.
  Arguments pa_promise {_} {_}.
  Arguments pa_id_eq {_} {_}.
  Arguments pa_γ_eq {_} {_}.

  Equations promises_lookup_at (promises : list promise_info) iid γ : option (promise_at iid γ) :=
  | [], iid, γ => None
  | p :: ps', iid, γ with decide (p.(pi_id) = iid), decide (p.(pi_γ) = γ) => {
    | left eq_refl, left eq_refl => Some (mk_promise_at p.(pi_id) p.(pi_γ) p eq_refl eq_refl);
    | left eq_refl, right _ => promises_lookup_at ps' p.(pi_id) γ
    | right _, _ => promises_lookup_at ps' iid γ
  }.

  Fixpoint promises_lookup promises id γ : option promise_info :=
    pa_promise <$> (promises_lookup_at promises id γ).

  Definition promise_at_pred {id γ} (pa : promise_at id γ) : (T Σ id → Prop) :=
    res_pred_transport pa.(pa_id_eq) pa.(pa_promise).(pi_pred).

  Definition promises_lookup_pred (promises : list promise_info)
      id (γ : gname) : option (T Σ id → Prop) :=
      promise_at_pred <$> promises_lookup_at promises id γ.

  Lemma promises_lookup_at_Some promises id γ pa :
    promises_lookup_at promises id γ = Some pa →
    pa.(pa_promise) ∈ promises.
  Proof.
    induction promises as [|? ? IH]; first by inversion 1.
    rewrite promises_lookup_at_equation_2.
    rewrite promises_lookup_at_clause_2_equation_1.
    destruct (decide (pi_id a = id)) as [eq1|neq].
    - destruct (decide (pi_γ a = γ)) as [eq2|neq].
      * destruct eq1.
        destruct eq2.
        simpl.
        intros [= <-].
        apply elem_of_list_here.
      * destruct eq1.
        rewrite promises_lookup_at_clause_2_clause_1_equation_2.
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

  (* FIXME: We need to take the strongest promise when two exist for the same
   * idx and gname. *)
  Fixpoint merge_promises prs1 prs2 :=
    match prs1 with
    | [] => prs2
    | p :: prs1' =>
      if decide (promises_lookup prs2 p.(pi_id) p.(pi_γ) = None)
      then p :: (merge_promises prs1' prs2)
      else merge_promises prs1' prs2
    end.

  Lemma merge_promises_elem p prs1 prs2 :
    p ∈ merge_promises prs1 prs2 →
    p ∈ prs1 ∨ p ∈ prs2.
  Proof.
  Admitted.

  Lemma promises_lookup_different p p2 prs2 :
    p2 ∈ prs2 →
    promises_lookup prs2 (pi_id p) (pi_γ p) = None →
    promises_different p p2.
  Proof.
  Admitted.

  Lemma merge_promises_wf prs1 prs2 :
    promises_wf prs1 →
    promises_wf prs2 →
    promises_wf (merge_promises prs1 prs2).
  Proof.
    intros wf1 wf2.
    induction prs1 as [|p prs1 IH]; first done.
    simpl.
    destruct (decide (promises_lookup prs2 (pi_id p) (pi_γ p) = None)) as [eq|eq].
    - simpl.
      split; last (apply IH; apply wf1).
      split.
      * intros p2.
        intros [in1|in2]%merge_promises_elem.
        + apply wf1. done.
        + eapply promises_lookup_different; done.
      * admit.
    - apply IH. apply wf1.
  Admitted.

  (* When we store picks we also need to store the promises that they are
   * related with. We store these promises in a map. This map should contain
   * promises at the "right" indices which this definition expresses. *)
  (* NOTE: Not used *)
  Definition promise_map_wf (pm : ∀ i, gmap gname promise_info) : Prop :=
    ∀ i γ p, (pm i) !! γ = Some p → p.(pi_id) = i ∧ p.(pi_γ) = γ.

End promises.

Section transmap.
  Context `{Σ : gFunctors}.

  Implicit Types (transmap : TransMap Σ).

  (* We need to:
    - Be able to turn a list of promises and a map of picks into a
      global transformation.
    - Say that a set of picks respects a list of promises.
    - Merge two lists of promises.
   *)

  Definition trans_at_deps transmap (p : promise_info)
      (trans : deps_to_trans p.(pi_n) p.(pi_deps)) :=
    ∀ idx,
      let dep := p.(pi_deps) !!! idx
      in transmap dep.(psi_id) !! dep.(psi_γ) = Some (trans 👀 idx).

  (** The transformations in [transmap] satisfy the relation in [p]. *)
  Definition transmap_satisfy_rel transmap p :=
    ∃ trans t,
      transmap p.(pi_id) !! p.(pi_γ) = Some t ∧
      trans_at_deps transmap p trans ∧
      p.(pi_rel) trans t.

  (** The [transmap] respect the promises in [ps]: There is a pick for every
   * promise and all the relations in the promises are satisfied by the
   * transformations in transmap. *)
  Definition transmap_resp_promises transmap (ps : list (promise_info)) :=
    Forall (transmap_satisfy_rel transmap) ps.

  Lemma promises_had_deps_resp_promises p idx p_d promises transmap :
    p.(pi_deps) !!! idx = p_d →
    promises_has_deps p promises →
    transmap_resp_promises transmap promises →
    ∃ t, psi_pred p_d t ∧ transmap (psi_id p_d) !! psi_γ p_d = Some t.
  Proof.
    intros look hasDeps resp.
    rewrite /transmap_resp_promises Forall_forall in resp.
    rewrite -look.
    specialize (hasDeps idx) as (p2 & Helem & eq1 & -> & strong).
    destruct (resp _ Helem) as (ts & (t & tmLook & ? & relHolds)).
    specialize (p2.(pi_rel_to_pred) ts t relHolds) as predHolds.
    exists (res_trans_transport eq1 t).
    simpl.
    split.
    * apply strong. clear -predHolds. destruct eq1. simpl. done.
    * clear -tmLook. destruct eq1. done.
  Qed.

  (** If a [transmap] respects a list [promises] and growing the list with [p]
   * is well formed, then we can conjur up a list of transitions from
   * [transmap] that match the dependencies in [p] and that satisfy their
   * predicates. *)
  Lemma transmap_satisfy_wf_cons p promises transmap :
    promises_wf (p :: promises) →
    transmap_resp_promises transmap promises →
    ∃ ts,
      trans_at_deps transmap p ts ∧
      deps_preds_hold p.(pi_deps) ts.
  Proof.
    intros WF resp.
    destruct WF as [[uniq hasDeps] WF'].
    set (F := (λ dep, T Σ dep.(psi_id))).
    edestruct (fun_ex_to_ex_hvec (F := F) p.(pi_deps)
      (λ i t,
        let pd := p.(pi_deps) !!! i in
        pd.(psi_pred) t ∧
        transmap (psi_id pd) !! psi_γ pd = Some t))
      as (ts & ?).
    { intros idx.
      eapply promises_had_deps_resp_promises; done. }
    exists ts.
    rewrite deps_preds_hold_alt.
    split.
    - intros di. apply H.
    - intros di. apply H.
  Qed.

  Equations transmap_insert_go transmap (id : gid Σ) (γ : gname) (pick : T Σ id)
    (id' : gid Σ) : gmap gname (T Σ id') :=
  | transmap, _, γ, pick, id', with decide (id = id') => {
    | left eq_refl => <[ γ := pick ]>(transmap id')
    | right _ => transmap id'
  }.

  Definition transmap_insert transmap id γ pick : TransMap Σ :=
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
    destruct (impl _ elem) as (t' & ts & hi).
    exists t', ts.
    rewrite /trans_at_deps.
    (* NOTE: This proof might be a bit of a mess. *)
    setoid_rewrite transmap_insert_lookup_ne.
    + apply hi.
    + apply (uniq _ elem).
    + apply elem_of_list_lookup_1 in elem as (ii & look).
      specialize (
        promises_well_formed_lookup promises _ p2 WF look) as hasDeps2.
      specialize (hasDeps2 idx) as (p3 & look3 & eq & eq2 & ?).
      rewrite eq2.
      destruct p3.
      simpl in *.
      specialize (uniq _ look3) as [? | ?].
      - rewrite -eq. left. done.
      - right. done.
  Qed.

  Definition transmap_overlap_resp_promises transmap (ps : list (promise_info)) :=
    ∀ i p, ps !! i = Some p →
      transmap_satisfy_rel transmap p ∨ (transmap p.(pi_id) !! p.(pi_γ) = None).

  Lemma trans_at_deps_subseteq transmap1 transmap2 p ts :
    transmap1 ⊆ transmap2 →
    trans_at_deps transmap1 p ts →
    trans_at_deps transmap2 p ts.
  Proof.
    intros sub ta.
    intros idx. simpl.
    specialize (sub (psi_id (pi_deps p !!! idx))).
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
  Lemma transmap_promises_to_maps transmap (promises : list promise_info) :
    transmap_overlap_resp_promises transmap promises →
    promises_wf promises →
    ∃ (map : TransMap Σ),
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
            rewrite transmap_insert_lookup_ne; first apply transIn.
            apply depsDiff.
          -- apply transmap_resp_promises_insert; done.
        * apply transmap_insert_subseteq_r; done.
  Qed.

  Lemma promises_to_maps (promises : list promise_info) :
    promises_wf promises →
    ∃ (transmap : TransMap Σ), transmap_resp_promises transmap promises.
  Proof.
    intros WF.
    edestruct (transmap_promises_to_maps (λ i : gid Σ, ∅)) as [m [resp a]].
    2: { done. }
    - intros ???. right. done.
    - exists m. apply resp.
  Qed.

End transmap.

Arguments promise_info Σ : clear implicits.
Arguments promise_self_info Σ : clear implicits.

Section next_gen_definition.
  Context `{Σ : gFunctors}.

  Implicit Types (picks : TransMap Σ).

  (* Every generational ghost location consists of a camera and a list of
   * cameras for the dependencies. *)

  (* If a transformation has been picked for one ghost name, then all the
   * dependencies must also have been picked. *)

  (* The resource [m] contains the agreement resources for all the picks in
   * [picks]. We need to know that a picked transformation satisfies the most
   * recent/strongest promise. We thus need the authorative part of the
   * promises. *)
  Definition res_for_picks Ω picks (m : iResUR Σ) :=
    ∀ i,
      dom (picks i) ≡ dom (m i) ∧
      ∀ γ (a : Rpre Σ i),
        m i !! γ = Some a  →
        ∃ gti ts γs (t : gti.(gcd_cmra) → gti.(gcd_cmra)) R Rs,
          Ω.(g_gen_infos) i = Some2 gti ∧
          (* BUG: [ts] is unrestricted. The transformations in [ts] should be
           * the result of looking up in [picks]. *)
          huncurry R ts t ∧
          picks i !! γ = Some (cmra_map_transport gti.(gti_look) (gen_generation (gti.(gcd_deps)) t)) ∧
          pred_prefix_list_for Rs R ∧
          a ≡ map_unfold (cmra_transport gti.(gti_look)
            (ε, GTS_tok_gen_shot t, ε,
             Some (to_agree γs), gV (●□ (to_max_prefix_list Rs)))).

  Definition own_picks Ω picks : iProp Σ :=
    ∃ m, uPred_ownM m ∗ ⌜ res_for_picks Ω picks m ⌝.

  (* NOTE: We need to translate the type of relation stored in [promise_info]
   * with the type of relation used by gti. We need to ensure that the *)

  Definition res_for_promises Ω (ps : list (promise_info Σ)) (m : iResUR Σ) :=
    ∀ p, p ∈ ps →
      ∃ gti (a : Rpre Σ p.(pi_id)) Rel Rs,
        Ω.(g_gen_infos) p.(pi_id) = Some2 gti ∧
        m p.(pi_id) !! p.(pi_γ) = Some a ∧
        (* BUG: [Rel] is not used for anything. *)
        pred_prefix_list_for Rs Rel ∧
        (* Rel = p.(pi_rel) ∧ *)
        a ≡ map_unfold (cmra_transport gti.(gti_look)
          (ε, ε, ε, ε, gV (◯ (to_max_prefix_list Rs)))).
  (* Print res_for_promises. *)

  Definition own_promises Ω (ps : list (promise_info Σ)) : iProp Σ :=
    ∃ m, uPred_ownM m ∗ ⌜ res_for_promises Ω ps m ⌝.

  (* The global transformation [fG] respects the entries in [picks].
   * NOTE: We may not need this given how [⚡==>] now quantifies over picks and
   * not global transformations. *)
  Definition gt_resp_picks (fG : iResUR Σ → iResUR Σ) picks :=
    ∀ (m : iResUR Σ) i γ a t,
      m i !! γ = Some a → (* For every element in the old element. *)
      picks i !! γ = Some t →
      (fG m) i !! γ = Some (map_unfold (t (map_fold a))).

  Definition nextgen {Ω} P : iProp Σ :=
    ∃ picks (ps : list (promise_info Σ)),
      (* We own resources for everything in [picks] and [promises]. *)
      own_picks Ω picks ∗ own_promises Ω ps ∗
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
  Context {Σ : gFunctors}.
  Implicit Types (picks : TransMap Σ).

  Definition merge_picks picks1 picks2 := λ i, (picks1 i) ∪ (picks2 i).

  Definition map_agree_overlap `{FinMap K M} {A} (m1 m2 : M A) :=
    ∀ (k : K) (i j : A), m1 !! k = Some i → m2 !! k = Some j → i = j.

  Lemma cmra_transport_validI {A B : cmra} (eq : A =@{cmra} B) (a : A) :
    ✓ cmra_transport eq a ⊣⊢@{iPropI Σ} ✓ a.
  Proof. destruct eq. done. Qed.

  Lemma tokens_for_picks_agree_overlap' Ω picks1 picks2 m1 m2 :
    res_for_picks Ω picks1 m1 →
    res_for_picks Ω picks2 m2 →
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
    (* edestruct m2look as (gti2 & t2 & ? & picks2Look & ?); first done. *)
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

  Lemma m_contains_tokens_for_picks_merge Ω picks1 picks2 (m1 m2 : iResUR Σ) :
    (∀ i γ a b, (m1 i) !! γ = Some a → (m2 i) !! γ = Some b → a ≡ b) →
    res_for_picks Ω picks1 m1 →
    res_for_picks Ω picks2 m2 →
    res_for_picks Ω (merge_picks picks1 picks2) (m1 ⋅ m2).
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

  Lemma own_picks_sep Ω picks1 picks2 :
    own_picks Ω picks1 -∗
    own_picks Ω picks2 -∗
    own_picks Ω (merge_picks picks1 picks2).
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
  Context {Σ : gFunctors}.

  Implicit Types (prs : list (promise_info Σ)).

  Definition promises_overlap_pred prs1 prs2 : Prop :=
    ∀ id γ p1 p2,
      promises_lookup_at prs1 id γ = Some p1 →
      promises_lookup_at prs2 id γ = Some p2 →
      pred_stronger (promise_at_pred p1) (promise_at_pred p2) ∨
        pred_stronger (promise_at_pred p2) (promise_at_pred p1).

  (* If two promise lists has an overlap then one of the overlapping promises
  * is strictly stronger than the other. *)
  Lemma own_promises_overlap Ω prs1 prs2 :
    own_promises Ω prs1 -∗
    own_promises Ω prs2 -∗
    ⌜ promises_overlap_pred prs1 prs2 ⌝.
  Proof.
    iIntros "(%m1 & O1 & %P1) (%m2 & O2 & %P2)".
    iIntros (id γ p1 p2 look1 look2).
    iCombine "O1 O2" as "O".
    iDestruct (ownM_valid with "O") as "#Hv".
    rewrite discrete_fun_validI.
    setoid_rewrite gmap_validI.
    iSpecialize ("Hv" $! id γ).
    rewrite lookup_op.
    (* rewrite /res_for_promises in P1, P2. *)
  Admitted.

  Lemma own_promises_sep Ω prs1 prs2 :
    own_promises Ω prs1 -∗
    own_promises Ω prs2 -∗
    own_promises Ω (merge_promises prs1 prs2).
  Proof.
  Admitted.

End own_promises_properties.

(* In this section we prove structural rules of the nextgen modality. *)

Section nextgen_properties.
  Context {Σ : gFunctors} {Ω : @gTransforms Σ}.

  Lemma res_for_picks_empty :
    res_for_picks Ω (λ i : gid Σ, ∅) ε.
  Proof. done. Qed.

  Lemma own_picks_empty :
    ⊢@{iProp Σ} own_picks _ (λ i : gid Σ, ∅).
  Proof. iExists ε. rewrite ownM_unit' left_id. iPureIntro. done. Qed.

  Lemma res_for_promises_empty :
    res_for_promises Ω [] (ε : iResUR Σ).
  Proof. intros ? elem. inversion elem. Qed.

  Lemma own_promises_empty :
    ⊢@{iProp Σ} own_promises Ω [].
  Proof.
    iExists ε. rewrite ownM_unit' left_id.
    iPureIntro. apply res_for_promises_empty.
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

(** The transformations [ts] satisfies the predicates [ps]. *)
Equations preds_hold {n} {DS : ivec n cmra}
    (ts : trans_for n DS) (ps : preds_for n DS) : Prop :=
  | hcons t ts', hcons p ps' := p t ∧ preds_hold ts' ps' ;
  | hnil, hnil := True.
Global Transparent preds_hold.

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
      preds_hold ts deps_preds → ∃ (e : A → A), (huncurry R_2) ts e) →
    (* For every dependency we own a [rely_self]. *)
    (∀ (i : fin n), rely_self (γs !!! i) (deps_preds 👀 i)) -∗
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
    destruct pred_prefix as [(isLast1 & look1) ?].
    destruct rely_pred_prefix as [(isLast2 & look2) ?].
    rewrite last_lookup in isLast1.
    rewrite last_lookup in isLast2.
    eapply look1; last done.
    { apply le_pred. apply prefix_length. eassumption. }
    eapply prefix_lookup; done.
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
    Definition PS : preds_for _ _ := [P1; P2].
    Compute (preds_hold (DS := [A; B]) TS PS).

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
