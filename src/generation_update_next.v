From Equations Require Import Equations.

From iris.algebra Require Import functions gmap agree excl csum max_prefix_list.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

From iris_named_props Require Import named_props.

From self Require Import hvec extra basic_nextgen_modality gen_trans
  gen_single_shot gen_pv.

Import uPred.

(** Data describing the cameras that a given camera depends on. *)
Definition deps_ty n := ivec n Type.
Definition deps n := ivec n cmra.
Bind Scope ivec_scope with deps.

Section types.

  (** A transformation over the carrier of [A]. *)
  Definition cmra_to_trans A := cmra_car A → cmra_car A.

  (** A predicate over a transformation over [A]. *)
  Definition cmra_to_pred A := (cmra_to_trans A) → Prop.

  Definition pred_over_ty {n} (DS : deps_ty n) (A : Type) :=
    iimpl id DS ((A → A) → Prop).

  Definition pred_over {n} (DS : deps n) A :=
    iimpl id (ivec_map cmra_to_trans DS) ((A → A) → Prop).

  Definition True_pred {n} {DS : deps n} {A} : pred_over DS A :=
    hcurry (λ _ _, True).

  (* This results in the type:
     [(max_nat → max_nat) → (excl () → excl ()) → (nat → nat) → Prop] *)
  Compute (pred_over [max_natR; exclR unitO] natR).

End types.

Definition trans_for n (DS : deps n) := hvec id n (cmra_to_trans <$> DS).

Notation preds_for := (hvec cmra_to_pred).

(* trans_for does not give universe issue. *)
Definition test_exist {Σ} {n : nat} {DS : deps n} : iProp Σ :=
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

  Canonical Structure pred_over_tyO (A : Type) (DS : deps_ty n) :=
    leibnizO (pred_over_ty DS A).
  Canonical Structure pred_overO (A : Type) (DS : deps n) :=
    leibnizO (pred_over DS A).

  Definition promises (A : Type) (DS : deps_ty n) :=
    max_prefix_list (pred_over_ty DS A).
  Definition promisesR (A : cmra) (DS : deps n) :=
    max_prefix_listR (pred_over DS A).
  Definition promisesUR (A : cmra) (DS : deps n) :=
    max_prefix_listUR (pred_over DS A).

  (* Authorative promises. *)
  Definition auth_promises {A : Type} {DS : deps n}
    (ps : list (pred_over DS A)) : auth (max_prefix_list (pred_over DS A)) :=
    ● (to_max_prefix_list ps).
  Definition auth_promises_ty {A : Type} {DS : deps_ty n}
    (ps : list (pred_over_ty DS A)) : auth (promises A DS) :=
    ● (to_max_prefix_list ps).

  (* Fragmental promises. *)
  Definition frag_promises {A : Type} {DS : deps_ty n}
    (ps : list (pred_over_ty DS A)) : auth (promises A DS) :=
    ◯ (to_max_prefix_list ps).

End dependency_relation_cmra.

Section dependency_relation_extra.
  Context {n} {A : cmra} {DS : deps n}.
  Implicit Types (R : pred_over DS A) (P : (A → A) → Prop).

  Definition pred_stronger (R1 R2 : pred_over DS A) :=
    ∀ (ts : trans_for n DS) (t : A → A),
      huncurry R1 ts t → huncurry R2 ts t.

  Definition pred_weaker (R1 R2 : pred_over DS A) := pred_stronger R2 R1.

  Definition rel_implies_pred R P : Prop :=
    ∀ (ts : trans_for n DS) (t : A → A), huncurry R ts t → P t.

  Definition pred_prefix_list_for (all : list (pred_over DS A)) R :=
    (* The given promise [R] is the last promise out of all promises. *)
    last all = Some R ∧
    (* The list of promises increases in strength. *)
    ∀ i j (Ri Rj : pred_over DS A),
      i ≤ j → all !! i = Some Ri → all !! j = Some Rj → pred_weaker Ri Rj.

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

Definition generational_cmra {n} A (DS : deps_ty n) : Type :=
  option (agree (A → A)) * GTS (A → A) *
    option A * gen_pv (auth (promises A DS)).

Definition generational_cmraR {n} (A : cmra) (DS : deps n) :=
  prodR
    (prodR (prodR (optionR (agreeR (leibnizO (A → A)))) (GTSR (A → A))) (optionR A))
    (gen_pvR (authR (promisesR A DS))).

Definition gen_generation_first {A : cmra} (f : A → A) :
  prodR (optionR (agreeR (leibnizO (A → A)))) (GTSR (A → A)) →
  prodR (optionR (agreeR (leibnizO (A → A)))) (GTSR (A → A))
  := prod_map
       (const (Some (to_agree f)) : optionR (agreeR (leibnizO (A → A))) → optionR (agreeR (leibnizO (A → A))))
       (GTS_floor : (GTSR (A → A)) → (GTSR (A → A))).

(* The generational transformation function for the encoding of each ownership
over a generational camera. *)
Definition gen_generation {n} {A : cmra} (DS : deps n)
    (f : A → A) : generational_cmraR A DS → generational_cmraR A DS :=
  prod_map
    (prod_map (gen_generation_first f) (fmap f : optionR A → optionR A))
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

Global Instance gen_generation_gen_trans {n} {A : cmra} {DS : deps n} (f : A → A)
  `{!Proper (equiv ==> equiv) f} :
  GenTrans f → GenTrans (gen_generation DS f).
Proof. apply _. Qed.

Global Instance gen_generation_proper {n} {A : cmra} (DS : deps n) (f : A → A) :
  Proper ((≡) ==> (≡)) f →
  Proper ((≡) ==> (≡)) (gen_generation DS f).
Proof.
  intros ? [[??]?] [[??]?] [[??]?]. simpl in *.
  rewrite /gen_generation /gen_generation_first.
  solve_proper.
Qed.

(* Working with the 4-tuple is sometimes annoying. Then these lemmas help. *)
Lemma prod_valid_1st {Σ} {A B C D : cmra} (a : A) (b : B) (c : C) (d : D) e f g h :
  ✓ ((a, b, c, d) ⋅ (e, f, g, h)) ⊢@{iProp Σ} ✓ (a ⋅ e).
Proof. rewrite 3!prod_validI. iIntros "[[[$ _] _] _]". Qed.

Lemma prod_valid_2st {Σ} {A B C D : cmra} (a : A) (b : B) (c : C) (d : D) e f g h :
  ✓ ((a, b, c, d) ⋅ (e, f, g, h)) ⊢@{iProp Σ} ✓ (b ⋅ f).
Proof. rewrite 3!prod_validI. iIntros "[[[_ $] _] _]". Qed.

Lemma prod_valid_3th {Σ} {A B C D : cmra} (a : A) (b : B) (c : C) (d : D) e f g h :
  ✓ ((a, b, c, d) ⋅ (e, f, g, h)) ⊢@{iProp Σ} ✓ (c ⋅ g).
Proof. rewrite 3!prod_validI. iIntros "[[_ $] _]". Qed.

Lemma prod_valid_4th {Σ} {A B C D : cmra} (a : A) (b : B) (c : C) (d : D) e f g h :
  ✓ ((a, b, c, d) ⋅ (e, f, g, h)) ⊢@{iProp Σ} ✓ (d ⋅ h).
Proof. rewrite 3!prod_validI. iIntros "[_ $]". Qed.

Class genInG {n} (Σ : gFunctors) (A : cmra) (DS : deps n) := GenInG {
  genInG_inG : inG Σ (generational_cmraR A DS);
  genInG_inG_deps : ∀ i d, DS !!! i = d → inG Σ (generational_cmraR A DS);
  (* genInG_id : gid Σ; *)
  (* genInG_apply := rFunctor_apply (gFunctors_lookup Σ genInG_id); *)
  (* genInG_gti : gen_trans_info Σ (genInG_id); *)
  (* genInG_gen_trans : Ω.(g_valid_gt) (genInG_id) = Some2 genInG_gti; *)
  (* genInG_gti_typ : A = genInG_gti.(gti_car); *)
  (* genInG_prf : A = genInG_apply (iPropO Σ) _; *)
  (* genInG_gen_trans2 : *)
  (*   genInG_gti.(gti_valid) = *)
  (*     (gen_transport (gen_cmra_eq genInG_gti_typ genInG_gti.(gti_look)) (lift g)); *)
}.

Existing Instance genInG_inG.

(* Knowledge that [A] is a resource, with the information about its dependencies
hidden in the dependent pair. *)
Class genInSelfG (Σ : gFunctors) (A : cmra) := GenInG2 {
  genInSelfG_n : nat;
  genInSelfG_DS : deps genInSelfG_n;
  genInSelfG_gen : genInG Σ A (genInSelfG_DS);
}.

Existing Instance genInSelfG_gen.
(* Global Arguments genInG_id {_ _ _ _} _. *)
(* Global Program Instance genInG_inG {n} {DS : deps n} `{i : !genInG Σ A DS} : *)
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

  (** [TransMap] contains transformation functions for a subset of ghost names. It is
  the entries that we have picked generational transformations for. *)
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

(* Definition of the next generation modality. *)
Section promises.
  Context `{Σ : gFunctors}.

  Implicit Types (transmap : TransMap Σ).

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
    pi_id : gid Σ; (* The index of the RA in the global RA. *)
    pi_γ : gname; (* Ghost name for the promise. *)
    pi_n : nat; (* The number of dependencies. *)
    pi_deps : ivec pi_n promise_self_info;
    (* The predicate that relates our transformation to those of the dependencies. *)
    (* pi_rel : hvec (λ dep, T Σ dep.(psi_id)) pi_n pi_deps → T Σ pi_id → Prop; *)
    pi_rel : deps_to_trans pi_n pi_deps → T Σ pi_id → Prop;
    (* A predicate that holds for the promise's own transformation whenever
    * [pi_rel] holds. A "canonical" choice could be: [λ t, ∃ ts, pi_rel ts t]. *)
    pi_pred : T Σ pi_id → Prop;
    pi_rel_to_pred : ∀ ts t, pi_rel ts t → pi_pred t;
    pi_witness : ∀ ts, deps_preds_hold pi_deps ts → ∃ t, pi_rel ts t;
  }.

  (** Convert a [promise_info] into a [promise_self_info] by discarding fields
   * about dependencies. *)
  Definition promise_info_to_self (pi : promise_info) :=
    {| psi_id := pi_id pi; psi_γ := pi_γ pi; psi_pred := pi_pred pi |}.

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
    ∀ i p, ps !! i = Some p → transmap_satisfy_rel transmap p.

  Definition promises_unique (promises : list promise_info) : Prop :=
    ∀ i j p1 p2, i ≠ j → promises !! i = Some p1 → promises !! j = Some p2 →
      p1.(pi_id) ≠ p2.(pi_id) ∨ p1.(pi_γ) ≠ p2.(pi_γ).

  Definition promises_different p1 p2 :=
    p1.(pi_id) ≠ p2.(pi_id) ∨ p1.(pi_γ) ≠ p2.(pi_γ).

  Definition promises_has_deps (promises : list (promise_info)) p :=
    ∀ idx, ∃ p_d j,
      promises !! j = Some p_d ∧
      p.(pi_deps) !!! idx = promise_info_to_self p_d.

  Definition promise_well_formed p (promises : list (promise_info)) : Prop :=
    (∀ i p2, promises !! i = Some p2 → promises_different p p2) ∧
    promises_has_deps promises p.

  (* This definition has nice computational behavior when applied to a [cons]. *)
  Fixpoint promises_well_formed (promises : list (promise_info)) : Prop :=
    match promises with
    | nil => True
    | cons p promises' =>
      promise_well_formed p promises' ∧ promises_well_formed promises'
    end.

  (* A well formed promise is not equal to any of its dependencies. *)
  Lemma promise_well_formed_neq_deps p (promises : list (promise_info)) :
    promise_well_formed p promises →
    ∀ idx,
      pi_id p ≠ psi_id (pi_deps p !!! idx) ∨ pi_γ p ≠ psi_γ (pi_deps p !!! idx).
  Proof.
    intros [uniq hasDeps] idx.
    destruct (hasDeps idx) as (p2 & i & look & ->).
    destruct p2.
    apply (uniq i _ look).
  Qed.

  Lemma promises_well_formed_lookup promises idx p :
    promises_well_formed promises →
    promises !! idx = Some p →
    promises_has_deps promises p. (* We forget the different part for now. *)
  Proof.
    intros WF look.
    revert dependent idx.
    induction promises as [ |?? IH].
    - intros ? [=].
    - destruct WF as [[? hasDeps] WF'].
      intros [ | idx].
      * simpl. intros [= ->].
        intros idx.
        destruct (hasDeps idx) as (? & i & ? & ?).
        eexists _, (S i). done.
      * intros look.
        intros d.
        destruct (IH WF' idx look d) as (? & i & ? & ?).
        eexists _, (S i). done.
  Qed.

  Lemma transmap_satisfy_well_formed_cons p promises transmap :
    promises_well_formed (p :: promises) →
    transmap_resp_promises transmap promises →
    ∃ ts,
      trans_at_deps transmap p ts ∧
      deps_preds_hold p.(pi_deps) ts.
  Proof.
    intros WF resp.
    destruct WF as [[uniq hasDeps] WF'].
    set (F := (λ dep, T Σ dep.(psi_id))).
    edestruct (fun_ex_to_ex_hvec (F := F) p.(pi_deps)
      (λ i x,
        let pd := p.(pi_deps) !!! i in
        pd.(psi_pred) x ∧
        transmap (psi_id pd) !! psi_γ pd = Some x))
      as (ts & ?).
    { intros di.
      destruct (hasDeps di) as (p' & j & look & ->).
      destruct (resp _ _ look) as (ts & (t & ? & ? & ?)).
      specialize (p'.(pi_rel_to_pred) ts t H1) as hipo.
      exists t. destruct p'. done. }
    exists ts.
    rewrite deps_preds_hold_alt.
    split.
    - intros di. apply H.
    - intros di. apply H.
  Qed.

  (* For soundness we need to be able to build a map of gts that agree with
   * picks and that satisfy all promises.

     We need to be able to extend picks along a list of promises.

     We must also be able to combine to lists of promises.
  *)

  (* Equations promises_lookup *)
  (*   (ps : list (promise_info)) (id : gid Σ) (γ : gname) : option (T Σ id) := *)
  (* | [], id, γ => None *)
  (* | p :: ps', id, γ with (decide (p.(pi_id) = id)) => { *)
  (*   | left eq_refl => Some (p.(pi_)) *)
  (*   | right neq => _ *)
  (* }. *)

  (* When we store picks we also need to store the promises that they are
   * related with. We store these promises in a map. This map should contain
   * promises at the "right" indices which this definition expresses. *)
  Definition promise_map_well_formed (pm : ∀ i, gmap gname promise_info) : Prop :=
    ∀ i γ p, (pm i) !! γ = Some p → p.(pi_id) = i ∧ p.(pi_γ) = γ.

  (* TODO: We need to store evidence that the picks in [transmap] satisfies the
   * relations and predicates in the [promises]. *)

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

  Lemma transmap_resp_promises_cons transmap p promises :
    transmap_resp_promises transmap promises ∧ transmap_satisfy_rel transmap p ↔
    transmap_resp_promises transmap (p :: promises).
  Proof.
    rewrite /transmap_resp_promises. split.
    - intros [all sat] [|n'] p'; simpl.
      * intros [= ->]. apply sat.
      * apply all.
    - intros all. split.
      * intros i p' look. apply (all (S i)). apply look.
      * apply (all 0). done.
  Qed.

  Lemma transmap_resp_promises_insert p promises transmap t :
    promises_well_formed (p :: promises) →
    transmap_resp_promises transmap promises →
    transmap_resp_promises (transmap_insert transmap (pi_id p) (pi_γ p) t) promises.
  Proof.
    intros [[uniq hasDeps] WF] resp idx p2 look.
    rewrite /transmap_satisfy_rel.
    specialize (resp idx p2 look).
    destruct resp as (t' & ts & hi).
    exists t', ts.
    rewrite /trans_at_deps.
    setoid_rewrite transmap_insert_lookup_ne.
    + apply hi.
    + apply (uniq idx p2 look).
    + specialize (
        promises_well_formed_lookup promises idx p2 WF look) as hasDeps2.
      specialize (hasDeps2 idx0) as (p3 & ? & look3 & eq).
      rewrite eq.
      specialize (uniq _ p3 look3).
      destruct p3.
      apply uniq.
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

 Lemma transmap_promises_to_maps transmap (promises : list promise_info) :
    transmap_overlap_resp_promises transmap promises →
    promises_well_formed promises →
    ∃ (map : TransMap Σ),
      transmap_resp_promises map promises ∧
      transmap ⊆ map.
  Proof.
    induction promises as [|p promises' IH].
    - intros _. exists transmap.
      split; last done.
      intros ? ?. inversion 1.
    - intros HR [WF WF'].
      specialize (promise_well_formed_neq_deps _ _ WF) as depsDiff.
      destruct IH as (map & resp & sub).
      {  eapply transmap_overlap_resp_promises_cons. done. } { done. }
      (* We either need to use the transformation in [picks] or extract one
       * from [p]. *)
      destruct (transmap p.(pi_id) !! p.(pi_γ)) eqn:look.
      + destruct (HR 0 p) as [sat | ?]; [done | | congruence].
        destruct sat as (ts & t & transIn & hold & pRelHolds).
        exists map. (* We don't insert as map already has transformation. *)
        split; last done.
        apply transmap_resp_promises_cons. split; try done.
        eexists _, _. split_and!; last done.
        -- specialize (sub p.(pi_id)).
           rewrite map_subseteq_spec in sub.
           apply sub.
           done.
        -- eapply trans_at_deps_subseteq; done.
      + eassert _ as sat.
        { eapply transmap_satisfy_well_formed_cons; done. }
        destruct sat as (ts & transIn & hold).
        eassert (∃ t, _) as [t pRelHolds].
        { apply p.(pi_witness). apply hold. }
        exists (transmap_insert map p.(pi_id) p.(pi_γ) t).
        split.
        * apply transmap_resp_promises_cons.
          split.
          -- apply transmap_resp_promises_insert; done.
          -- rewrite /transmap_satisfy_rel.
            exists ts, t.
            split. { by rewrite transmap_insert_lookup. }
            split; last done.
            intros ??.
            rewrite transmap_insert_lookup_ne; first apply transIn.
            apply depsDiff.
        * apply transmap_insert_subseteq_r; done.
  Qed.

  Lemma promises_to_maps (promises : list promise_info) :
    promises_well_formed promises →
    ∃ (transmap : TransMap Σ), transmap_resp_promises transmap promises.
  Proof.
    intros WF.
    edestruct (transmap_promises_to_maps (λ i : gid Σ, ∅)) as [m [resp a]].
    2: { done. }
    - intros ???. right. done.
    - exists m. apply resp.
  Qed.

  (* (* Turn a map of picks and a list of promises into a full map of picks. *) *)
  (* Definition build_full_promises picks (ps : list (promise_info)) : TransMap Σ := *)
  (*   λ id, ∅. *)
  (*   (* λ id, *) *)
  (*   (*   foldl (λ p m, *) *)
  (*   (*     if (id = p.(pi_id)) *) *)
  (*   (*     then <[ p.(pi_γ) := p.(pi_) ] *) *)
  (*   (*   ) (ø) ps. *) *)

  (* (* TODO: This is the key result that we want to prove. *) *)
  (* Lemma build_full_properties picks ps : *)
  (*   let gt := build_full_promises picks ps *)
  (*   in picks ⊆ gt ∧ transmap_resp_promises gt ps. *)
  (* Proof. *)
  (* Admitted. *)

  (* NOTE: This is not possible! We need to feed the picks into the promises as
  * the resulting transformation can depend on the picks. *)
  (* TODO: This is the key result we want to prove. *)
  Lemma map_from_transmap_promises transmap promises :
    promises_well_formed promises →
    ∃ (map : TransMap Σ),
      transmap_resp_promises map promises ∧
      transmap ⊆ map.
  Proof.
    intros WF.
    edestruct (promises_to_maps) as (mapP & resp); first done.
    exists (transmap ∪ mapP).
    split; last apply transmap_union_subseteq_l.
    intros ? p look.
    destruct (resp i _ look) as (ts & t & ? & ? & ?).
    destruct (transmap p.(pi_id) !! p.(pi_γ)) as [t2|] eqn:look2.
    - eexists _, t2.
      admit.
    - exists ts, t.
      split_and!; last done.
      * rewrite lookup_union_r; done.
      * intros idx.
        simpl.
        rewrite lookup_union_r; try done.
  Abort.

End promises.

Arguments promise_info Σ : clear implicits.
Arguments promise_self_info Σ : clear implicits.

Section next_gen_definition.
  Context `{Σ : gFunctors}.

  Implicit Types (picks : TransMap Σ).

  (* The resource [m] contains the agreement resources for all the picks in
  [picks]. *)
  Definition res_for_picks picks (m : iResUR Σ) :=
    ∀ i,
      dom (picks i) ≡ dom (m i) ∧
      (∀ γ (a : Rpre Σ i),
        m i !! γ = Some a  →
        (* NOTE: Maybe we'll need to pull this equality out of a global map as
         * before. *)
        ∃ n (A : cmra) (DS : deps n)
          (eq : generational_cmraR A DS = R Σ i) (t : A → A) R Rs,
          (* ∃ gti (t : gti.(gti_car) → gti.(gti_car)), *)
            (* Ω.(g_valid_gt) i = Some2 gti ∧ *)
          picks i !! γ = Some (cmra_map_transport eq (gen_generation DS t)) ∧
          pred_prefix_list_for Rs R ∧
          a ≡ map_unfold (cmra_transport eq
            (None, GTS_tok_gen_shot t, None, gV (●□ (to_max_prefix_list Rs))))).

  Definition own_picks picks : iProp Σ :=
    ∃ m, uPred_ownM m ∗ ⌜ res_for_picks picks m ⌝.

  Definition res_for_promises (ps : list (promise_info Σ)) (m : iResUR Σ) :=
    ∀ p, p ∈ ps →
      ∃ n (a : Rpre Σ p.(pi_id)) (A : cmra) (DS : deps n)
      (* NOTE: Is there a better way to get a hold of [A] and [DS]? *)
      (eq : generational_cmraR A DS = R Σ p.(pi_id)) Rel Rs,
        m p.(pi_id) !! p.(pi_γ) = Some a ∧
        pred_prefix_list_for Rs Rel ∧
        a ≡ map_unfold (cmra_transport eq
          (None, (None, None), None, gV (◯ (to_max_prefix_list Rs)))).

  Definition own_promises (ps : list (promise_info Σ)) : iProp Σ :=
    ∃ m, uPred_ownM m ∗ ⌜ res_for_promises ps m ⌝ .

  (* The global transformation [fG] respects the entries in [picks].
   * NOTE: We may not need this given how [⚡==>] now quantifies over picks and
   * not global transformations. *)
  Definition gt_resp_picks (fG : iResUR Σ → iResUR Σ) picks :=
    ∀ (m : iResUR Σ) i γ a t,
      m i !! γ = Some a → (* For every element in the old element. *)
      picks i !! γ = Some t →
      (fG m) i !! γ = Some (map_unfold (t (map_fold a))).

  Definition nextgen P : iProp Σ :=
    ∃ picks (ps : list (promise_info Σ)),
      (* We own resources for everything in [picks] and [promises]. *)
      own_picks picks ∗ own_promises ps ∗
      ⌜ promises_well_formed ps ⌝ ∗
      ∀ full_picks (val : transmap_valid full_picks),
        ⌜ transmap_resp_promises full_picks ps ⌝ ∗
        ⌜ picks ⊆ full_picks ⌝ ∗
        let _ := build_trans_generation full_picks val in (* Why is this instance not found automatically? *)
        ⚡={build_trans full_picks}=> P.

End next_gen_definition.

Notation "⚡==> P" := (nextgen P)
  (at level 99, P at level 200, format "⚡==>  P") : bi_scope.

Section nextgen_properties.
  Context {Σ : gFunctors}.

  Lemma res_for_picks_empty :
    res_for_picks (λ i : gid Σ, ∅) ε.
  Proof. done. Qed.

  Lemma own_picks_empty :
    ⊢@{iProp Σ} own_picks (λ i : gid Σ, ∅).
  Proof. iExists ε. rewrite ownM_unit' left_id. iPureIntro. done. Qed.

  Lemma res_for_promises_empty :
    res_for_promises [] (ε : iResUR Σ).
  Proof. intros ? elem. inversion elem. Qed.

  Lemma own_promises_empty :
    ⊢@{iProp Σ} own_promises [].
  Proof.
    iExists ε. rewrite ownM_unit' left_id.
    iPureIntro. apply res_for_promises_empty.
  Qed.

  Lemma nextgen_emp_2 : emp ⊢@{iProp Σ} ⚡==> emp.
  Proof.
    iIntros "emp".
    rewrite /nextgen.
    iExists (λ i, ∅), [].
    iSplitL "". { iApply own_picks_empty. }
    iSplitL "". { iApply own_promises_empty. }
    iSplit; first done.
    iIntros (full_picks ?).
  Qed.

  Lemma nextgen_sep_2 P Q :
    (⚡==> P) ∗ (⚡==> Q) ⊢@{iProp Σ} ⚡==> (P ∗ Q) .
  Proof.
  Admitted.

End nextgen_properties.

(* Ownership over generational ghost state. *)

Section generational_resources.
  Context {n} {A} {DS : deps n} `{!genInG Σ A DS}.
  Implicit Types (R : pred_over DS A) (P : (A → A) → Prop).

  Definition gen_own_res (a : A) : generational_cmraR A DS :=
    (None, (None, None), Some a, ε).

  Definition gen_own (γ : gname) (a : A) : iProp Σ :=
    own γ (gen_own_res a).

  Definition own_shot γ t : iProp Σ :=
    own γ ((None, GTS_tok_gen_shot t, None, ε)).

  Definition gen_token_used γ : iProp Σ :=
    own γ ((None, GTS_tok_perm, None, ε)).

  Definition gen_picked_in γ (t : A → A) : iProp Σ :=
    own γ ((Some (to_agree t), (None, None), None, ε) : generational_cmraR A DS).

  Definition gen_token γ : iProp Σ :=
    own γ ((None, GTS_tok_both, None, ε)).

  Definition token_res all : generational_cmraR A DS :=
    (None, GTS_tok_both, None, gPV (● (to_max_prefix_list all))).

  (** Ownership over the token and the promises for [γ]. *)
  Definition token (γ : gname) (γs : ivec n gname) R P : iProp Σ :=
    ∃ (all : list (pred_over DS A)),
      ⌜ pred_prefix_list_for' all R P ⌝ ∗
      own γ (token_res all).

  Definition used_token (γ : gname) (γs : ivec n gname) R P : iProp Σ :=
    ∃ (all : list (pred_over DS A)),
      ⌜ pred_prefix_list_for' all R P ⌝ ∗
      own γ ((
        None,
        GTS_tok_both,
        None,
        gP (● to_max_prefix_list all) ⋅ gV (●□ to_max_prefix_list all)
      ) : generational_cmraR A DS).

  (* TODO: We need some way of converting between the relations stored in
   * promise_info and the relations stored by the user. *)

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
      "#pref_list" ∷ ⌜ pred_prefix_list_for' all R P ⌝ ∗
      "own_preds" ∷ own γ ((None, (None, None), None,
              gPV (◯ to_max_prefix_list all)) : generational_cmraR A DS).

End generational_resources.

Definition rely_self `{i : !genInSelfG Σ A}
    γ (P : (A → A) → Prop) : iProp Σ :=
  ∃ γs R, rely (DS := genInSelfG_DS) γ γs R P.

(** The transformations [ts] satisfies the predicates [ps]. *)
Equations preds_hold {n} {DS : deps n}
    (ts : trans_for n DS) (ps : preds_for n DS) : Prop :=
  | hcons t ts', hcons p ps' := p t ∧ preds_hold ts' ps' ;
  | hnil, hnil := True.
Global Transparent preds_hold.

Section rules.
  Context {n : nat} {DS : deps n} `{!genInG Σ A DS}.

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
    own γ (None, GTS_tok_perm, None, ε) ∗
    own γ (None, GTS_tok_gen, None, ε).
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
  Lemma token_strengthen_promise `{∀ (i : fin n), genInSelfG Σ (DS !!! i)}
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
  Lemma rely_nextgen γ γs (R : pred_over DS A) P `{∀ (i : fin n), genInSelfG Σ (DS !!! i)} :
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
    iSplitL.
    iModIntro.
  Admitted.

  Lemma token_to_rely γ γs (R : pred_over DS A) P :
    token γ γs R P ⊢ rely γ γs R P.
  Proof. Admitted.

  Lemma token_rely_combine_pred γ γs R1 P1 R2 P2 :
    token γ γs R1 P1 -∗ rely γ γs R2 P2 -∗ ⌜ pred_stronger R1 R2 ⌝.
  Proof.
    iDestruct 1 as (prs1 prefix1) "own1".
    iDestruct 1 as (prs2 prefix2) "own2".
    iDestruct (own_valid_2 with "own1 own2") as "val".
    iDestruct (prod_valid_4th with "val") as "%val".
    iPureIntro.
    move: val.
    rewrite gen_pv_op. rewrite gen_pv_valid.
    rewrite auth_both_valid_discrete.
    rewrite to_max_prefix_list_included_L.
    intros [prefix _].
    destruct prefix1 as [(isLast1 & look1) ?].
    destruct prefix2 as [(isLast2 & look2) ?].
    rewrite last_lookup in isLast1.
    rewrite last_lookup in isLast2.
    eapply look1; last done.
    { apply le_pred. apply prefix_length. eassumption. }
    eapply prefix_lookup; done.
  Qed.

  Lemma rely_combine_pred γ γs R1 P1 R2 P2 :
    rely γ γs R1 P1 -∗
    rely γ γs R2 P2 -∗
    ⌜ pred_stronger R1 R2 ∨ pred_stronger R2 R1 ⌝.
  Proof.
    iDestruct 1 as (prs1 prefix1) "own1".
    iDestruct 1 as (prs2 prefix2) "own2".
    iDestruct (own_valid_2 with "own1 own2") as "val".
    iDestruct (prod_valid_4th with "val") as "%val".
    iPureIntro.
    move: val.
    rewrite gen_pv_op. rewrite gen_pv_valid.
    rewrite auth_frag_valid.
    rewrite to_max_prefix_list_op_valid_L.
    destruct prefix1 as [(isLast1 & look1) ?].
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
Global Instance genInG_forall_2 {Σ n m} {DS1 : deps n} {DS2 : deps m}
  `{!genInG Σ A DS1} `{!genInG Σ B DS2} :
  ∀ (i : fin 2), genInSelfG Σ ([A; B]%IL !!! i).
Proof.
  apply forall_fin_2.
  split.
  - apply (GenInG2 _ _ n DS1 _).
  - apply (GenInG2 _ _ m DS2 _).
Qed.

Section test.
  Context `{max_i : !inG Σ max_natR}.
  Context `{i : !genInG Σ max_natR [max_natR; max_natR] }.

  Definition a_rely :=
    rely (1%positive) [2%positive; 3%positive] (λ Ta Tb Ts, Ta = Ts ∧ Tb = Ts) (λ _, True).

  Section test.
    Variables (A : cmra) (B : cmra) (T1 : A → A) (T2 : B → B)
      (P1 : (A → A) → Prop) (P2 : (B → B) → Prop).

    Definition TS : trans_for _ [A; B] := [T1; T2]%HV.
    Definition PS : preds_for _ _ := [P1; P2].
    Compute (preds_hold (DS := [A; B]) TS PS).

    Context `{!genInG Σ B [] }.
    Context `{!genInG Σ A [A; B] }.

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
