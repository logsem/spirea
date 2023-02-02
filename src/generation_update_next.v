From Equations Require Import Equations.

From iris.algebra Require Import functions gmap agree excl csum.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

From self Require Import extra basic_nextgen_modality gen_trans gen_single_shot.
From self Require Import hvec.

Import uPred.

(** Data describing the cameras that a given camera depends on. *)
Definition deps n := ivec n cmra.
Bind Scope ivec_scope with deps.

Section types.
  (* Implicit Type (n : nat) (DS : deps n) (A : cmra). *)

  (** A transformation over the carrier of [A]. *)
  Definition cmra_to_trans A := cmra_car A → cmra_car A.

  (** A predicate over a transformation over [A]. *)
  Definition cmra_to_pred A := (cmra_to_trans A) → Prop.

  (* Definition deps_to_trans {n} DS : ivec Type n := *)
  (*   ivec_fmap (λ A, cmra_car A → cmra_car A) DS. *)

  Definition pred_over {n} (DS : deps n) A :=
    iimpl cmra_to_trans DS ((A → A) → Prop).

  Definition True_pred {n} {DS : deps n} {A} : pred_over DS A :=
    hcurry (λ _ _, True).

  (* This results in the type:
     [(max_nat → max_nat) → (excl () → excl ()) → (nat → nat) → Prop] *)
  Compute (pred_over [max_natR; exclR unitO] natR).

  (* Definition to_pred_ty DS : ivec Type := ivec_fmap cmra_to_pred DS. *)

End types.

Notation trans_for := (hvec cmra_to_trans).
Definition trans_for_alt n (DS : deps n) := hvec id n (cmra_to_trans <$> DS).

Notation preds_for := (hvec cmra_to_pred).

(* trans_for_alt does not give universe issue. *)
Definition test_exist {Σ} {n : nat} {DS : deps n} : iProp Σ :=
  ∃ (ts : trans_for_alt n DS), ⌜ True ⌝.

(* trans_for _does_ give universe issue. The root cause is the way the [cmra] appears in the type. In [trans_for_alt] the occurence of [cmra_car] prevents the universe issue somehow. *)
(* Definition test_exist {Σ} {n : nat} {DS : ivec cmra n} : iProp Σ := *)
(*   ∃ (ts : trans_for n DS), ⌜ True ⌝. *)

(* The functor in [Σ] at index [i] applied to [iProp]. *)
Notation R Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPropO Σ)).
(* The functor in [Σ] at index [i] applied to [iPreProp]. *)
Notation Rpre Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ)).
Notation T Σ i := (R Σ i → R Σ i).

Record promise {Σ} := MkPromise {
    promise_g : gname; (* Ghost name for the promise. *)
    promise_i : gid Σ; (* The index of the RA in the global RA. *)
    promise_n : nat; (* The number of dependencies. *)
    promise_deps : list nat; (* Indices in the list of promises of the dependencies. *)
    promise_RAs : ivec promise_n (gid Σ);
    (* The predicate that relates our transformation to those of the dependencies. *)
    promise_rel : hvec (λ (i : gid Σ), T Σ i : Type) promise_n promise_RAs → T Σ promise_i → Prop;
    promise_pred : T Σ promise_i → Prop;
    (* rel_impl_pred : ; *)
    (* deps_preds : foo; *)
    (* witness : foo; *)
}.

(* TODO: Adapt this. *)
Definition generational_cmra A : Type := A.
  (* option (agree (A → A)) * GTS (A → A) * option A. *)
Definition generational_cmraR (A : cmra) := A.
  (* prodR (prodR (optionR (agreeR (leibnizO (A → A)))) (GTSR (A → A))) (optionR A). *)

Definition promise_consistent {Σ} (promises : list (@promise Σ)) p i :=
  ∀ x j,
    p.(promise_deps) !! x = Some j →
    j < i ∧ (* The dependency is prior in the list. *)
    ∃ p_d M,
      promises !! j = Some p_d ∧
      p.(promise_RAs) !! x = Some M ∧
      p_d.(promise_i) = M.

Definition promises_consistent {Σ} (promises : list (@promise Σ)) :=
  ∀ i p, promises !! i = Some p → promise_consistent promises p i.

Class genInG {n} (Σ : gFunctors) (A : cmra) (DS : deps n) := GenInG {
  genInG_id : gid Σ;
  genInG_apply := rFunctor_apply (gFunctors_lookup Σ genInG_id);
  (* genInG_gti : gen_trans_info Σ (genInG_id); *)
  (* genInG_gen_trans : Ω.(g_valid_gt) (genInG_id) = Some2 genInG_gti; *)
  (* genInG_gti_typ : A = genInG_gti.(gti_car); *)
  genInG_prf : A = genInG_apply (iPropO Σ) _;
  (* genInG_gen_trans2 : *)
  (*   genInG_gti.(gti_valid) = *)
  (*     (gen_transport (gen_cmra_eq genInG_gti_typ genInG_gti.(gti_look)) (lift g)); *)
}.

(* Knowledge that [A] is a resource, with the information about its dependencies
hidden in the dependent pair. *)
Class genInSelfG (Σ : gFunctors) (A : cmra) := GenInG2 {
  genInSelfG_n : nat;
  genInSelfG_DS : deps genInSelfG_n;
  genInSelfG_gen : genInG Σ A (genInSelfG_DS);
}.

Global Arguments genInG_id {_ _ _ _} _.

Global Program Instance genInG_inG {n} {DS : deps n} `{i : !genInG Σ A DS} :
      inG Σ (generational_cmraR A) :=
  {|
    inG_id := genInG_id i;
    inG_prf := genInG_prf; (* gen_cmra_eq genInG2_gti_typ genInG2_gti.(gti_look); *)
  |}.

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

(** The transformations [ts] satisfies the predicates [ps]. *)
Equations preds_hold_alt {n} {DS : deps n}
    (ts : trans_for_alt n DS) (ps : preds_for n DS) : Prop :=
  | hcons t ts', hcons p ps' := p t ∧ preds_hold_alt ts' ps' ;
  | hnil, hnil := True.
Global Transparent preds_hold_alt.

(** The transformations [ts] satisfies the predicates [ps]. *)
Equations preds_hold {n} {DS : deps n}
    (ts : trans_for n DS) (ps : preds_for n DS) : Prop :=
  | hcons t ts', hcons p ps' := p t ∧ preds_hold ts' ps' ;
  | hnil, hnil := True.
Global Transparent preds_hold.

Definition dummy_use_ing {n : nat} {DS : deps n} `{!genInG Σ A DS} := True.

Section rules.
  Context {n : nat} {DS : deps n} `{!genInG Σ A DS}.

  Definition gen_own (γ : gname) (a : A) : iProp Σ := own γ a.
    (* own γ (None, (None, None), Some a). *)

  (** Ownership over the token for [γ]. *)
  Definition token  (γ : gname) (γs : ivec n gname)
    (R : pred_over DS A) (P : (A → A) → Prop) : iProp Σ :=
    ⌜ dummy_use_ing ⌝.

  (** Knowledge that γ is accociated with the predicates R and P. *)
  Definition rely (γ : gname) (γs : ivec n gname)
    (R : pred_over DS A) (P : (A → A) → Prop) : iProp Σ :=
    ⌜ dummy_use_ing ⌝.

  Definition rely_self {B} `{i : !genInSelfG Σ B}
      (γ : gname) (P : (B → B) → Prop) : iProp Σ :=
    ⌜ True ⌝.

  Lemma own_gen_alloc (a : A) γs :
    ✓ a → ⊢ |==> ∃ γ, gen_own γ a ∗ token γ γs True_pred (λ _, True%type).
  Proof. Admitted.

  Definition trans_in {B} (γ : gname) (t : B → B) : iProp Σ :=
    ⌜ dummy_use_ing ⌝%I.

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
    token γ γs R P ⊢ token γ γs R P.
  Proof. Admitted.

  Lemma rely_nextgen γ γs (R : pred_over DS A) P :
    rely γ γs R P
    ⊢ rely γ γs R P ∗
      ∃ (t : A → A),
      ⌜ ∃ (ts : trans_for n DS),
        huncurry R ts t ∧ (* The transformations satisfy the promise. *)
        P t ⌝ ∗ (* For convenience we also get this directly. *)
      trans_in γ t ∗
      (∃  (ts' : trans_for_alt n DS), (* Temp universe workaround. *)
        (∀ (i : fin n), trans_in (γs !!! i) (hvec_lookup_fmap ts' i))).
  Proof. Admitted.

  Lemma token_to_rely γ γs (R : pred_over DS A) P :
    token γ γs R P ⊢ rely γ γs R P.
  Proof. Admitted.

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

    Definition TS : trans_for _ _ := [T1; T2].
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
