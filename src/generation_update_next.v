From Equations Require Import Equations.

From iris.algebra Require Import functions gmap agree excl csum.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

From self Require Import extra basic_nextgen_modality.
From self Require Import hvec.

Import uPred.

(** Data describing the cameras that a given camera depends on. *)
Definition deps n := ivec cmra n.
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
Notation preds_for := (hvec cmra_to_pred).

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
    promise_RAs : ivec (gid Σ) promise_n;
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

Class genInG {n} (Σ : gFunctors) (A : cmra) (DS : deps n)
    := GenInG2 {
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

Section rules.
  Context `{Σ : gFunctors}.

  Definition gen_own `{!inG Σ (generational_cmraR A)}
      (γ : gname) (a : A) : iProp Σ :=
    own γ a.
    (* own γ (None, (None, None), Some a). *)

  (** Ownership over the token for [γ]. *)
  Definition token {n} {DS : deps n} `{i : !genInG Σ A DS} (γ : gname) (γs : list gname)
    (R : pred_over DS A) (P : (A → A) → Prop) : iProp Σ :=
    ⌜ True ⌝.

  (** Knowledge that γ is accociated with the predicates R and P. *)
  Definition rely {n} {DS : deps n} `{i : !genInG Σ A DS} (γ : gname) (γs : list gname)
    (R : pred_over DS A) (P : (A → A) → Prop) : iProp Σ :=
    ⌜ True ⌝.

  (* FIXME: Since the definition will use [own] we need some instance involving
  Σ. But, we would like for it to not mention [DS]. Figure this out later. *)
  Definition rely_self {n} {DS : deps n} `{i : !genInG Σ A DS} (γ : gname) (P : (A → A) → Prop) : iProp Σ :=
    ⌜ True ⌝.

  Global Arguments token {_ _ _ _} _ _ _%type _%type.

  Lemma own_gen_alloc {n} {DS : deps n} `{!genInG Σ A DS} (a : A) γs :
    ✓ a → ⊢ |==> ∃ γ, gen_own γ a ∗ token γ γs True_pred (λ _, True%type).
  Proof. Admitted.

  (** The transformations [ts] satisfies the predicates [ps]. *)
  Equations preds_hold {n} {DS : deps n} (ts : trans_for n DS) (ps : preds_for n DS) : Prop :=
    | hcons t ts', hcons p ps' := p t ∧ preds_hold ts' ps' ;
    | hnil, hnil := True.
  Global Transparent preds_hold.

  (* genInG Σ (ivec_lookup_total DS i) DS2 *)

  (* Lemma fooo {Σ} {n} DS DS2 i : *)
  (*   (∀ (i2 : fin n), *)
  (*     genInG Σ (ivec_lookup_total DS i2) (ivec_lookup_total DS2 i2)) → *)
  (*   genInG Σ (ivec_lookup_total DS i) DS2. *)

  (** Strengthen a promise. *)
  Lemma token_strengthen_promise {n} {DS : deps n} `{!genInG Σ A DS} γ γs (deps_preds : preds_for n DS)
      (R_1 R_2 : pred_over DS A) (P_1 P_2 : (A → A) → Prop) :
    (* The new relation is stronger. *)
    (∀ (ts : trans_for n DS) (t : A → A), huncurry R_1 ts t → huncurry R_2 ts t ∧ P_2 t) →
    (* The new predicate is stronger. *)
    (∀ t, P_1 t → P_2 t) →
    (* The new relation implies the predicate. *)
    (∀ ts t, huncurry R_2 ts t → P_2 t) →
    (* Evidence that the promise is realizeable. *)
    (∀ (ts : trans_for n DS),
       preds_hold ts deps_preds → ∃ (e : A → A), (huncurry R_2) ts e) →
    (* For every dependency we own a [rely_self]. *)
    (∀ (i : fin (ilen DS)), ∃ γ, rely_self γ (deps_preds 👀 i)) -∗
    token γ γs R_1 P_1 -∗
    token γ γs R_2 P_2.
  Proof.
  Admitted.


End rules.

Section test.
  Context `{max_i : !inG Σ max_natR}.
  Context `{i : !genInG Σ max_natR (icons max_natR (icons max_natR inil))}.

  Definition a_rely :=
    rely (1%positive) [] (λ Ta Tb Ts, Ta = Ts ∧ Tb = Ts) (λ _, True).

  Section test.
    Variables (A : cmra) (B : cmra) (T1 : A → A) (T2 : B → B)
      (P1 : (A → A) → Prop) (P2 : (B → B) → Prop).

    Definition TS : trans_for _ := hcons T1 (hcons T2 hnil).
    Definition PS : preds_for _ := hcons P1 (hcons P2 hnil).
    Compute (preds_hold (DS := [A; B]) TS PS).

    Context `{!genInG Σ A [A; B]%IL}.

    Lemma foo (γ : gname) (γs : list gname) : True.
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
