From Equations Require Import Equations.

From iris.algebra Require Import functions gmap agree excl csum.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

From self Require Import extra.
From self Require Import generational_update.
From self Require Import hvec.
Import uPred.

Equations test_equations (l : hvec (icons nat (icons bool inil))) : nat :=
  test_equations (hcons x xs) := x.

(*
(* Putting a [cmra] inside a [list] gives a universe error so we define our own
list to workaround this. *)
Inductive ilist (A : Type) : Type :=
 | inil : ilist A
 | icons : A -> ilist A -> ilist A.

Arguments inil {A}.
Arguments icons {A} a l.

Declare Scope list2_scope.
Bind Scope list2_scope with ilist.
Delimit Scope list2_scope with L2.

Global Notation "[ ] " := inil : list2_scope.
Global Notation "[ x ] " := (icons x inil) : list2_scope.
Global Notation "[ x ; .. ; y ] " := (icons x .. (icons y inil) ..) : list2_scope.

Fixpoint ilen {A} (l : ilist A) : nat :=
  match l with inil => 0 | icons _ l2 => S (ilen l2) end.

Fixpoint list2_to_list {A} (l : ilist A) : list A :=
  match l with inil => nil | icons t ts => cons t (list2_to_list ts) end.

Fixpoint list2_to_tlist (l : ilist Type) : tlist :=
  match l with inil => inil | icons t ts => icons t (list2_to_tlist ts) end.

Fixpoint list2_to_vec {A} (l : ilist A) : vec A (ilen l) :=
  match l as l' return vec A (ilen l') with
    | inil => [#]
    | icons t tail => t ::: list2_to_vec tail
  end.
*)

(*
Fixpoint tlist_lookup_fin (As : tlist) : fin (tlen As) → Type :=
  match As return fin (tlen As) → Type with
  | inil => λ i, fin_zero i
  | icons t ts => λ i,
      match i with
      | 0%fin => λ _, t
      | FS i' =>  λ f, f i'
      end (tlist_lookup_fin ts)
  end.

SFV: Could not get this variant using [fin] and [tlist_lookup_fin] to work.
Infix "👀" := tlist_lookup_fin (at level 20).

Definition tlist_lookup_vec {As : tlist} (l : hvec As) :
    ∀ (i : fin (tlen As)), tlist_to_vec As !!! i.
  match l in hvec As return (∀ (i : fin (tlen As)), As 👀 i) with
  | hnil => λ i, fin_zero i
  | @hcons A As' x xs => λ i : fin (tlen (icons A As')),
      (* match i in fin (S l) return ∀ v : vec Type l, vector_lookup_total _ _ i v with *)
      (* match i return tlist_to_vec (icons (thead As) (ttail As)) !!! i with *)
      (* match i in fin l return (match l with 0 => (unit : Type) | S t => (tlist_to_vec (icons A As')) !!! i end) with *)
      (* | 0%fin => λ _, x *)
      (* | FS _ => λ _, _ *)
      (* end (tlist_to_vec (icons A As')) *)
      (* match i in fin l return ∀ vec : vec Type l, (match l with 0 => (unit : Type) | S t => vec !!! i end) with *)
      (* match *)
      (*   i as i0 in (fin n) *)
      (*   return *)
      (*     (match n as x0 return Type with *)
      (*     | 0 => IDProp *)
      (*     | S t => tlist_to_vec (icons A As') !!! i *)
      (*     end) with *)
        let f := hlist_lookup_fin As' xs
        in _
      (* match i as i0 in (fin n) return ∀ (As' : tlist), (∀ (i : fin (pred n)), As' 👀 i) → ((icons A As') 👀 i0) with *)
      (* (* match i with *) *)
      (* | 0%fin => λ _, x *)
      (* | FS i' => λ f, f i' *)
      (* end As' (hlist_lookup As' xs) *)
  end.
*)

(** A telescope inspired notation for [himpl]. *)
Notation "As -h> B" :=
  (himpl As B) (at level 99, B at level 200, right associativity).

(** Data describing the cameras that a given camera depends on. *)
Definition deps := ilist cmra.
Bind Scope ilist_scope with deps.

Notation T Σ i := (R Σ i → R Σ i).

Record promise {Σ} := MkPromise {
    promise_g : gname; (* Ghost name for the promise. *)
    promise_i : gid Σ; (* The index of the RA in the global RA. *)
    promise_deps : list nat; (* Indices in the list of promises of the dependencies. *)
    promise_RAs : list (gid Σ);
    (* The predicate that relates our transformation to those of the dependencies. *)
    (* promise_rel : *)
    (*   list_to_tele ((λ (i : gid Σ), T Σ i : Type) <$> promise_RAs) → T Σ promise_i → Prop; *)
    promise_pred : T Σ promise_i → Prop;
    (* rel_impl_pred : ; *)
    (* deps_preds : foo; *)
    (* witness : foo; *)
}.

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

Class genInG2 (Σ : gFunctors) (A : cmra) (DS : deps)
    := GenInG2 {
  genInG2_id : gid Σ;
  genInG2_apply := rFunctor_apply (gFunctors_lookup Σ genInG2_id);
  genInG2_gti : gen_trans_info Σ (genInG2_id);
  (* genInG_gen_trans : Ω.(g_valid_gt) (genInG_id) = Some2 genInG_gti; *)
  genInG2_gti_typ : A = genInG2_gti.(gti_car);
  (* genInG_gen_trans2 : *)
  (*   genInG_gti.(gti_valid) = *)
  (*     (gen_transport (gen_cmra_eq genInG_gti_typ genInG_gti.(gti_look)) (lift g)); *)
}.

Global Arguments genInG2_id {_} {_} {_} _.

Global Program Instance genInG2_inG `{i : !genInG2 Σ A D} :
      inG Σ (generational_cmraR A) :=
  {|
    inG_id := genInG2_id i;
    inG_prf := gen_cmra_eq genInG2_gti_typ genInG2_gti.(gti_look);
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

(* (P : (i : fin n) → T i → Prop) *)

(* Definition hlist_to_prod {l : tlist} (v : hvec l) : *)
(*     ∀ (i : fin (tlen l)), (hlist_to_vec v !!! i). *) (* hlist_to_vec makes no sense *)

Section test.
  (* Context `{!inG Σ test_A_R}. *)
  (* Context `{!inG Σ test_B_R}. *)
  Context `{max_i : !inG Σ max_natR}.
  Context `{i : !genInG2 Σ max_natR (icons max_natR (icons max_natR inil))}.

  Definition deps_to_trans (DS : ilist cmra) : ilist Type :=
    ilist_fmap (λ A, cmra_car A → cmra_car A) DS.

  (** Converts a list of cameras into a tlist of predicates over their carries. *)
  (* Definition deps_to_trans (DS : ilist cmra) := deps_to_trans DS. *)

  (** Ownership over the token for [γ]. *)
  Definition token `{i : !genInG2 Σ A DS} (γ : gname) (γs : list gname)
    (R : (deps_to_trans DS) -h> (A → A) → Prop) (P : (A → A) → Prop) : iProp Σ :=
    ⌜ True ⌝.

  Global Arguments token {_ _ _} _ _ _%type _%type.

  (** Knowledge that γ is accociated with the predicates R and P. *)
  Definition rely `{i : !genInG2 Σ A DS} (γ : gname) (γs : list gname)
    (R : deps_to_trans DS -h> (A → A) → Prop) (P : (A → A) → Prop) : iProp Σ :=
    ⌜ True ⌝.

  (* FIXME: Since the definition will use [own] we need some instance involving
  Σ. But, we would like for it to not mention [DS]. Figure this out later. *)
  Definition rely_self {A} (* `{i : !genInG2 Σ A DS} *) (γ : gname) (P : (A → A) → Prop) : iProp Σ :=
    ⌜ True ⌝.

  Definition trans (A : Type) := A → A.

  Definition a_rel (Ta : max_natR → max_natR) Tb Ts :=
    Ta = Ts ∧ Tb = Ts.

  Definition a_rely :=
    rely (1%positive) [] (λ Ta Tb Ts, Ta = Ts ∧ Tb = Ts) (λ _, True).

  Definition True_pred {TT : ilist Type} {A : Type} :=
    hcurry (As := TT) (λ _ (_ : A), True).

  Lemma own_gen_alloc2 `{!genInG2 Σ A DS} (a : A) γs :
    ✓ a → ⊢ |==> ∃ γ, gen_own γ a ∗ token γ γs True_pred (λ _, True%type).
  Proof. Admitted.

  (* For a list of types [list Type] we need a list of an element of every type. *)
  (* Definition trans_for_map (DS : ilist cmra) : Type := *)
  (*   ∀ (i : fin (ilen DS)), trans (cmra_car $ list2_to_vec DS !!! i). *)

  (* Definition map_to_list {DS} (preds : trans_for_map DS) := *)
  (*   (λ i, preds i) <$> finite.fin_enum (ilen DS). *)

  (* Fixpoint own_rely_self_for_deps_2 (DS : ilist cmra) (ts : preds_for DS) : iProp Σ := *)
  (*   match ts with *)
  (*   | hnil => True%I *)
  (*   | hcons a xs => (∃ γ, rely_self γ a) ∗ own_rely_self_for_deps_2 xs *)
  (*   end. *)
  (*   (* ∀ (i : fin (ilen DS)), ∃ γ, rely_self γ (ts i). *) *)

  (* For a list of types [list Type] we need a list of an element of every type. *)
  Definition trans_for (DS : ilist cmra) : Type :=
    hvec (deps_to_trans DS).

  Definition pred_over (DS : deps) (A : cmra) :=
    deps_to_trans DS -h> (A → A) → Prop.

  (* This results in the type:
     [(max_nat → max_nat) → (excl () → excl ()) → (nat → nat) → Prop] *)
  Compute (pred_over [max_natR; exclR unitO] natR).

  Definition preds_for (DS : ilist cmra) : Type :=
    hvec $ (ilist_fmap (λ A, (trans (cmra_car A) → Prop)) DS).

  (* Given a list of cameras return a type whose elements contain a predicate
  over transformation functions for each camera in the list. We represent all of
  these predicates as a dependent function as this encoding makes it possible to
  lookup specific predicates which is used in [own_rely_self_for_deps]. *)
  Definition preds_for_map (DS : deps) : Type :=
    ∀ (i : fin (ilen DS)), (trans (cmra_car $ ilist_to_vec DS !!! i)) → Prop.

  Definition own_rely_self_for_deps (DS : ilist cmra) (ts : preds_for_map DS) : iProp Σ :=
    ∀ (i : fin (ilen DS)), ∃ γ, rely_self γ (ts i).

  (** The transformations [ts] satisfies the predicates [ps]. *)
  Equations preds_hold {DS}
    (ts : hvec (ilist_fmap (λ A, cmra_car A → cmra_car A) DS))
    (ps : hvec $ (ilist_fmap (λ A, (trans (cmra_car A) → Prop)) DS)) : Prop :=
    @preds_hold (icons ty tys) (hcons t ts') (hcons p ps') := p t ∧ preds_hold ts' ps' ;
    @preds_hold _ _ _ := True.
  Global Transparent preds_hold.

  Section test.
    Variables (A : cmra) (B : cmra) (T1 : A → A) (T2 : B → B)
      (P1 : (A → A) → Prop) (P2 : (B → B) → Prop).

    Definition TS := hcons T1 (hcons T2 hnil).
    Definition PS := hcons P1 (hcons P2 hnil).
    Compute (preds_hold (DS := [A; B]) TS PS).

  End test.

    (* | hnil, hcons p ps := True *)
    (* | hcons t ts, hnil := True *)
    (* | hnil, hnil := True. *)
    (* | hnil, hnil := True. *)
  (* Definition preds_hold_hlist {DS} : trans_for DS → preds_for DS → Prop := *)
  (*   match DS with *)
  (*   | inil => λ _ _, True *)
  (*   | icons c ds => λ trans, *)
  (*       match trans in hvec TS return *)
  (*             match TS with *)
  (*               inil => Prop *)
  (*             | icons T TS' => (hvec (icons ) → Prop end) with *)
  (*       | hnil => True *)
  (*       | hcons t ts => _ *)
  (*       end *)
  (*     (* match trans with *) *)
  (*     (* | hnil => True *) *)
  (*     (* | hcons t ts => *) *)
  (*     (*     match preds with *) *)
  (*     (*     | hnil => True *) *)
  (*     (*     | hcons p ps => _ *) *)
  (*     (*     end *) *)
  (*     (* end *) *)
  (*   end. *)
  (* match trans with *)
  (* | hnil => True *)
  (* | hcons t ts => *)
  (*     match preds with *)
  (*     | hnil => True *)
  (*     | hcons p ps => _ *)
  (*     end *)
  (* end. *)

  (** Strengthen a promise. *)
  Lemma token_strengthen_promise `{!genInG2 Σ A DS} γ γs (deps_preds : preds_for DS)
      (R_1 R_2 : pred_over DS A) (P_1 P_2 : (A → A) → Prop) :
    (* The new relation is stronger. *)
    (∀ (ts : hvec (deps_to_trans DS)) (t : A → A), huncurry R_1 ts t → huncurry R_2 ts t ∧ P_2 t) →
    (* The new predicate is stronger. *)
    (∀ t, P_1 t → P_2 t) →
    (* The new relation implies the predicate. *)
    (∀ ts t, huncurry R_2 ts t → P_2 t) →
    (* Evidence that the promise is realizeable. *)
    (∀ (ts : hvec (deps_to_trans DS)),
       preds_hold ts deps_preds → ∃ (e : A → A), (huncurry R_2) ts e) →
    (* For every dependency we own a [rely_self]. *)
    (* own_rely_self_for_deps DS deps_preds -∗ *)
    token γ γs R_1 P_1 -∗
    token γ γs R_2 P_2.
  Proof.
  Admitted.

  (* Compute (token_strengthen_promise (DS := [max_natR; exclR unitO]) (1%positive) []). *)

  (* Program Definition transport_rel_3 {M1 M2 : cmra} (eq : M1 = M2) *)
  (*   (rel : (M1 → M1) → (M1 → M1) → (M1 → M1) → Prop) : *)
  (*   (M2 → M2) → (M2 → M2) → (M2 → M2) → Prop. *)
  (* Proof. rewrite eq in rel. done. Qed. *)

  (* Definition a_promise := *)
  (*   {| *)
  (*     promise_g := 1%positive; *)
  (*     promise_i := inG_id max_i; *)
  (*     promise_deps := [0; 1]; *)
  (*     promise_RAs := [inG_id max_i; inG_id max_i]; *)
  (*     promise_rel := tele_app (transport_rel_3 inG_prf a_rel); *)
  (*     promise_pred := λ _, True; *)
  (*   |}. *)

  (* Definition my_tele := [tele (x : nat) (y : nat) (z : nat)]. *)
  (* Definition ff : my_tele -t> nat := (λ x y z, (x + y + z)%nat). *)
  (* Definition ff_alt : nat → nat → nat → nat := (λ x y z, (x + y + z)%nat). *)
  (* Definition test := tele_app (TT := my_tele) ff. *)

  (* Definition my_tele_2 := list_to_tele [(nat : Type); (nat : Type); (nat : Type)]. *)

  (* Compute tele_fun [tele (a : nat) (b : Z)] bool. *)
  (* Lemma tt_ff : my_tele -t> nat = nat → nat → nat → nat. *)
  (* Proof. simpl. done. Qed. *)

End test.
