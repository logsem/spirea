From Equations Require Import Equations.

From iris.algebra Require Import numbers excl.
From iris.base_logic.lib Require Export iprop own.

From self Require Import extra hvec.
From self.high Require Import increasing_map.

Import EqNotations. (* Get the [rew] notation. *)
Import uPred.
#[global] Instance eqdecision_eqdec a : EqDecision a → EqDec a.
Proof. done. Qed.

Section types.

  (** A transformation over the carrier of the camera [A]. *)
  Definition cmra_to_trans A := cmra_car A → cmra_car A.

  (** A predicate over a transformation over [A]. *)
  Definition pred_over A := (cmra_to_trans A) → Prop.

  (** Relation that is always true. *)
  Definition True_pred {A} : pred_over A := λ _, True.

  (* Definition rel_over_typ {n} (DS : ivec n Type) (A : Type) := *)
  (*   iimpl id ((λ a, a → a) <$> DS) ((A → A) → Prop). *)

  (* (* An example to demonstrate [rel_over_typ]. This results in the type: *)
  (*    [(bool → bool) → (() → ()) → (nat → nat) → Prop] *) *)
  (* Compute (rel_over_typ [bool : Type; unit : Type] nat). *)

  (** A relation over transformations between the cameras in [DS and [A]. *)
  Definition rel_over {n} (DS : ivec n cmra) (A : cmra) :=
    iimpl (cmra_to_trans <$> DS) ((A → A) → Prop).

  (* An example to demonstrate [rel_over]. This results in the type:
     [(max_nat → max_nat) → (excl () → excl ()) → (nat → nat) → Prop] *)
  Compute (rel_over [max_natR; exclR unitO] natR).

  (** Relation that is always true. *)
  Definition True_rel {n} {DS : ivec n cmra} {A} : rel_over DS A :=
    hcurry (λ _ _, True).

  Definition trans_for n (DS : ivec n cmra) := hvec n (cmra_to_trans <$> DS).

  (* Test that [trans_for] does not give universe issue. *)
  #[local]
  Definition test_exist {Σ} {n : nat} {DS : ivec n cmra} : iProp Σ :=
    ∃ (ts : trans_for n DS), ⌜ True ⌝.

  (* Notation trans_for_old := (hvec cmra_to_trans). *)

  (* trans_for_old _does_ give universe issue. The root cause is the way the
   * [cmra] appears in the type. In [trans_for] the occurence of [cmra_car]
   * prevents the universe issue somehow. *)
  (* Definition test_exist {Σ} {n : nat} {DS : ivec cmra n} : iProp Σ := *)
  (*   ∃ (ts : trans_for n DS), ⌜ True ⌝. *)

End types.

#[global]
Notation preds_for n ls := (hvec n (pred_over <$> ls)).

#[global]
(* The functor in [Σ] at index [i] applied to [iProp]. *)
Notation R Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPropO Σ)).

(* The functor in [Σ] at index [i] applied to [iPreProp]. *)
#[global]
Notation Rpre Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ)).

#[global]
Notation T Σ i := (R Σ i → R Σ i).

Section dependency_relation_extra.
  Context {n} {A : cmra} {DS : ivec n cmra}.
  Implicit Types (R : rel_over DS A) (P : (A → A) → Prop).

  Definition rel_stronger (R1 R2 : rel_over DS A) :=
    ∀ (ts : trans_for n DS) (t : A → A),
      huncurry R1 ts t → huncurry R2 ts t.

  #[global]
  Instance rel_stronger_preorder : PreOrder rel_stronger.
  Proof.
    split.
    - intros ??. naive_solver.
    - intros ???????. naive_solver.
  Qed.

  Definition rel_weaker := flip rel_stronger.

  Lemma rel_weaker_stronger R1 R2 : rel_stronger R1 R2 ↔ rel_weaker R2 R1.
  Proof. done. Qed.

  #[global]
  Instance rel_weaker_preorder : PreOrder rel_weaker.
  Proof. unfold rel_weaker. apply _. Qed.

  Definition pred_stronger (P1 P2 : (A → A) → Prop) :=
    ∀ (t : A → A), P1 t → P2 t.

  #[global]
  Instance pred_stronger_preorder : PreOrder pred_stronger.
  Proof.
    split.
    - intros ??. naive_solver.
    - intros ???????. naive_solver.
  Qed.

  Definition pred_weaker := flip pred_stronger.

  #[global]
  Instance pred_weaker_preorder : PreOrder pred_weaker.
  Proof. unfold pred_weaker. apply _. Qed.

  Lemma pred_weaker_stronger P1 P2 : pred_stronger P1 P2 ↔ pred_weaker P2 P1.
  Proof. done. Qed.

  Lemma pred_stronger_trans (P1 P2 P3 : (A → A) → Prop) :
    pred_stronger P1 P2 → pred_stronger P2 P3 → pred_stronger P1 P3.
  Proof. intros S1 S2 ? ?. apply S2. apply S1. done. Qed.

  Definition rel_implies_pred R P : Prop :=
    ∀ (ts : trans_for n DS) (t : A → A), huncurry R ts t → P t.

  (* Notation preds_for n ls := (hvec pred_over n ls). *)

  (* TODO: Delete this probably. *)
  Definition rel_prefix_list_for {A} rel (all : list A) e :=
    (* The given promise [R] is the last promise out of all promises. *)
    last all = Some e ∧
    (* The list of promises increases in strength. *)
    increasing_list rel all.

  Definition pred_prefix_list_for' (rels : list (rel_over DS A)) preds R P :=
    length rels = length preds ∧
    rel_prefix_list_for rel_weaker rels R ∧
    rel_prefix_list_for pred_weaker preds P ∧
    rel_implies_pred R P.

  Lemma pred_prefix_list_for'_singl R P :
    rel_implies_pred R P →
    pred_prefix_list_for' (R :: []) (P :: []) R P.
  Proof.
    rewrite /pred_prefix_list_for'.
    rewrite /rel_prefix_list_for.
    intros ?. split_and!; eauto using increasing_list_singleton.
  Qed.

  Lemma pred_prefix_list_for'_True :
    pred_prefix_list_for' (True_rel :: []) (True_pred :: []) True_rel True_pred.
  Proof. apply pred_prefix_list_for'_singl. done. Qed.

  Lemma pred_prefix_list_for'_grow rels preds P_1 R_1 R_2 P_2 :
    rel_implies_pred R_2 P_2 →
    rel_weaker R_1 R_2 →
    pred_weaker P_1 P_2 →
    pred_prefix_list_for' rels preds R_1 P_1 →
    pred_prefix_list_for' (rels ++ (R_2 :: nil)) (preds ++ (P_2 :: nil)) R_2 P_2.
  Proof.
    rewrite /pred_prefix_list_for'. rewrite /rel_prefix_list_for.
    rewrite !app_length.
    intros ??? (-> & [??] & [??] & ?).
    rewrite !last_snoc.
    split_and!; try done; eapply increasing_list_snoc; done.
  Qed.

  Lemma pred_prefix_list_for_prefix_of {B} (Rel : relation B) `{!PreOrder Rel}
      (Rs1 Rs2 : list B) e e2:
    rel_prefix_list_for Rel Rs1 e →
    rel_prefix_list_for Rel Rs2 e2 →
    Rs1 `prefix_of` Rs2 →
    Rel e e2.
  Proof.
    intros PP1 PP2 pref.
    destruct PP1 as [isLast1 _].
    destruct PP2 as [isLast2 weaker].
    rewrite last_lookup in isLast1.
    eapply prefix_lookup_Some in isLast1; last done.
    apply: increasing_list_last_greatest; done.
  Qed.

End dependency_relation_extra.

Definition path_different {A} (id1 : A) (γ1 : gname) id2 γ2 :=
  id1 ≠ id2 ∨ γ1 ≠ γ2.

Section path_different.
  Implicit Types (γ : gname).

  Lemma path_equal_or_different {n} (id1 id2 : fin n) (γ1 γ2 : gname) :
    id1 = id2 ∧ γ1 = γ2 ∨ (path_different id1 γ1 id2 γ2).
  Proof.
    unfold path_different.
    destruct (decide (id1 = id2)) as [eq|?]; last naive_solver.
    destruct (decide (γ1 = γ2)) as [eq2|?]; last naive_solver.
    left. naive_solver.
  Qed.

  Lemma path_different_sym {A} (id1 : A) γ1 id2 γ2 :
    path_different id1 γ1 id2 γ2 ↔ path_different id2 γ2 id1 γ1.
  Proof. unfold path_different. naive_solver. Qed.

End path_different.
