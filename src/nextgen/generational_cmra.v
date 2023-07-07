From iris.algebra Require Import functions gmap agree excl csum max_prefix_list.
From iris.algebra.lib Require Import mono_list.
From iris.proofmode Require Import classes tactics.

From self Require Import hvec extra cmra_morphism_extra gen_single_shot gen_pv.
From self.nextgen Require Import types.

Import EqNotations. (* Get the [rew] notation. *)

Local Infix "*R*" := prodR (at level 50, left associativity).

Section dependency_relation_cmra.
  Context {n : nat}.

  Canonical Structure pred_overO (A : cmra) :=
    leibnizO (pred_over A).
  Canonical Structure rel_overO (DS : ivec n cmra) (A : cmra) :=
    leibnizO (rel_over DS A).

End dependency_relation_cmra.

Definition generational_cmraR {n} (A : cmra) (DS : ivec n cmra) : cmra :=
  (* Agreement on transformation into generation *)
  optionR (agreeR (leibnizO (A → A))) *R*
  (* Facilitates choice of transformation out of generation *)
  GTSR (A → A) *R*
  (* Ownership over A *)
  optionR A *R*
  (* Gname of dependencies - we don't need to store their [gid] as that is static. *)
  optionR (agreeR (leibnizO (list gname))) *R*
  (* List of promised relations. *)
  gen_pvR (mono_listR (rel_overO DS A)) *R*
  (* List of promised predicates. *)
  gen_pvR (mono_listR (pred_overO A)).

Local Infix "*M*" := prod_map (at level 50, left associativity).

(* The generational transformation function for the encoding of each ownership
over a generational camera. *)
Definition gen_cmra_trans {n} {A : cmra} {DS : ivec n cmra}
    (f : A → A) : generational_cmraR A DS → generational_cmraR A DS :=
  (const (Some (to_agree f)) : _ → optionR (agreeR (leibnizO (A → A)))) *M*
  (GTS_floor : (GTSR (A → A)) → (GTSR (A → A))) *M*
  (fmap f : optionR A → optionR A) *M*
  id *M*
  gen_pv_trans *M*
  gen_pv_trans.

Section tuple_helpers.
  (* Working with the 6-tuple is sometimes annoying. These lemmas help. *)
  Context {A B C D E F : cmra}.
  Implicit Types (a : A) (b : B) (c : C) (d : D) (e : E) (f : F).

  Lemma prod_valid_1st {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    ✓ ((a1, b1, c1, d1, e1, f1) ⋅ (a2, b2, c2, d2, e2, f2)) ⊢@{iProp Σ} ✓ (a1 ⋅ a2).
  Proof. rewrite 5!prod_validI /= -4!assoc. iIntros "(? & ? & ? & ? & ? & ?)". done. Qed.

  Lemma prod_valid_2nd {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    ✓ ((a1, b1, c1, d1, e1, f1) ⋅ (a2, b2, c2, d2, e2, f2)) ⊢@{iProp Σ} ✓ (b1 ⋅ b2).
  Proof. rewrite 5!prod_validI /= -4!assoc. iIntros "(? & ? & ? & ? & ? & ?)". done. Qed.

  Lemma prod_valid_3th {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    ✓ ((a1, b1, c1, d1, e1, f1) ⋅ (a2, b2, c2, d2, e2, f2)) ⊢@{iProp Σ} ✓ (c1 ⋅ c2).
  Proof. rewrite 5!prod_validI /= -4!assoc. iIntros "(? & ? & ? & ? & ? & ?)". done. Qed.

  Lemma prod_valid_4th {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    ✓ ((a1, b1, c1, d1, e1, f1) ⋅ (a2, b2, c2, d2, e2, f2)) ⊢@{iProp Σ} ✓ (d1 ⋅ d2).
  Proof. rewrite 5!prod_validI /= -4!assoc. iIntros "(? & ? & ? & ? & ? & ?)". done. Qed.

  Lemma prod_valid_5th {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    ✓ ((a1, b1, c1, d1, e1, f1) ⋅ (a2, b2, c2, d2, e2, f2)) ⊢@{iProp Σ} ✓ (e1 ⋅ e2).
  Proof. rewrite 5!prod_validI /= -4!assoc. iIntros "(? & ? & ? & ? & ? & ?)". done. Qed.

  Lemma prod_valid_6th {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    ✓ ((a1, b1, c1, d1, e1, f1) ⋅ (a2, b2, c2, d2, e2, f2))
    ⊢@{iProp Σ} ✓ (f1 ⋅ f2).
  Proof. rewrite 5!prod_validI /= -4!assoc. iIntros "(? & ? & ? & ? & ? & ?)". done. Qed.

  Lemma prod_6_equiv a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    (a1, b1, c1, d1, e1, f1) ≡ (a2, b2, c2, d2, e2, f2)
    ↔ (a1 ≡ a2) ∧ (b1 ≡ b2) ∧ (c1 ≡ c2) ∧ (d1 ≡ d2) ∧ (e1 ≡ e2) ∧ (f1 ≡ f2).
  Proof.
    split.
    - intros (((((? & ?) & ?) & ?) & ?) & ?). done.
    - intros (? & ? & ? & ? & ? & ?). done.
  Qed.

  Lemma prod_6_equivI {Σ} a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    (a1, b1, c1, d1, e1, f1) ≡ (a2, b2, c2, d2, e2, f2)
    ⊣⊢@{iProp Σ} (a1 ≡ a2) ∧ (b1 ≡ b2) ∧ (c1 ≡ c2) ∧ (d1 ≡ d2) ∧ (e1 ≡ e2) ∧ (f1 ≡ f2).
  Proof. rewrite !prod_equivI. simpl. rewrite -4!assoc. done. Qed.

  Lemma pair_op_6 a1 b1 c1 d1 e1 f1 a2 b2 c2 d2 e2 f2 :
    (a1, b1, c1, d1, e1, f1) ⋅ (a2, b2, c2, d2, e2, f2) =
    (a1 ⋅ a2, b1 ⋅ b2, c1 ⋅ c2, d1 ⋅ d2, e1 ⋅ e2, f1 ⋅ f2).
  Proof. done. Qed.

End tuple_helpers.

Lemma own_gen_cmra_split {Σ}
    {A B C D E F : ucmra} `{!inG Σ (A *R* B *R* C *R* D *R* E *R* F)}
    γ a b c d e f :
  own γ (a, b, c, d, e, f) ⊣⊢
    own γ (a, ε, ε, ε, ε, ε) ∗
    own γ (ε, b, ε, ε, ε, ε) ∗
    own γ (ε, ε, c, ε, ε, ε) ∗
    own γ (ε, ε, ε, d, ε, ε) ∗
    own γ (ε, ε, ε, ε, e, ε) ∗
    own γ (ε, ε, ε, ε, ε, f).
 Proof.
   rewrite -5!own_op.
   f_equiv.
   (* NOTE: Doing the split before rewriting is, for some reason, much faster
    * than doing the rewrite without the split. *)
   repeat split; simpl;
     rewrite ?ucmra_unit_right_id; rewrite ?ucmra_unit_left_id; reflexivity.
Qed.

(* The lemma above somehow causes [Qed]s to be very slow, this variant seems
 * slightly better. *)
Lemma own_gen_cmra_split_alt {Σ} {n} (A : cmra) (DS : ivec n cmra)
    `{!inG Σ (generational_cmraR A DS)} γ a b c d e f :
  own γ (a, b, c, d, e, f) ⊢
    own γ (a, ε, ε, ε, ε, ε) ∗
    own γ (ε, b, ε, ε, ε, ε) ∗
    own γ (ε, ε, c, ε, ε, ε) ∗
    own γ (ε, ε, ε, d, ε, ε) ∗
    own γ (ε, ε, ε, ε, e, ε) ∗
    own γ (ε, ε, ε, ε, ε, f).
Proof. rewrite own_gen_cmra_split. done. Qed.

(* Constructors for each of the elements in the pair. *)

Definition gc_tup_pick_in {n A} (DS : ivec n cmra) pick_in : generational_cmraR A DS :=
 (Some (to_agree (pick_in)), ε, ε, ε, ε, ε).

Definition gc_tup_pick_out {A n} (DS : ivec n cmra) pick_out : generational_cmraR A DS :=
 (ε, pick_out, ε, ε, ε, ε).

Definition gc_tup_elem {A n} (DS : ivec n cmra) a : generational_cmraR A DS :=
 (ε, ε, Some a, ε, ε, ε).

Definition gc_tup_deps {n} A (DS : ivec n cmra) deps : generational_cmraR A DS :=
 (ε, ε, ε, Some (to_agree deps), ε, ε).

Definition gc_tup_promise_list {n A} {DS : ivec n cmra} l : generational_cmraR A DS :=
 (ε, ε, ε, ε, l, ε).

Definition gc_tup_rel_pred {n A} {DS : ivec n cmra} l1 l2 : generational_cmraR A DS :=
 (ε, ε, ε, ε, l1, l2).

Global Instance gen_trans_const {A : ofe} (a : A) :
  CmraMorphism (A := optionR (agreeR A)) (const (Some (to_agree a))).
Proof.
  split; first apply _.
  - done.
  - intros. simpl. rewrite (core_id). done.
  - intros ??. simpl.
    rewrite -Some_op.
    rewrite agree_idemp.
    done.
Qed.

Section gen_cmra.
  Context {n} {A : cmra} {DS : ivec n cmra}.
  Global Instance gen_generation_gen_trans (f : A → A)
    `{!Proper (equiv ==> equiv) f} :
    CmraMorphism f → CmraMorphism (gen_cmra_trans (DS := DS) f).
  Proof. apply _. Qed.

  Global Instance gen_generation_proper (f : A → A) :
    Proper ((≡) ==> (≡)) f →
    Proper ((≡) ==> (≡)) (gen_cmra_trans (DS := DS) f).
  Proof.
    intros ? [[??]?] [[??]?] [[??]?]. simpl in *.
    rewrite /gen_cmra_trans.
    solve_proper.
  Qed.

  Global Instance gen_generation_ne (f : A → A) :
    NonExpansive f →
    NonExpansive (gen_cmra_trans (DS := DS) f).
  Proof. solve_proper. Qed.

  Lemma gen_cmra_trans_apply f (a : generational_cmraR A DS) :
    (gen_cmra_trans f) a =
      (Some (to_agree f), GTS_floor a.1.1.1.1.2, f <$> a.1.1.1.2, a.1.1.2,
        gen_pv_trans a.1.2, gen_pv_trans a.2).
  Proof. done. Qed.

End gen_cmra.

Lemma generational_cmraR_transp {A1 A2 n1 n2} {DS1 : ivec n1 cmra} {DS2 : ivec n2 cmra}
    (eq_n : n1 = n2) :
  A1 = A2 →
  DS1 = rew <- eq_n in DS2 →
  generational_cmraR A1 DS1 = generational_cmraR A2 DS2.
Proof. revert eq_n. intros -> -> ->. done. Defined.

Lemma generational_cmraR_transp_refl {A n} {DS : ivec n cmra} :
  generational_cmraR_transp (A1 := A) (n1 := n) (DS1 := DS)
    eq_refl eq_refl eq_refl = eq_refl.
Proof. done. Qed.

