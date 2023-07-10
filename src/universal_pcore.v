From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import csum excl auth dfrac.
From iris.algebra Require Import csum excl auth dfrac.

(** A good core is one that returns the largest local unit. *)
Definition pcore_good (A : cmra) :=
  ∀ (a : A),
    (pcore a = None ∧ (∀ a', ✓ (a ⋅ a') → a ⋅ a' ≢ a)) ∨
    (∀ pa, pcore a = Some pa →
      (∀ a', a ⋅ a' ≡ a → a' ≡ pa ∨ a' ≼ pa)).

Lemma qp_add_neq q p : (q + p ≠ q)%Qp.
Proof.
  intros Heq. eapply (Qp.not_add_le_l q p). rewrite Heq //.
Qed.

Lemma dfrac_pcore_good : pcore_good dfrac.
Proof.
  intros [?| |?]; simpl.
  - left. split; first done.
    intros [?| |?] ?; try done.
    rewrite dfrac_op_own.
    intros [= ?%qp_add_neq ]. done.
  - right. intros ?. inversion 1.
    intros [?| |?]; try done. intros ?. left. done.
  - right. intros ?. inversion 1.
    intros [?| |?]; try naive_solver.
    + inversion 1. apply qp_add_neq in H3. done.
    + inversion 1. apply qp_add_neq in H3. done.
Qed.

Lemma excl_pcore_good {A} : pcore_good (exclR A).
Proof.
  intros [?|]; (left; split; first done).
  - intros [?|] ?; inversion 1.
  - intros [?|]; inversion 1.
Qed.

(** A good cmra is one where every element has either no local unit or one
 * greates local unit. *)
Definition good_cmra (A : cmra) : Prop :=
  ∀ (a : A) (au1 au2 : A),
    a ⋅ au1 ≡ a → a ⋅ au2 ≡ a → (* [au1] and [au2] are two local units *)
    (au1 ≡ au2 ∨ au1 ≼ au2 ∨ au2 ≼ au1).

Definition good_computable_cmra (A : cmra) : Type :=
  ∀ (a : A),
  (* [a] has one largest local unit *)
  {pa : A |
    ✓ (a ⋅ pa) ∧ a ⋅ pa = a ∧
    ∀ pa', ✓ (a ⋅ pa') → a ⋅ pa' ≢ a → pa = pa' ∨ pa' ≼ pa
  } +
  (* [a] has no local unit *)
  {∀ a', ✓ (a ⋅ a') → a ⋅ a' ≢ a}.
