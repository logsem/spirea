(* For a camera [A] the camera [gen_pv A] contains two elements of [A]. The
first element is called "persistent" and it is carried through into the next
generation. The second element is called "volatile" and is discarded going into
the next generation.

The construction uses a product and an option. The option serves to force the
core to be a totalt function. Otherwise the generational transformation would
not commute with the core for an element [(a_p, a_v)] where the core is defined
for [a_p] but not for [a_v]. *)

From iris.algebra Require Import cmra.

From self Require Import gen_trans.

Definition gen_pv (A : cmra) : Type := option A * option A.
Definition gen_pvR (A : cmra) : cmra := prodR (optionR A) (optionR A).
Definition gen_pvUR (A : ucmra) : cmra := prodUR (optionUR A) (optionUR A).

Definition gen_pv_trans {A : cmra} (p : gen_pv A) : gen_pv A :=
  match p with (a_p, a_v) => (a_p, a_v) end.

#[global]
Instance gen_pv_trans_gentrans A : GenTrans (gen_pv_trans (A := A)).
Proof.
  split.
  - intros n [??] [??]. solve_proper.
  - intros ? [??] [??]. done.
  - intros [??]. done.
  - intros [??] [??]. done.
Qed.

Section pv.
  Context `{A : cmra}.
  Implicit Type (a : A).

  Inductive pv_stat := sP | sPV | sV.

  Definition mk_gen_pv (p : pv_stat) a :=
    match p with
      | sV => (None, Some a)
      | sP => (Some a, None)
      | sPV => (Some a, Some a)
    end.

  (* [a] is both persisted and volatile. *)
  Definition gPV (a : A) : gen_pv A := mk_gen_pv sPV a.
  (* [a] is volatile. *)
  Definition gV (a : A) : gen_pv A := mk_gen_pv sV a.
  (* [a] is persisted. *)
  Definition gP (a : A) : gen_pv A := mk_gen_pv sP a.

  Lemma gen_pv_valid p a : ✓ (mk_gen_pv p a) ↔ ✓ a.
  Proof.
    destruct p; rewrite pair_valid Some_valid; naive_solver.
  Qed.

  Lemma gen_pv_op p a1 a2 :
    (mk_gen_pv p a1) ⋅ (mk_gen_pv p a2) ≡ mk_gen_pv p (a1 ⋅ a2).
  Proof. destruct p; done. Qed.

  (* As long as one status is [PV] the operation guarantees validity of the composition of two elements. *)
  Lemma gen_pv_op_valid p a1 a2 :
    ✓ ((gPV a1) ⋅ (mk_gen_pv p a2)) ↔ ✓ (a1 ⋅ a2).
  Proof.
    destruct p; rewrite pair_valid Some_valid; split; try naive_solver; simpl.
    - intros V. split; first done. apply cmra_valid_op_l in V. done.
    - intros V. split; last done. eapply cmra_valid_op_l. done.
  Qed.

End pv.
