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

  (* [a] is both persisted and volatile. *)
  Definition gPV (a : A) : gen_pv A := (Some a, Some a).
  (* [a] is volatile. *)
  Definition gV (a : A) : gen_pv A := (None, Some a).
  (* [a] is persisted. *)
  Definition gP (a : A) : gen_pv A := (Some a, None).

End pv.
