From iris.proofmode Require Import tactics.
(* From iris.program_logic Require Export weakestpre. *)

(* -From self.lang Require Export notation primitive_laws lang class_instances proofmode. *)
(* -From self Require Import dprop view lang. *)

From self.lang Require Export notation.
From self.base Require Export primitive_laws.
From self.lang Require Export lang.
From self.base Require Export class_instances proofmode.
From self.high Require Import dprop.

(* -From self Require Import dprop view lang. *)
From self.lang Require Export notation lang.
From self.algebra Require Import view.
From self.base Require Export primitive_laws class_instances proofmode.
From self.high Require Import dprop.
From self Require Export weakestpre.

Definition prog : expr := let: "l" := ref #1 in ! "l".

Definition pure : expr :=
  let: "a" := #1 in
  let: "b" := #7 in
  "a" + "b".

Section specs.
  Context `{!nvmG Σ, !wpnvmG Σ}.

  Lemma wp_bin_op : ⊢ WP (#1 + #2) {{ v, ⌜1 = 1⌝ }}.
  Proof.
    wp_pures.
    done.
  Qed.

  Lemma wp_with_let :
    {{{ True }}} pure {{{ RET (#8); True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    rewrite /pure.
    wp_pures.
    iModIntro.
    iApply "Post".
    done.
  Qed.

End specs.

Section simple_increment.
  Context `{!nvmG Σ}.

End simple_increment.
