From iris.proofmode Require Import tactics.
(* From iris.program_logic Require Export weakestpre. *)
From self.lang Require Export notation primitive_laws lang class_instances proofmode.
From self Require Import vprop view lang.
From self Require Export weakestpre.

Definition prog : expr := let: "l" := ref #1 in ! "l".

Definition pure : expr :=
  let: "a" := #1 in
  let: "b" := #7 in
  "a" + "b".

Section specs.
  Context `{!nvmG Σ}.

  Lemma wp_bin_op : ⊢ WP (#1 + #2) {{ v, True }}.
  Proof.
    wp_pures.
    done.
  Qed.

  Lemma wp_pure :
    {{{ True }}} pure {{{ RET (#8); True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    rewrite /pure.
    wp_pures.
    wp_pure _.
  Admitted.

  Lemma wp_pure TV :
    {{{ True }}}
      (ThreadState pure TV)
    {{{ RET (ThreadVal (#8) TV); True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    wp_pures.
  Admitted.

End specs.