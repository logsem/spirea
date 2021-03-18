From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From self.lang Require Export notation primitive_laws lang.

Definition prog : expr := let: "l" := ref #1 in ! "l".

Definition pure : expr :=
  let: "a" := #1 in
  let: "b" := #7 in
  "a" + "b".

Section specs.
  Context `{!nvmG Σ}.

  Lemma wp_pure TV :
    {{{ True }}}
      (ThreadState pure TV)
    {{{ RET (ThreadVal (#8) TV); True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    wp_pures.
  Admitted.

End specs.