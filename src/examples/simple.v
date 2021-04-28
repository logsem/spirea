From iris.proofmode Require Import tactics.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances.
From self.high Require Import proofmode.
From self.high Require Import dprop weakestpre recovery_weakestpre.

Definition prog : expr := let: "l" := ref #1 in ! "l".

Definition pure : expr :=
  let: "a" := #1 in
  let: "b" := #7 in
  "a" + "b".

Section specs.
  Context `{!nvmG Σ}.

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

  Definition incr (ℓa ℓb : loc) : expr :=
    #ℓa <- #1 ;;
    WB #ℓa ;;
    Fence ;;
    #ℓb <- #1.

  Definition recover (ℓa ℓb : loc) : expr :=
    let: "a" := ! #ℓa in
    let: "b" := ! #ℓb in
    if: "b" ≤ "a"
    then #() #() (* Get stuck. *)
    else #().

  Lemma wpc_incr (ℓa ℓb : loc) : expr :=

  Lemma incr_safe s k E ℓa ℓb :
    ⊢ wpr s k E (incr ℓa ℓb) (recover ℓa ℓb) (λ _, True%I) (λ _ _, True%I).
  Proof.
  Abort.

End simple_increment.
