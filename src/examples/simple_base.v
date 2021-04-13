From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Import crash_weakestpre.
From self.base Require Export primitive_laws class_instances.
From self.algebra Require Import view.
From self.base Require Import proofmode.

Section simple_increment.
  Context `{!nvmG Σ}.

  Definition pure : expr :=
    let: "a" := #1 in
    let: "b" := #7 in
    "a" + "b".

  Lemma wp_with_let :
    {{{ True }}} ThreadState pure (∅, ∅, ∅) {{{ TV, RET ThreadVal (#8) TV; True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    rewrite /pure.
    wp_pures.
    iModIntro.
    by iApply "Post".
  Qed.

  Definition incr_both (ℓ1 ℓ2 : loc) : expr :=
    #ℓ1 <- #1 ;;
    WB #ℓ1 ;;
    Fence ;;
    #ℓ2 <- #1.

  Definition recover ℓ1 ℓ2 : expr :=
    let: "x" := ! ℓ1 in
    let: "y" := ! ℓ2 in
    if: "y" ≤ "x"
    then #() #()
    else #().

  Definition init_hist : history := {[ 0 := Msg #0 ∅ ∅ ]}.

  Lemma wp_incr ℓ1 ℓ2 k E1 :
    {{{ ℓ1 ↦h init_hist ∗ ℓ2 ↦h init_hist }}}
      ThreadState (incr_both ℓ1 ℓ2) (∅, ∅, ∅) @ k; E1
    {{{ v t1 t2 TV, RET ThreadVal v TV;
      ℓ1 ↦h {[ 0 := Msg #0 ∅ ∅; t1 := Msg #1 ∅ ∅ ]} ∗
      ℓ2 ↦h {[ 0 := Msg #0 ∅ ∅; t2 := Msg #1 {[ ℓ1 := MaxNat t1 ]} {[ ℓ1 := MaxNat t1 ]} ]}
    }}}
    {{{ True }}}.
  Proof.
  Abort.
  
End simple_increment.
