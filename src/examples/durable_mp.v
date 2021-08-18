From iris.proofmode Require Import tactics.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances.
From self.high Require Import proofmode wpc_proofmode.
From self.high Require Import crash_weakestpre weakestpre recovery_weakestpre.

Section program.
  Definition leftProg (x y : loc) : expr :=
    #x <- #1 ;;
    WB #x ;;
    Fence ;;
    #y <-{rel} #1.

  Definition rightProg (y z : loc) : expr :=
    if: !{acq} #y = #1
    then Fence ;; #z <- #1
    else #().

  Definition prog (x y z : loc) : expr :=
    Fork (leftProg x y) ;; rightProg y z.

  Definition recovery x z : expr :=
    if: ! z = #1
    then assert: ! x = #1
    else #().
End program.

Instance subseteq_nat : SqSubsetEq nat := λ v w, v ≤ w.

Instance subseteq_nat_preorder : PreOrder (⊑@{nat}).
Proof. apply _. Qed.

Instance nat_abstract_state : AbstractState nat.
Proof. esplit; apply _. Defined.

Section proof.
  Context `{nvmFixedG Σ, nvmDeltaG Σ}.

  Context (x y z : loc).

  Definition inv_x (n : nat) (v : val) (hG : nvmDeltaG Σ) : dProp Σ := ⌜v = #n⌝.

  Definition inv_y (n : nat) (v : val) (hG : nvmDeltaG Σ) : dProp Σ :=
    ⌜v = #n⌝ ∗ (⌜n = 1⌝ -∗ know_flush_lb x 1).

  Definition inv_z (n : nat) (v : val) (hG : nvmDeltaG Σ) : dProp Σ :=
    ⌜v = #n⌝ ∗ (⌜n = 1⌝ -∗ know_flush_lb x 1).

  Lemma prog_spec k E :
    {{{
      ⎡ know_pred x inv_x ⎤ ∗
      ⎡ know_pred y inv_y ⎤ ∗
      ⎡ know_pred z inv_z ⎤ ∗
      x ↦ₚ [0] ∗
      know_store_lb y 0 ∗
      z ↦ₚ [0]
    }}}
      prog x y z
    @ k ; E
    {{{ RET #(); True }}}
    {{{ <PC> _, ∃ (sx sz : list nat), x ↦ₚ sx ∗ z ↦ₚ sz }}}.
  Proof.
    iIntros (Φ Φc).
    iIntros "(a & b & c)".
  Abort.

End proof.
