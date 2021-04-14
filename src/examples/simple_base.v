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

  Lemma wp_with_let TV :
    {{{ True }}} ThreadState pure TV {{{ RET ThreadVal (#8) TV; True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    rewrite /pure.
    wp_pures.
    iModIntro.
    by iApply "Post".
  Qed.

  Definition alloc_load : expr :=
    let: "ℓ" := ref #4
    in !"ℓ".

  Lemma wp_load_store SV PV :
    {{{ validV SV }}} ThreadState alloc_load (SV, PV, ∅) {{{ TV', RET ThreadVal (#4) TV'; True }}}.
  Proof.
    iIntros (Φ) "#val Post".
    rewrite /alloc_load.
    wp_alloc ℓ as "pts".
    wp_pures.
    iApply (wp_load with "[$pts $val]").
    iNext. iIntros (t v) "[pts [%look gt]]".
    move: look.
    rewrite /initial_history.
    rewrite -lookup_fmap.
    rewrite map_fmap_singleton.
    intros [<- <-]%lookup_singleton_Some.
    iApply "Post".
    done.
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
