From iris.proofmode Require Import tactics.
From iris.bi Require Import monpred.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances adequacy.
From self.high Require Import proofmode wpc_proofmode.
From self.high Require Import weakestpre_exp weakestpre_at.
From self.high Require Import protocol no_buffer abstract_state_instances.

Section fence_sync.
  Context `{!nvmG Σ}.

  Variable (ℓ ℓ': loc).


  Definition prog_left : expr :=
    #ℓ' <-_NA #42;;
    Flush #ℓ';;
    CmpXchg #ℓ #0 #1;;
    Flush #ℓ;;
    Fence #ℓ.

  Definition prog_right : expr :=
    CmpXchg #ℓ #1 #2.

  (* Predicate used for the location [ℓ']. *)
  Definition prot' : LocationProtocol nat :=
    {| p_full := λ (n : nat) v, ⌜ v = #n ⌝%I;
       p_read := λ (n : nat) v, ⌜ v = #n ⌝%I;
       p_pers := λ (n : nat) v, ⌜ v = #n ⌝%I;
       p_bumper n := n |}.

  Global Instance prot_cond' : ProtocolConditions prot'.
  Proof.
    split; try apply _.
    { iIntros.
      rewrite /p_full /p_read /prot' //=.
      iSplit.
      - iIntros.
        by iFrame "%".
      - iIntros ([]).
        done. }
    { iIntros.
      iSplit; iIntros.
      - by iModIntro.
      - iExists (True)%I.
        iSplit; first by iIntros "!> ? !>".
        iIntros.
        by iModIntro. }
    { iIntros.
      by iModIntro. }
  Qed.

  (* Predicate used for the location [ℓ]. *)
  Definition prot : LocationProtocol nat :=
    {| p_full := λ (n : nat) v, (⌜ v = #n ⌝ ∗ (⌜ n ≥ 1 ⌝ -∗ store_lb ℓ' prot' 42)) %I;
       p_read := λ (n : nat) v, ⌜ v = #n ⌝%I;
       p_pers := λ (n : nat) v, (⌜ v = #n ⌝ ∗ (⌜ n ≥ 1 ⌝ -∗ flush_lb ℓ' prot' 42))%I;
       p_bumper n := n |}.

  Global Instance prot_cond : ProtocolConditions prot.
  Proof.
    split; try apply _.
    { intros.
      rewrite /IntoNoBuffer /p_full /prot //=.
      iIntros "[% H]".
      destruct (decide (1 ≤ s)).
      - iSpecialize ("H" with "[//]").
        iModIntro.
        iSplit; first done.
        by iIntros.
      - iModIntro.
        iSplit; first done.
        iIntros; lia. }
    { intros.
      rewrite /IntoNoBuffer /p_pers /prot //=.
      iIntros "[% H]".
      destruct (decide (1 ≤ s)).
      - iSpecialize ("H" with "[//]").
        iModIntro.
        iSplit; first done.
        by iIntros.
      - iModIntro.
        iSplit; first done.
        iIntros; lia. }
    { iIntros.
      rewrite /p_full /p_read /prot' //=.
      iSplit.
      - iIntros "[% H]".
        by iFrame "%∗".
      - iIntros "[% H]".
        by iApply "H".  }
  Admitted.

  Lemma spec_right st E:
    {{{ ℓ ↦_AT^{prot} [0] }}}
      prog_right @ st; E
      {{{ v b, RET (v, #b); ⌜ b = true ⌝ -∗ store_lb ℓ' prot' 42 }}}.
  Proof.
    iIntros (Φ) "pts Φpost".
    rewrite /prog_right.
    wp_apply (wp_cmpxchg_at
                (λ n, ⌜n = 1⌝ -∗ store_lb ℓ' prot' 42)%I
                (λ _, True)%I
                (True)%I
                ℓ prot [] 0 _ _
                (λ n, ⌜n = 1⌝ -∗ store_lb ℓ' prot' 42)%I
                2 with "[$pts]").
    { iIntros.
      iExists (True)%I.
      iIntros.
      iSplit.
      (* safe comparison *)
      { admit. }
      iSplit.
      (* success *)
      { iIntros.
        subst.
        rewrite /p_full /p_read /p_pers /prot //=.
        iSplitL "".
        - iIntros "!>[% H]".
          simplify_eq.
          iPureIntro.
          rewrite /sqsubseteq.
          lia.
        -
      }
    }

  Lemma spec ℓ st E :
    {{{ ℓ ↦_{prot} [0] }}}
      program ℓ @ st; E
    {{{ RET #(); ℓ ↦_{prot} [1] }}}.
  Proof.
    iIntros (Φ) "pts Φpost".
    rewrite /program.
    wp_apply (wp_store_na with "[$pts]"); first done.
    { suff leq : (0 ≤ 1); first apply leq. lia. }
    { done. }
    iIntros "pts".
    wp_pures.
    wp_apply (wp_flush_na with "pts").
    iIntros "(pts & _ & lb) /=".
    wp_pures.
    wp_apply wp_fence_sync.
    iModIntro.
    simpl.
    wp_pures.
    iModIntro.
    iApply "Φpost".
    iApply (mapsto_na_persist_lb with "pts lb").
    cbn. lia.
  Qed.

End fence_sync.
