From iris.proofmode Require Import tactics.
From iris.bi Require Import monpred.
From iris.program_logic Require weakestpre.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Export notation lang lemmas tactics syntax.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances adequacy.
From self.high Require Import proofmode wpc_proofmode.
From self.high Require Import weakestpre_exp weakestpre_at locations.
From self.high.modalities Require Import fence.
From self.high Require Import protocol no_buffer abstract_state_instances.

Section Axioms.
  Context `{AbstractState ST}.
  Context `{!nvmG Σ}.

  Implicit Types (ℓ : loc) (s : ST) (prot : LocationProtocol ST).

  Lemma wp_store_na ℓ prot (ss: list ST) v s__last s st E `{!ProtocolConditions prot} :
    list.last ss = Some s__last →
    s__last ⊑ s →
    {{{ mapsto_na ℓ prot 1 ss ∗ prot.(p_full) s v }}}
      #ℓ <-_NA v @ st; E
    {{{ RET #(); mapsto_na ℓ prot 1 (ss ++ [s]) }}}.
  Proof.
  Admitted.
End Axioms.

Section fence_sync.
  Context `{!nvmG Σ}.

  Variable (ℓ ℓ': loc).

  Definition prog_left : expr :=
    #ℓ' <-_NA #42;;
    Flush #ℓ' ;;
    Fence ;;
    let: "b" := Snd (CmpXchg #ℓ #0 #1) in
    Flush #ℓ ;;
    FenceSync ;;
    "b".

  Definition prog_right : expr :=
    CmpXchg #ℓ #1 #2.

  (* Predicate used for the location [ℓ']. *)
  Definition prot' : LocationProtocol nat :=
    {| p_full := λ (n : nat) v, ⌜ v = #n ⌝%I;
       p_read := λ (n : nat) v, ⌜ v = #n ⌝%I;
       p_pers := λ (n : nat) v, True%I;
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

  Variable (excl_token: dProp Σ).
  Axiom excl_token_excl: excl_token ∗ excl_token -∗ False.

  (* Predicate used for the location [ℓ]. *)
  Definition prot : LocationProtocol nat :=
    {| p_full := λ (n : nat) v, (⌜ v = #n ⌝ ∗ excl_token ∗ (⌜ n = 1 ⌝ -∗ ℓ' ↦_{prot'} [0; 42])) %I;
       p_read := λ (n : nat) v, ⌜ v = #n ⌝%I;
       p_pers := λ (n : nat) v, True%I;
       p_bumper n := n |}.
  Global Instance prot_cond : ProtocolConditions prot.
  Proof. Admitted.

  Lemma spec_left st E:
    {{{ ℓ' ↦_{prot'} [0] ∗ ℓ ↦_AT^{prot} [0] }}}
      prog_left @ st; E
    {{{ b, RET #b; ⌜b = true⌝ -∗ persist_lb ℓ prot 1 }}}.
  Proof.
    iIntros (Φ) "[pts' pts] Φpost".
    rewrite /prog_left.
    wp_apply (wp_store_na _ prot' [0] _ _ 42 with "[pts']");
      [ done | rewrite /sqsubseteq //=; lia | by iFrame | ].
    rewrite //=. iIntros "pts'".
    wp_pures.
    wp_apply (weakestpre.wp_flush_na _ prot' 42 1%Qp [0] with "pts'").
    iIntros "(pts' & #flush_lb' & _)".
    wp_pures.
    wp_apply (weakestpre.wp_fence).
    do 2 iModIntro.
    wp_pures.
    wp_apply (wp_cmpxchg_at
                (λ n, True)%I
                (λ _, True)%I
                (True)%I
                ℓ prot [] 0 _ _
                (λ n, excl_token)%I
                1 with "[$pts pts']").
    { iIntros.
      iExists (True)%I.
      iIntros.
      (* safe comparison *)
      iSplit. { iIntros "_". iPureIntro. left. done. }
      iSplit.
      (* success *)
      { iIntros.
        subst.
        rewrite /p_full /p_read /p_pers /prot //=.
        iSplitL "".
        { iIntros "!>[% H]".
          simplify_eq.
          iPureIntro.
          rewrite /sqsubseteq.
          lia. }
        iSplitL "".
        { iIntros (??) "% (_ & ? & _) [ (_ & ? & _) | (_ & % & % & _ & _ & ? & _) ]";
          iDestruct (excl_token_excl with "[$]") as "[]". }
        iSplitL "".
        { iIntros "!> _".
          iSplitL ""; first by iModIntro.
          done. }
        iSplitL "".
        { iIntros "!>[(% & ? & _) _]".
          iFrame "%∗". }
        iIntros "$ !>".
        iFrame "pts'".
        iSplitPure; first done.
        iSplit; first iModIntro; done.
      }
      (* failure *)
      { iSplit; last done.
        iIntros "!> ?".
        iFrame. } }
    iIntros (???) "[H | H]"; rewrite //=.
    - (* successful *)
      wp_pures.
      wp_apply (weakestpre_exp.wp_flush_lb _ prot 1 _ _ True%I with "[H]").
      { iDestruct "H" as "(_ & _ & H)".
        iSplit; first iApply (mapsto_at_store_lb ℓ prot [0] with "[$]").
        iSplit.
        { rewrite /mapsto_at.
          iNamed "H".
          done. }
        rewrite /R_progress.
        iModIntro.
        iIntros.
        iExists True%I, True%I.
        iSplitL "".
        { iIntros. repeat iModIntro. done. }
        iSplitL "".
        { iIntros. repeat iModIntro. done. }
        iIntros.
        iSplit.
        { iIntros "_ !>". done. }
        done. }
      iIntros "post_fence".
      wp_pures.
      wp_apply (weakestpre_exp.wp_fence_sync with "post_fence").
      iIntros "[? _]".
      wp_pures.
      iModIntro.
      iApply "Φpost".
      iFrame.
      done.
    - (* failed *)
      (* probably better have a lemma for flush that's essentially no-op *)
      wp_pures.
      iDestruct "H" as "(% & % & H & _)".
      wp_apply (weakestpre_exp.wp_flush_lb _ prot 0 _ _ True%I with "[H]").
      { iSplit; first iApply (mapsto_at_store_lb ℓ prot [] with "[$]").
        iSplit.
        { rewrite /mapsto_at.
          iNamed "H".
          done. }
        rewrite /R_progress.
        iModIntro.
        iIntros.
        iExists True%I, True%I.
        iSplitL "".
        { iIntros. repeat iModIntro. done. }
        iSplitL "".
        { iIntros. repeat iModIntro. done. }
        iIntros.
        iSplit.
        { iIntros "_ !>". done. }
        done. }
      iIntros "post_fence".
      wp_pures.
      wp_apply (weakestpre_exp.wp_fence_sync with "post_fence").
      iIntros "[? _]".
      wp_pures.
      iModIntro.
      iApply "Φpost".
      iIntros "%".
      congruence.
  Qed.

  Lemma spec_right st E:
    {{{ ℓ ↦_AT^{prot} [0] }}}
      prog_right @ st; E
      {{{ v b, RET (v, #b); ⌜ b = true ⌝ -∗ <fence> ℓ' ↦_{prot'} [0; 42] }}}.
  Proof.
    iIntros (Φ) "pts Φpost".
    rewrite /prog_right.
    wp_apply (wp_cmpxchg_at
                (λ n, ⌜1%Z = Z.of_nat n⌝ ∗ ℓ' ↦_{prot'} [0; 42])%I
                (λ _, True)%I
                (True)%I
                ℓ prot [] 0 _ _
                (λ n, excl_token ∗ ⌜1%Z = Z.of_nat n⌝ ∗ ℓ' ↦_{prot'} [0; 42])%I
                2 with "[$pts]").
    { iIntros.
      iExists (True)%I.
      iIntros.
      (* safe comparison *)
      iSplit. { iIntros "_". iPureIntro. left. done. }
      iSplit.
      (* success *)
      { iIntros.
        subst.
        rewrite /p_full /p_read /p_pers /prot //=.
        iSplitL "".
        { iIntros "!>[% H]".
          simplify_eq.
          iPureIntro.
          rewrite /sqsubseteq.
          lia. }
        iSplitL "".
        { iIntros (??) "% (_ & ? & _) [ (_ & ? & _) | (_ & % & % & _ & _ & ? & _) ]";
          iDestruct (excl_token_excl with "[$]") as "[]". }
        iSplitL "".
        { iIntros "!> _".
          iSplitL ""; first by iModIntro.
          iIntros "_".
          iFrame "%".
          done. }
        iSplitL "".
        { iIntros "!>[(% & ? & φ_old) _]".
          iFrame "%".
          simplify_eq.
          iFrame "%∗".
          iApply "φ_old".
          iPureIntro.
          lia. }
        iIntros "(token & % & ?) !>".
        iSplitL "token".
        { iFrame "%∗".
          iSplitPure; first done.
          iIntros (?). lia. }
        iFrame "∗%".
        by iModIntro.
      }
      (* failure *)
      { iSplit; last done.
        iIntros "!> ?".
        iFrame. } }
    iIntros (???) "H".
    iApply "Φpost".
    iIntros.
    iDestruct "H" as "[ (_ & [? ?] & _) | [% _] ]"; last congruence.
    iFrame.
  Qed.
End fence_sync.
