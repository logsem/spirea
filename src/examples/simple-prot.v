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
From self.high Require Import weakestpre_exp locations.
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


  Lemma wp_cmpxchg_at Q1 Q2 Q3 ℓ prot `{!ProtocolConditions prot} ss s_i (v_i : val) v_t R s_t st E :
    {{{
      ℓ ↦_AT^{prot} (ss ++ [s_i]) ∗
      (∀ s_l v_l s_p v_p, ∃ P, ⌜ s_i ⊑ s_l ⌝ -∗
        ((▷ prot.(p_read) s_l v_l) -∗ ⌜ vals_compare_safe v_i v_l ⌝) ∗
        (( (* in case of success *)
            ⌜ v_l = v_i ⌝ -∗
            (* The state we write fits in the history. *)
            (<obj> (prot.(p_full) s_l v_l -∗ ⌜ s_l ⊑ s_t ⌝)) ∗
            (∀ s_n v_n, ⌜ s_l ⊑ s_n ⌝ -∗ prot.(p_full) s_l v_l -∗
                        prot.(p_read) s_n v_n -∗ ⌜ s_l = s_n ∨ s_t ⊑ s_n ⌝) ∗
            (* Extract the objective knowledge from [p_pers] *)
            (<obj> (prot.(p_pers) s_p v_p -∗ <obj> P ∗ (P -∗ prot.(p_pers) s_p v_p))) ∗
            (* Extract from the location we load. *)
            (<obj> (prot.(p_full) s_l v_l ∗ P -∗ prot.(p_read) s_l v_l ∗ R s_l)) ∗
            (* Establish the invariant for the value we store. *)
            (R s_l ==∗ prot.(p_full) s_t v_t ∗ <obj> P ∗ Q1 s_l))
         ∧ (* in case of failure *)
           ((<obj> (prot.(p_full) s_l v_l -∗ prot.(p_full) s_l v_l ∗ Q2 s_l)) ∗ Q3)
        ))
    }}}
      CmpXchg #ℓ v_i v_t @ st; E
    {{{ v b s_l, RET (v, #b);
      (⌜ b = true ⌝ ∗ <fence> Q1 s_l ∗ ℓ ↦_AT^{prot} ((ss ++ [s_i]) ++ [s_t])) ∨
      (⌜ b = false ⌝ ∗ ⌜ s_i ⊑ s_l ⌝ ∗ ℓ ↦_AT^{prot} (ss ++ [s_i]) ∗ <fence> (Q2 s_l) ∗ Q3)
    }}}.
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

  (* Predicate used for the location [ℓ]. *)
  Definition prot : LocationProtocol nat :=
    {| p_full := λ (n : nat) v, (⌜ v = #n ⌝ ∗ (⌜ n ≥ 1 ⌝ -∗ store_lb ℓ' prot' 42 ∗ flush_lb ℓ' prot' 42)) %I;
       p_read := λ (n : nat) v, ⌜ v = #n ⌝%I;
       p_pers := λ (n : nat) v, True%I;
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
    { iIntros.
      rewrite /p_full /p_read /prot' //=.
      iSplit.
      - iIntros "[% H]".
        by iFrame "%∗".
      - iIntros "[% H]".
        by iApply "H".  }
  Admitted.

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
                (λ n, True)%I
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
        { rewrite /sqsubseteq.
          iIntros (??) "% [% ?] %".
          simplify_eq.
          iPureIntro.
          lia. }
        iSplitL "".
        { iIntros "!> _".
          iSplitL ""; first by iModIntro.
          done. }
        iSplitL "".
        { iIntros "!>[[% φ_old] _]".
          iFrame "%". }
        iIntros "_ !>".
        iPoseProof (mapsto_na_store_lb ℓ' prot' (1%Qp) [0] 42 with "pts'") as "#?".
        iFrame "#".
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
      wp_apply (wp_flush_lb _ prot 1 _ _ True%I with "[H]").
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
      wp_apply (wp_fence_sync with "post_fence").
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
      wp_apply (wp_flush_lb _ prot 0 _ _ True%I with "[H]").
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
      wp_apply (wp_fence_sync with "post_fence").
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
      {{{ v b, RET (v, #b); ⌜ b = true ⌝ -∗ <fence> store_lb ℓ' prot' 42 }}}.
  Proof.
    iIntros (Φ) "pts Φpost".
    rewrite /prog_right.
    wp_apply (wp_cmpxchg_at
                (λ n, ⌜1%Z = Z.of_nat n⌝ ∗ store_lb ℓ' prot' 42)%I
                (λ _, True)%I
                (True)%I
                ℓ prot [] 0 _ _
                (λ n, ⌜1%Z = Z.of_nat n⌝ ∗ store_lb ℓ' prot' 42)%I
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
        { rewrite /sqsubseteq.
          iIntros (??) "% [% ?] %".
          simplify_eq.
          iPureIntro.
          lia. }
        iSplitL "".
        { iIntros "!>[% ?]".
          iSplitL ""; first by iModIntro.
          iIntros "_".
          iFrame "%".
          done. }
        iSplitL "".
        { iIntros "!>[[% φ_old] _]".
          iFrame "%".
          simplify_eq.
          iFrame "%".
          iApply "φ_old".
          iPureIntro.
          lia. }
        iIntros "[% #?] !>".
        iFrame "#%".
        iSplit; last by iModIntro.
        iSplitPure; first done.
        by iIntros.
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

  Lemma

End fence_sync.
