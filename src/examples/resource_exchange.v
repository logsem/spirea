From Equations Require Import Equations.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import gmap_view.
From iris_named_props Require Import named_props.
From nextgen Require Import cmra_morphism_extra gmap_view_transformation.

From self Require Import extra solve_view_le encode_relation map_extra view_slice.

From self.lang Require Import syntax tactics lemmas.

From self.base Require Import generational_resources primitive_laws.

From self.high Require Import wrappers monpred_simpl protocol locations crash_weakestpre weakestpre.
From self.high.modalities Require Import post_fence_sync_advanced.
From self.high.lib Require Import abstract_state increasing_map.
From self.high Require Import weakestpre_at weakestpre_exp proofmode.

From self Require Export lang.
From self.high Require Export dprop.

Set Default Proof Using "Type*".

Section Program.
    Definition try_push: expr :=
    λ: "ℓ" "v",
      if: Snd (CmpXchg "ℓ" NONEV (SOME "v")) then
        #()
      else
        #().

  Definition try_pop: expr :=
    λ: "ℓ",
      match: !_AT "ℓ" with
        NONE => NONEV
      | SOME "v" =>
          if: Snd (CmpXchg "ℓ" (SOME "v") NONEV) then
            Flush "ℓ";; FenceSync ;; SOME "v"
          else
            NONEV
      end.
End Program.

(* The exclusive ghost resource: [gset_disj nat]. *)
Definition excl_opsR : cmra := gmap_viewR nat unitO.
Class excl_opsG (Σ: gFunctors) (Ω: gGenCmras Σ) := {
  excl_ops_inG :: genInDepsG Σ Ω excl_opsR [#];
}.
Section Ghosts.
  Context `{!excl_opsG Σ Ω}.

  Definition drop_op (p: nat) n (_: unit): option _ :=
    if decide (n < p) then Some () else None.

  #[export] Instance drop_op_maptrans p: MapTrans (drop_op p).
  Proof.
    split; last solve_proper. unfold drop_above_hist.
    intros. done.
  Qed.
  
  Definition excl_ops_trans (p: nat): excl_opsR → excl_opsR :=
    map_entry_lift_gmap_view (drop_op p).

  Definition excl_ops_pred (p: nat): pred_over excl_opsR :=
    λ t, ∃ p', p ≤ p' ∧ t = excl_ops_trans p'.
  
  Definition ops_auth γ (n: nat): iProp Σ :=
    gen_own γ (gmap_view_auth (DfracOwn 1) (map_seq 0 (repeat () n))).

  Definition ops_frag γ (n: nat): iProp Σ :=
    "frag" ∷ gen_own γ (gmap_view_frag n (DfracOwn 1) ()) ∗
    "#frag_rely_self" ∷ ∃ p', ⌜ n < p' ⌝ ∗ rely_self γ (excl_ops_pred p').

  Definition ops_token γ (p: nat) :=
    token γ [#] (excl_ops_pred p) (excl_ops_pred p).
  
  Lemma excl_ops_alloc:
    ⊢ |==> ∃ γ, ops_auth γ 0 ∗ ops_token γ 0.
  Proof.
    iMod (own_gen_alloc (DS := [#]) (gmap_view_auth (DfracOwn 1) ∅) [#] [##] with "[]") as (γ) "(HO & tok)".
    { by apply gmap_view_auth_valid. }
    { iIntros (i'). inversion i'. }
    iMod (token_strengthen_promise (DS := [#])
            _ [#] [##] _ (excl_ops_pred 0) _ (excl_ops_pred 0) with "[] tok")
      as "tok".
    { intros ???. unfold True_rel. rewrite huncurry_curry. done. }
    { done. }
    { intros ts. dependent elimination ts. done. }
    { intros ts _. dependent elimination ts.
      exists (excl_ops_trans 0).
      split; first apply _.
      eexists.
      done. }
    { iIntros (i'). inversion i'. }
    iModIntro.
    iDestruct (token_to_rely with "tok") as "#rely".
    iDestruct (rely_to_rely_self with "rely") as "?".
    iExists _.
    iFrame "∗#".
  Qed.
  
  #[export] Instance ops_frag_into_base_nextgen {γ} n:
    base_IntoNextgen
      (ops_frag γ n)
      (ops_frag γ n).
  Proof.
    rewrite /base_IntoNextgen /ops_frag.
    iNamed 1.
    iModIntro.
    iDestruct "frag" as (t) "[picked_in frag]".
    iDestruct "frag_rely_self" as (p Hlt) "[rely_self (%t' & (%p' & %Hle & %H) & picked_in')]".
    iPickedInAgree "picked_in picked_in'".
    subst t.
    iSplitL "frag".
    { iApply (gen_own_proper with "frag").
      rewrite /excl_ops_trans.
      unfold map_entry_lift_gmap_view, gMapTrans_frag_lift, map_trans_frag_lift, fmap_view, fmap_pair. simpl.
      unfold gmap_view_frag, view_frag.
      f_equiv.
      rewrite -{2}insert_empty.
      erewrite map_imap_insert_Some;
        first rewrite map_imap_empty insert_empty //.
      rewrite agree_option_map_to_agree /drop_op decide_True //.
      lia. }
    iExists p.
    by iFrame "#".
  Qed.

  Lemma map_seq_grow (n: nat):
    (map_seq 0 (repeat () (S n)): gmap nat unit) = <[ n := () ]> (map_seq 0 (repeat () n)).
  Proof.
    simpl repeat.
    rewrite repeat_cons map_seq_snoc.
    f_equiv.
    rewrite repeat_length //.
  Qed.
  
  Lemma ops_auth_grow {γ n}:
    ops_auth γ n ==∗ ops_auth γ (S n) ∗ gen_own γ (gmap_view_frag n (DfracOwn 1) ()).
  Proof.
    iIntros "ops_auth".
    iMod (gen_own_update with "ops_auth") as "[$ $]"; last done.
    rewrite map_seq_grow.
    apply gmap_view_alloc; last done.
    rewrite lookup_map_seq_0 lookup_ge_None repeat_length //.
  Qed.
    
  Lemma ops_auth_ops_frag_false {γ} n:
    ops_auth γ n -∗
    ops_frag γ n -∗
    False.
  Proof.
    iIntros "auth". iNamed 1.
    iDestruct (gen_own_valid_2 with "auth frag") as %[_ contra]%gmap_view_both_valid_L.
    rewrite lookup_map_seq_0 in contra.
    apply lookup_lt_Some in contra.
    rewrite repeat_length in contra.
    lia.
  Qed.

  Lemma ops_token_strengthen {γ p} p':
    p ≤ p' →
    ops_token γ p ==∗ ops_token γ p' ∗ rely_self γ (excl_ops_pred p').
  Proof.
    iIntros (?) "token".
    iMod (token_strengthen_promise_0_deps _ _ (excl_ops_pred p') with "token") as "token".
    { rewrite /excl_ops_pred.
      intros ? (p'' & ? & ->).
      eexists.
      split; last done.
      lia. }
    { exists (excl_ops_trans p').
      split; first apply _.
      by eexists. }
    iDestruct (token_to_rely with "token") as "#rely".
    iDestruct (rely_to_rely_self with "rely") as "$".
    done.
  Qed.

  Lemma map_entry_lift_gmap_view_auth dq (m: gmap nat unit) map_entry :
    (map_entry_lift_gmap_view map_entry (gmap_view_auth dq m)) =
    (gmap_view_auth dq (map_imap map_entry m)).
  Proof.
    unfold map_entry_lift_gmap_view, fmap_view, fmap_pair. simpl.
    rewrite agree_map_to_agree. done.
  Qed.
End Ghosts.
Opaque ops_frag.

(* We now define the abstract state used for the location [ℓ] *)
Section Protocol.
  Context `{!excl_opsG Σ Ω, !nvmBaseGS Σ Ω}.
  Variables (γ: gname) (R: val → dProp Σ).
  Hypothesis (R_buffer_free: ∀ v, BufferFree (R v)).
  Hypothesis (R_NGF: ∀ v, IntoNGFlush (R v) (R v)).
  #[local] Existing Instances R_buffer_free R_NGF.
  
  Instance list_abstract_state T `{!EqDecision T, Countable T} : AbstractState (list T) :=
    { abs_state_relation := prefix }.

  (* [inl] is push, [inr] is pop. *)
  Notation ST := (list (val + unit)).

  Definition p_pure (σ: ST) (v: val): dProp Σ :=
    ⌜ match last σ with
      | Some (inl w) =>
          v = SOMEV w 
      | _ =>  v = NONEV 
      end ⌝.
  
  Definition p_full (σ: ST) (v: val): dProp Σ :=
    ⎡ ops_auth γ (length σ) ⎤ ∗
    match last σ with
    | Some (inl w) => ⌜ v = SOMEV w ⌝ ∗ ⌜ val_is_unboxed v ⌝ ∗ R w
    | _ => ⌜ v = NONEV ⌝
    end.

  Definition p_read (σ: ST) (v: val): dProp Σ :=
    match last σ with
    | Some (inl w) =>
        ⌜ v = SOMEV w ⌝ ∗ ⌜ val_is_unboxed v ⌝ ∗
        ((R w) ∨ ⎡ ops_frag γ (length σ) ⎤)
    | _ => ⌜ v = NONEV ⌝
    end.
  
  Definition p_pers (σ: ST) (v: val): dProp Σ :=
    ⎡ ops_token γ (length σ) ⎤ ∗ p_pure σ v.
  
  Lemma p_read_p_pure (σ: ST) (v: val):
    p_read σ v -∗ p_pure σ v.
  Proof.
    rewrite /p_read /p_pure.
    destruct (last σ) as [[] | ]; try naive_solver.
    iIntros "[$ _]".
  Qed.
  
  Definition prot : LocationProtocol ST :=
  {| protocol.p_full := p_full;
     protocol.p_read := p_read;
     protocol.p_pers := p_pers;
     p_bumper h := h |}.
  
  #[export] Instance prot_cond : ProtocolConditions prot.
  Proof.
    split; try done; try solve_proper; try apply _.
    - intros σ v.
      rewrite /prot /p_full /=.
      destruct (last σ) as [[] | ]; try apply _.
    - intros σ v.
      rewrite /prot /p_read /=.
      destruct (last σ) as [[] | ]; try apply _.
    - intros σ v.
      apply bi.equiv_entails. split.
      + rewrite /prot /p_full /p_read /=.
        iIntros "[ops_auth R]".
        iSplitL "R"; destruct (last σ) as [[ w | ] | ]; try naive_solver.
        * iDestruct "R" as "($ & $ & R)".
          by iLeft.
        * iIntros "($ & $ & [ $ | ops_frag ])"; first done.
          iDestruct (ops_auth_ops_frag_false with "ops_auth ops_frag") as %[].
      + iIntros "[? H]".
        by iApply "H".
    - rewrite /prot /p_full /p_read /p_pers /p_pure /=.
      iIntros (σ_p v_p σ_f v_f) "%HorderPF [ops_token Hσ_p] [ops_auth R]".
      iSplit.
      + (* we pick [t] to be [excl_ops_trans (length σ_f)] *)
        iMod (ops_token_strengthen (length σ_f) with "ops_token") as "[ops_token _]".
        { by apply prefix_length. }
        iMod (token_pick (DS := [#]) _ [#] _ _ [##]%HV (excl_ops_trans (length σ_f)) with "[] ops_token") as "[token picked_out]".
        { by eexists. }
        { iIntros (i'). inversion i'. }
        iModIntro.
        (* It's difficult to get [match .. with] to work with typeclasses. *)
        destruct (last σ_f) as [[ w | ] | ]; iModIntro.
        * iDestruct "ops_auth" as (?) "[picked_in ops_auth]".
          iPickedInAgree "picked_out picked_in".
          iDestruct "R" as "[% R]".
          iFrame "∗%".
          rewrite /excl_ops_trans map_entry_lift_gmap_view_auth /=.
          iApply (gen_own_proper with "ops_auth").
          f_equiv.
          rewrite map_equiv_iff.
          intros i.
          rewrite map_lookup_imap ?lookup_map_seq_0 /drop_op /=.
          destruct (decide _); destruct (repeat () (length σ_f) !! i) as [ [] | ] eqn:Hlook; rewrite Hlook /= //.
          apply lookup_lt_Some in Hlook.
          rewrite repeat_length in Hlook.
          lia.
        * iDestruct "ops_auth" as (?) "[picked_in ops_auth]".
          iPickedInAgree "picked_out picked_in".
          iDestruct "R" as "%".
          iFrame "∗%".
          rewrite /excl_ops_trans map_entry_lift_gmap_view_auth /=.
          iApply (gen_own_proper with "ops_auth").
          f_equiv.
          rewrite map_equiv_iff.
          intros i.
          rewrite map_lookup_imap ?lookup_map_seq_0 /drop_op /=.
          destruct (decide _); destruct (repeat () (length σ_f) !! i) as [ [] | ] eqn:Hlook; rewrite Hlook /= //.
          apply lookup_lt_Some in Hlook.
          rewrite repeat_length in Hlook.
          lia.
        * iDestruct "ops_auth" as (?) "[picked_in ops_auth]".
          iPickedInAgree "picked_out picked_in".
          iDestruct "R" as "%".
          iFrame "∗%".
          rewrite /excl_ops_trans map_entry_lift_gmap_view_auth /=.
          iApply (gen_own_proper with "ops_auth").
          f_equiv.
          rewrite map_equiv_iff.
          intros i.
          rewrite map_lookup_imap ?lookup_map_seq_0 /drop_op /=.
          destruct (decide _); destruct (repeat () (length σ_f) !! i) as [ [] | ] eqn:Hlook; rewrite Hlook /= //.
          apply lookup_lt_Some in Hlook.
          rewrite repeat_length in Hlook.
          lia.
      + iIntros (σ_c v_c) "!> R %HorderPC %HorderCF".
        (* we pick [t] to be [excl_ops_trans (length σ_c)] *)
        iMod (ops_token_strengthen (length σ_c) with "ops_token") as "[ops_token _]".
        { by apply prefix_length. }
        iMod (token_pick (DS := [#]) _ [#] _ _ [##]%HV (excl_ops_trans (length σ_c)) with "[] ops_token") as "[token picked_out]".
        { by eexists. }
        { iIntros (i'). inversion i'. }
        iModIntro.
        destruct (last σ_c) as [[ w | ] | ]; iModIntro.
        * iDestruct "ops_auth" as (?) "[picked_in ops_auth]".
          iPickedInAgree "picked_out picked_in".
          iDestruct "R" as "[% R]".
          iFrame "∗%".
          rewrite /excl_ops_trans map_entry_lift_gmap_view_auth /=.
          iAssert ⎡ ops_auth γ (length σ_c) ⎤%I with "[ops_auth]" as "ops_auth".
          { iApply (gen_own_proper with "ops_auth").
            f_equiv.
            rewrite map_equiv_iff.
            intros i.
            rewrite map_lookup_imap ?lookup_map_seq_0 /drop_op /=.
            destruct (decide _);
              destruct (repeat () (length σ_f) !! i) as [ [] | ] eqn:Hlook1;
              destruct (repeat () (length σ_c) !! i) as [ [] | ] eqn:Hlook2;
              rewrite ?Hlook1 ?Hlook2 /= //.
            - apply lookup_ge_None in Hlook2.
              rewrite repeat_length in Hlook2. 
              lia.
            - apply lookup_ge_None in Hlook1.
              rewrite repeat_length in Hlook1.
              assert (length σ_c ≤ length σ_f) by by apply prefix_length. 
              lia.
            - apply lookup_lt_Some in Hlook2.
              rewrite repeat_length in Hlook2. 
              lia.
            - apply lookup_lt_Some in Hlook2.
              rewrite repeat_length in Hlook2. 
              lia. }
          iDestruct "R" as "[ $ [ $ | ops_frag ]]"; first done.
          iDestruct (ops_auth_ops_frag_false with "ops_auth ops_frag") as %[].
        * iDestruct "ops_auth" as (?) "[picked_in ops_auth]".
          iPickedInAgree "picked_out picked_in".
          iDestruct "R" as "%".
          iFrame "∗%".
          rewrite /excl_ops_trans map_entry_lift_gmap_view_auth /=.
          iAssert ⎡ ops_auth γ (length σ_c) ⎤%I with "[ops_auth]" as "$".
          { iApply (gen_own_proper with "ops_auth").
            f_equiv.
            rewrite map_equiv_iff.
            intros i.
            rewrite map_lookup_imap ?lookup_map_seq_0 /drop_op /=.
            destruct (decide _);
              destruct (repeat () (length σ_f) !! i) as [ [] | ] eqn:Hlook1;
              destruct (repeat () (length σ_c) !! i) as [ [] | ] eqn:Hlook2;
              rewrite ?Hlook1 ?Hlook2 /= //.
            - apply lookup_ge_None in Hlook2.
              rewrite repeat_length in Hlook2. 
              lia.
            - apply lookup_ge_None in Hlook1.
              rewrite repeat_length in Hlook1.
              assert (length σ_c ≤ length σ_f) by by apply prefix_length. 
              lia.
            - apply lookup_lt_Some in Hlook2.
              rewrite repeat_length in Hlook2. 
              lia.
            - apply lookup_lt_Some in Hlook2.
              rewrite repeat_length in Hlook2. 
              lia. }
        * iDestruct "ops_auth" as (?) "[picked_in ops_auth]".
          iPickedInAgree "picked_out picked_in".
          iDestruct "R" as "%".
          iFrame "∗%".
          rewrite /excl_ops_trans map_entry_lift_gmap_view_auth /=.
          iAssert ⎡ ops_auth γ (length σ_c) ⎤%I with "[ops_auth]" as "$".
          { iApply (gen_own_proper with "ops_auth").
            f_equiv.
            rewrite map_equiv_iff.
            intros i.
            rewrite map_lookup_imap ?lookup_map_seq_0 /drop_op /=.
            destruct (decide _);
              destruct (repeat () (length σ_f) !! i) as [ [] | ] eqn:Hlook1;
              destruct (repeat () (length σ_c) !! i) as [ [] | ] eqn:Hlook2;
              rewrite ?Hlook1 ?Hlook2 /= //.
            - apply lookup_ge_None in Hlook2.
              rewrite repeat_length in Hlook2. 
              lia.
            - apply lookup_ge_None in Hlook1.
              rewrite repeat_length in Hlook1.
              assert (length σ_c ≤ length σ_f) by by apply prefix_length. 
              lia.
            - apply lookup_lt_Some in Hlook2.
              rewrite repeat_length in Hlook2. 
              lia.
            - apply lookup_lt_Some in Hlook2.
              rewrite repeat_length in Hlook2. 
              lia. }
    - rewrite /prot /p_read /=.
      iIntros (σ v) "R".
      destruct (last σ) as [[ w | ] | ]; iModIntro; done.
  Qed.
End Protocol.

Section Proof.
  Context `{!excl_opsG Σ Ω, !nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ}.
  Variables (γ: gname) (R: val → dProp Σ).
  Hypothesis (R_buffer_free: ∀ v, BufferFree (R v)).
  Hypothesis (R_NGF: ∀ v, IntoNGFlush (R v) (R v)).
  
  Definition is_stack ℓ: dProp Σ :=
    ∃ σs σ_i, ℓ ↦_AT^{prot γ R} (σs ++ [σ_i]).

  #[export] Instance is_stack_persistent ℓ:
    Persistent (is_stack ℓ).
  Proof.
    rewrite /is_stack.
    apply bi.exist_persistent. intros.
    apply bi.exist_persistent. intros.
    apply _.
  Qed.
    
  Lemma wp_try_push ℓ w:
    val_is_unboxed (SOMEV w) →
    {{{ is_stack ℓ ∗ R w }}}
      try_push #ℓ w
    {{{ RET #(); True }}}.
  Proof.
    rewrite /try_push.
    iIntros (??) "[(%σs & %σ_i & is_stack) R] HΦ".
    wp_pures.
    wp_bind (CmpXchg _ _ _).
    iApply (wp_cmpxchg_at
              (λ _ _, True%I) (λ _, True%I) True%I
              (λ _, True%I) (λ σ, ⎡ ops_auth γ (length σ) ⎤)%I with "[$is_stack R]").
    { iIntros.
      iSplitR. { iIntros "_". iPureIntro. left. done. }
      iSplitL.
      - iIntros.
        iExists (σ_l ++ [inl w]).
        iSplitR.
        { iIntros "!> _".
          iPureIntro.
          by apply prefix_app_r. }
        iSplitR.
        { iIntros (???) "[ops_auth1 _] [[ops_auth2 _] | [ _ (% & % & % & [ops_auth2 _ ]) ] ]";
            iDestruct (gen_own_valid_2 with "ops_auth1 ops_auth2") as %[]%gmap_view_auth_op_valid. }
        iSplitR.
        { iIntros "!> predP".
          iSplitR; first by iModIntro.
          naive_solver. }
        iSplitR.
        { iModIntro.
          iIntros "[[$ R] _]".
          rewrite /prot /p_read /=.
          destruct (last σ_l) as [[] | ]; try done.
          iDestruct "R" as "($ & $ & R)".
          by iLeft. }
        iIntros "ops_auth".
        iMod (ops_auth_grow with "ops_auth") as "[ops_auth _]".
        iModIntro.
        iSplitL; last (iSplit; [by iModIntro | done]).
        rewrite /prot /p_full /=.
        rewrite app_length /= Nat.add_1_r last_snoc.
        by iFrame.
      - iSplit; last done.
        iModIntro.
        naive_solver. }
    iIntros "!>" (????) "_".
    destruct b; wp_pures; iModIntro; iApply "HΦ"; done.
  Qed.

  Lemma wp_try_pop ℓ:
    {{{ is_stack ℓ }}}
      try_pop #ℓ
    {{{ v, RET v; (∃ w, ⌜ v = SOMEV w ⌝ ∗ R w) ∨ ⌜ v = NONEV ⌝ }}}.
  Proof.
    rewrite /try_pop.
    iIntros (?) "(%σs & %σ_i & #is_stack) HΦ".
    wp_pures.
    wp_bind (Load _ _).
    iDestruct (mapsto_at_drop with "is_stack") as "mapsto".
    iApply (wp_load_at_simple ℓ _
              (λ σ v, ⌜ match last σ with | Some (inl w) => v = SOMEV w ∧ val_is_unboxed v | _ => v = NONEV end ⌝)%I
              with "[$mapsto]").
    { iIntros "!>" (σ_l v_l ?) "H".
      rewrite /prot /p_read /=.
      destruct (last σ_l) as [[] | ]; try naive_solver.
      iDestruct "H" as "(% & % & $)".
      done. }
    iClear (σ_i) "mapsto is_stack".
    iIntros "!>" (σ_i v_i) "[#is_stack >%HlastOp]".
    (* TODO: clever way to achieve this? *)
    destruct (last σ_i) as [[ v | ] | ]; first destruct (HlastOp) as [-> safe]; wp_pures.
    - wp_bind (CmpXchg _ _ _).
      iEval (rewrite -(app_nil_l [σ_i])) in "is_stack".
      iApply (wp_cmpxchg_at
                (λ σ_l σ_t, (⎡ gen_own γ (gmap_view_frag (length σ_l) (DfracOwn 1) ()) ⎤ ∗ ⌜ last σ_l = Some (inl v) ⌝ ∗ ⌜ length σ_l < length σ_t ⌝)%I)
                (λ _, True%I)
                True%I
                (λ _, True%I)
                (λ σ_l, ⎡ ops_auth γ (length σ_l) ⎤ ∗ ⌜ last σ_l = Some (inl v) ⌝)%I with "[$is_stack]").
      { iIntros.
        iSplitR. { iIntros "_". iPureIntro. left. done. }
        iSplit.
        - iIntros.
          subst v_l.
          iExists (σ_l ++ [inr ()]).
          iSplitR.
          { iIntros "!> _".
            iPureIntro.
            by apply prefix_app_r. }
          iSplitL.
          { iIntros (???) "[ops_auth1 _] [[ops_auth2 _] | [ _ (% & % & % & [ops_auth2 _ ]) ] ]";
              iDestruct (gen_own_valid_2 with "ops_auth1 ops_auth2") as %[]%gmap_view_auth_op_valid. }
          iSplitL.
          { iIntros "!> predP".
            iSplitR; first by iModIntro.
            naive_solver. }
          iSplitL.
          { iModIntro.
            iIntros "[[$ R] _]".
            rewrite /prot /p_read /=.
            destruct (last σ_l) as [[] | ]; try (iDestruct "R" as "%"; congruence).
            iDestruct "R" as "(%eq & %safe' & R)".
            injection eq as ->.
            iSplitL; last done.
            iSplitR; first done.
            iSplitPure; first done.
            iLeft. done. }
          iIntros "[ops_auth %]".
          iMod (ops_auth_grow with "ops_auth") as "[ops_auth ops_frag]".
          iModIntro.
          iSplitL "ops_auth". 
          + rewrite /prot /p_full /=.
            rewrite app_length /= Nat.add_1_r last_snoc.
            by iFrame.
          + iFrame.
            iSplit; first by iModIntro.
            iSplit; first done.
            iPureIntro.
            rewrite app_length /=.
            lia.
        - iSplit; last done.
          iModIntro.
          naive_solver. }
      iIntros "!>" (????) "Hpost".
      destruct b; wp_pures.
      + iDestruct "Hpost" as "[(_ & >[frag [%Hlook %]] & #is_stack' & seen_state) | [% ?]]"; last done.
        wp_bind (Flush _).
        iApply (wp_flush_xchg _ (prot γ R) σ_l σ_t _ _ (R v) with "[is_stack $seen_state frag]").
        { iDestruct (mapsto_at_store_lb with "is_stack'") as "$".
          iSplitR; first by iNamed "is_stack".
          rewrite /exchange_1 /exchange_2 /exchange_3.
          iIntros (v_t) "!> predR".
          iDestruct (p_read_p_pure with "predR") as "%".
          iFrame.
          iIntros (σ_old v_old) "!>".
          iSplit.
          - iIntros (?) "[ops_token _]".
            rewrite /prot /p_pers /=.
            iMod (ops_token_strengthen (length σ_t) with "ops_token") as "[$ #rely]".
            { by apply prefix_length. }
            iModIntro.
            iSplitPure; first done.
            iIntros (?) "!> predR".
            iModIntro.
            rewrite /p_read /= Hlook.
            Transparent ops_frag.
            iDestruct "predR" as "($ & $ & [$ | [frag' _ ] ] )".
            + iRight.
              rewrite /ops_frag.
              iFrame.
              iExists _. iFrame "#".
              done.
            + iDestruct (gen_own_valid_2 with "frag frag'") as %[]%gmap_view_frag_op_valid.
              done.
          - iIntros (?) "[ops_token $]".
            iDestruct (token_to_rely with "ops_token") as "#rely".
            iDestruct (rely_to_rely_self with "rely") as "rely_self".
            iFrame "ops_token".
            iModIntro.
            iIntros (?) "!> predR".
            iModIntro.
            rewrite /prot /p_read /= Hlook.
            Transparent ops_frag.
            iDestruct "predR" as "($ & $ & [$ | [frag' _ ] ])".
            + iRight.
              rewrite /ops_frag.
              iFrame.
              iExists _. iFrame "#".
              iPureIntro.
              eapply Nat.lt_le_trans; first done.
              by apply prefix_length.
            + iDestruct (gen_own_valid_2 with "frag frag'") as %[contra _]%gmap_view_frag_op_valid.
              done. }
        iIntros "!> R".
        wp_pures.
        wp_bind FenceSync.
        iApply (wp_fence_sync' with "R").
        iIntros "!> [_ R]".
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iLeft.
        iExists v.
        by iFrame.
      + iModIntro.
        iApply "HΦ".
        by iRight.
    - subst v_i.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      by iRight.
    - subst v_i.
      wp_pures.
      iModIntro.
      iApply "HΦ".
      by iRight.
  Qed.
End Proof.
