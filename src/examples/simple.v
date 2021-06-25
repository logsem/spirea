From iris.proofmode Require Import tactics.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances.
From self.high Require Import proofmode wpc_proofmode.
From self.high Require Import dprop resources crash_weakestpre weakestpre recovery_weakestpre lifted_modalities.

Instance subseteq_nat : SqSubsetEq nat := λ v w, v ≤ w.

Instance subseteq_nat_preorder : PreOrder (⊑@{nat}).
Proof. apply _. Qed.

Instance nat_abstract_state : AbstractState nat.
Proof. esplit; apply _. Defined.

Definition prog : expr := let: "l" := ref #1 in ! "l".

Definition pure : expr :=
  let: "a" := #1 in
  let: "b" := #7 in
  "a" + "b".

Section specs.
  Context `{!nvmFixedG Σ, nvmDeltaG Σ}.

  Lemma wp_bin_op : ⊢ WP (#1 + #2) {{ v, ⌜1 = 1⌝ }}.
  Proof.
    wp_pures.
    iModIntro.
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

  Lemma wpc_bin_op t E : ⊢ WPC (#1 + #2) @ t; E {{ v, ⌜1 = 1⌝ }}{{ True }}.
  Proof.
    iStartProof.
    (* wpc_pure_smart wp_pure_filter as H. *)
    (* wpc_pure_smart wp_pure_filter as H. *)
    wpc_pures.
    { auto. }
    auto.
  Qed.

  Lemma wpc_with_let t E :
    ⊢ WPC pure @ t; E {{ v, ⌜ v = #8 ⌝ }}{{ True }}.
  Proof.
    rewrite /pure.
    iStartProof.
    wpc_pures. { auto. }
    auto.
  Qed.

End specs.

Section simple_increment.
  Context `{!nvmFixedG Σ, nvmDeltaG Σ}.

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

  (* NOTE: This example is currently broken since the crash condition used is
  not objective. We should use the post crash modality in the crash condition
  (maybe built in to WPC). *)
  Lemma wp_incr ℓa ℓb n E (Φ : val → dProp Σ) :
    ⊢ ℓa ↦ []; [0] | (λ s v, ⌜v = #s⌝) -∗
      ℓb ↦ []; [0] | (λ s v, ⌜v = #s⌝ ∗ know_flush_lower_bound ℓa s) -∗
      WPC (incr ℓa ℓb) @ n; E
        {{ λ _,
           ℓa ↦ []; [0; 1] | (λ s v, ⌜v = #s⌝) ∗ (* FIXME: The [0] should be moved left. *)
           ℓb ↦ []; [0; 1] | (λ s v, ⌜v = #s⌝ ∗ know_flush_lower_bound ℓa s)
        }}
        {{ ∃ (sa1 sa2 sb1 sb2 : list nat),
           ℓa ↦ sa1; sa2 | (λ s v, ⌜v = #s⌝) ∗
           ℓb ↦ sb1; sb2 | (λ s v, ⌜v = #s⌝ ∗ know_flush_lower_bound ℓa s) }}.
  Proof.
    iIntros "aPts bPts".
    rewrite /incr.

    (* The first store *)
    wpc_bind (_ <- _)%E.
    iApply wpc_atomic_no_mask.
    iSplit. { iModIntro. iExists _, _, _, _. iFrame "aPts bPts". }
    iApply (wp_store_ex with "[$aPts]").
    { reflexivity. }
    { suff H : (0 ≤ 1); first apply H. lia. }
    { done. }
    simpl.
    iNext. iIntros "aPts".
    iSplit. { iModIntro. iModIntro. iExists _, _, _, _. iFrame. }
    iModIntro.
    wpc_pures.
    { iModIntro. iExists _, _, _, _. iFrame. }

    (* The write back *)
    wpc_bind (WB _)%E.
    iApply wpc_atomic_no_mask.
    iSplit. { iModIntro. iExists _, _, _, _. iFrame "aPts bPts". }
    iApply (wp_wb_ex with "aPts"); first reflexivity.
    iNext.
    iIntros "[aPts afterFence]".
    iSplit. { iModIntro. iModIntro. iExists _, _, _, _. iFrame "aPts bPts". }
    iModIntro.
    wpc_pures.
    { iModIntro. iExists _, _, _, _. iFrame. }

    (* The fence. *)
    wpc_bind (Fence)%E.
    iApply wpc_atomic_no_mask.
    iSplit. { iModIntro. iExists _, _, _, _. iFrame "aPts bPts". }
    iApply (wp_fence with "afterFence").
    iNext.
    iIntros "#pLowerBound".
    iSplit. { iModIntro. iModIntro. iExists _, _, _, _. iFrame "aPts bPts". }
    iModIntro.
    wpc_pures.
    { iModIntro. iExists _, _, _, _. iFrame. }

    (* The last store *)
    iApply wpc_atomic_no_mask.
    iSplit. { iModIntro. iExists _, _, _, _. iFrame "aPts bPts". }
    iApply (wp_store_ex with "[$bPts]").
    { reflexivity. }
    { suff H : (0 ≤ 1); first apply H. lia. }
    { iFrame "#". done. }
    iNext. iIntros "bPts".
    iSplit. { iModIntro. iModIntro. iExists _, _, _, _. iFrame "aPts bPts". }
    iModIntro.
    iFrame "aPts bPts".
  Qed.

  (* FIXME: Hoare triples don't work as Perennial's Hoare triples are tied to iProp. *)
  (* Lemma wpc_incr' (ℓa ℓb : loc) : *)
  (*   {{{ (True : dProp Σ) }}} *)
  (*     incr ℓa ℓb @ 10; ⊤ *)
  (*   {{{ RET #(); (True : dProp Σ) }}}. *)

  (* Lemma wpc_incr (ℓa ℓb : loc) : *)
  (*   {{{ (True : dProp Σ) }}} *)
  (*     incr ℓa ℓb @ 10; ⊤ *)
  (*   {{{ RET #(); (True : dProp Σ) }}} *)
  (*   {{{ (True : dProp Σ) }}}. *)

  Lemma incr_safe s k E ℓa ℓb :
    ⊢ wpr s k E (incr ℓa ℓb) (recover ℓa ℓb) (λ _, True%I) (λ _ _, True%I).
  Proof.
  Abort.

End simple_increment.
