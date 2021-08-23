From iris.proofmode Require Import tactics.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances.
From self.high Require Import proofmode wpc_proofmode.
From self.high Require Import dprop resources crash_weakestpre weakestpre recovery_weakestpre lifted_modalities post_crash_modality.

Instance subseteq_nat : SqSubsetEq nat := λ v w, v ≤ w.

Instance subseteq_nat_preorder : PreOrder (⊑@{nat}).
Proof. apply _. Qed.

Instance nat_abstract_state : AbstractState nat.
Proof. esplit; apply _. Defined.

Lemma subseteq_nat_le (n m : nat) : n ⊑ m = (n ≤ m).
Proof. done. Qed.

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

  Definition incr_both (ℓa ℓb : loc) : expr :=
    #ℓa <- #1 ;;
    WB #ℓa ;;
    Fence ;;
    #ℓb <- #1.

  (* After a crash the following is possible: [a = 0, b = 0], [a = 1, b = 0],
  and [a = 1, b = 1]. The case that is _not_ possible is: [a = 0, b = 1]. *)

  Definition recover (ℓa ℓb : loc) : expr :=
    let: "a" := ! #ℓa in
    let: "b" := ! #ℓb in
    if: "a" < "b"
    then #() #() (* Get stuck. *)
    else #().

  Definition crash_condition {hD : nvmDeltaG Σ} ℓa ℓb : dProp Σ :=
    ("pred1" ∷ ⎡ know_pred ℓa (λ (n : nat) v _, ⌜v = #n⌝) ⎤ ∗
     "pred2" ∷ ⎡ know_pred ℓb (λ (n : nat) v hG, ⌜v = #n⌝ ∗ know_flush_lb ℓa n) ⎤ ∗
     "pts" ∷ ∃ (sa sb : list nat), "aPts" ∷ ℓa ↦ₚ sa ∗ "bPts" ∷ ℓb ↦ₚ sb)%I.

  (* NOTE: This example is currently broken since the crash condition used is
  not objective. We should use the post crash modality in the crash condition
  (maybe built in to WPC). *)
  Lemma wp_incr ℓa ℓb s n E :
    ⊢ ⎡ know_pred ℓa (λ (n : nat) v _, ⌜v = #n⌝) ⎤ -∗
      ⎡ know_pred ℓb (λ (n : nat) v hG, ⌜v = #n⌝ ∗ know_flush_lb ℓa n) ⎤ -∗
      ℓa ↦ₚ [0] -∗
      ℓb ↦ₚ [0] -∗
      WPC (incr_both ℓa ℓb) @ s; n; E
        {{ λ _, ℓa ↦ₚ [0; 1] ∗ ℓb ↦ₚ [0; 1] }}
        {{ <PC> _, crash_condition ℓa ℓb }}.
  Proof.
    iIntros "#pred1 #pred2 aPts bPts".
    rewrite /incr_both.

    (* The first store *)
    wpc_bind (_ <- _)%E.
    iApply wpc_atomic_no_mask.
    iSplit. {
      iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }
    iApply (wp_store_ex with "[$aPts]").
    { reflexivity. }
    { suff leq : (0 ≤ 1); first apply leq. lia. }
    { iFrame "pred1". done. }
    simpl.
    iNext. iIntros "aPts".
    iSplit. {
      iModIntro.
      iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }
    iModIntro.
    wpc_pures.
    { iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }

    (* The write back *)
    wpc_bind (WB _)%E.
    iApply wpc_atomic_no_mask.
    iSplit. {
      iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }
    iApply (wp_wb_ex with "aPts"); first reflexivity.
    iNext.
    iIntros "[aPts afterFence]".
    iSplit. {
      iClear "afterFence". (* FIXME: [iModIntro] spins in the absence of this. *)
      iModIntro.
      iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }
    iModIntro.
    wpc_pures.
    { iClear "afterFence". (* FIXME: [iModIntro] spins in the absence of this. *)
      iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }

    (* The fence. *)
    wpc_bind (Fence)%E.
    iApply wpc_atomic_no_mask.
    iSplit. {
      iClear "afterFence". (* FIXME: [iModIntro] spins in the absence of this. *)
      iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }
    iApply (wp_fence with "afterFence").
    iNext.
    iIntros "#pLowerBound".
    iSplit. {
      iModIntro.
      iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }
    iModIntro.
    wpc_pures.
    {
      iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }

    (* The last store *)
    iApply wpc_atomic_no_mask.
    iSplit.
    { iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }
    iApply (wp_store_ex with "[$bPts]").
    { reflexivity. }
    { suff leq : (0 ≤ 1); first apply leq. lia. }
    { iFrame "#". iFrame "pLowerBound". done. }
    iNext. iIntros "bPts".
    iSplit. {
      iModIntro.
      iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }
    iModIntro.
    iFrame "aPts bPts".
  Qed.

  Lemma wpc_recover `{hD : nvmDeltaG Σ} ℓa ℓb s k E :
    crash_condition ℓa ℓb -∗
    WPC recover ℓa ℓb
      @ s; k; E
      {{ _, True }}
      {{ <PC> H0, crash_condition ℓa ℓb }}.
  Proof.
    iNamed 1. iNamed "pts".
    rewrite /recover.
    iDestruct (mapsto_ex_last with "aPts") as %[sA saEq].
    iDestruct (mapsto_ex_last with "bPts") as %[sB sbEq].

    (* Load [ℓa]. *)
    wpc_bind (! _)%E.
    iApply wpc_atomic_no_mask.
    iSplit. {
      iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }
    iDestruct "pred1" as "#pred1".
    iDestruct "pred2" as "#pred2".
    iApply (wp_load_ex _ _ _ _ (λ v, ⌜v = #sA⌝)%I with "[$aPts $pred1]"); first done.
    { iModIntro. naive_solver. }
    iIntros "!>" (?) "[aPts ->]".
    iSplit.
    { iModIntro.
      iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }

    iModIntro.
    wpc_pures.
    { iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }

    (* Load [ℓb]. *)
    wpc_bind (! _)%E.
    iApply wpc_atomic_no_mask.
    iSplit. {
      iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }
    iDestruct "pred1" as "#pred1".
    iDestruct "pred2" as "#pred2".
    iApply (wp_load_ex _ _ _ _ (λ v, ⌜v = #sB⌝ ∗ know_flush_lb ℓa sB)%I
              with "[$bPts $pred2]"); first done.
    { iModIntro. iIntros (?) "[-> hi]". naive_solver. }
    iIntros "!>" (?) "(bPts & -> & lub)".
    iSplit.
    { iModIntro.
      iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }

    iModIntro.
    wpc_pures.
    { iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }

    iDestruct (mapsto_ex_flush_lb_incl with "lub aPts") as %incl; first done.
    rewrite bool_decide_eq_false_2.
    2: { rewrite subseteq_nat_le in incl. lia. }

    wpc_pures.
    { iDestruct "pred1" as "-#pred1". iDestruct "pred2" as "-#pred2".
      iCrash.
      iDestruct "aPts" as (? ?) "[aPts recA]".
      iDestruct "bPts" as (? ?) "[bPts recB]".
      iDestruct (recovered_at_or_lost with "recA pred1") as "pred1".
      iDestruct (recovered_at_or_lost with "recB pred2") as "pred2".
      iFrame. iExists _, _. iFrame. }

    iModIntro. done.
  Qed.

  (* FIXME: Hoare triples don't work as Perennial's Hoare triples are tied to iProp. *)
  (* Lemma wpc_incr' (ℓa ℓb : loc) : *)
  (*   {{{ (True : dProp Σ) }}} *)
  (*     incr_both ℓa ℓb @ 10; ⊤ *)
  (*   {{{ RET #(); (True : dProp Σ) }}}. *)

  (* Lemma wpc_incr (ℓa ℓb : loc) : *)
  (*   {{{ (True : dProp Σ) }}} *)
  (*     incr_both ℓa ℓb @ 10; ⊤ *)
  (*   {{{ RET #(); (True : dProp Σ) }}} *)
  (*   {{{ (True : dProp Σ) }}}. *)

  Lemma incr_safe s k E ℓa ℓb :
    ⊢ ⎡ know_pred ℓa (λ (n : nat) v _, ⌜v = #n⌝) ⎤ -∗
      ⎡ know_pred ℓb (λ (n : nat) v hG, ⌜v = #n⌝ ∗ know_flush_lb ℓa n) ⎤ -∗
      ℓa ↦ₚ [0] -∗
      ℓb ↦ₚ [0] -∗
      wpr s k E (incr_both ℓa ℓb) (recover ℓa ℓb)
        (λ _, ℓa ↦ₚ [0; 1] ∗ ℓb ↦ₚ [0; 1]) (λ _ _, True%I).
  Proof.
    iIntros "a b c d".
    iApply (idempotence_wpr _ _ _ _ _ _ _ (λ _, <PC> _, crash_condition ℓa ℓb)%I with "[a b c d] []").
    { iApply (wp_incr _ _ s k E with "a b c d"). }
    do 2 iModIntro.
    iIntros (hG') "R".
    iNext.
    iCrash.
    iApply (wpc_recover with "R").
  Qed.

End simple_increment.
