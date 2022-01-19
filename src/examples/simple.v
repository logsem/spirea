From iris.proofmode Require Import tactics.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances.
From self.high Require Import proofmode wpc_proofmode.
From self.high Require Import dprop resources crash_weakestpre weakestpre
     weakestpre_na recovery_weakestpre lifted_modalities modalities
     post_crash_modality protocol no_buffer.

Definition prog : expr := let: "l" := ref_NA #1 in ! "l".

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

  (* Predicate used for the location [a]. *)
  Definition ϕa : loc_pred (Σ := Σ) nat := λ n v _, ⌜v = #n⌝%I.

  Program Instance : LocationProtocol ϕa := { bumper n := n }.
  Next Obligation. iIntros. by iApply post_crash_flush_pure. Qed.
  Next Obligation. iIntros (????). iApply no_buffer_pure. done. Qed.

  (* Predicate used for the location [b]. *)
  Definition ϕb (ℓa : loc) : loc_pred (Σ := Σ) nat :=
    λ n v _, (⌜v = #n⌝ ∗ ∃ m, ⌜ n ≤ m ⌝ ∗ know_flush_lb ℓa m)%I.

  Program Instance protocol_b ℓa : LocationProtocol (ϕb ℓa) := { bumper n := n }.
  Next Obligation.
    iIntros (????) "[% lb]".
    iDestruct "lb" as (m ?) "lb".
    iCrashFlush.
    iDestruct "lb" as (??) "(_ & H & _)".
    iPureGoal; first done.
    iExists _. iFrame .
    iPureIntro. etrans; done.
  Qed.
  Next Obligation.
    iIntros (????). iIntros "[? (% & H1 & H2)]". iModIntro. iFrame. naive_solver.
  Qed.

  Definition crash_condition {hD : nvmDeltaG Σ} ℓa ℓb : dProp Σ :=
    ("#aPred" ∷ know_protocol ℓa ϕa ∗
     "#bPred" ∷ know_protocol ℓb (ϕb ℓa) ∗
     "pts" ∷ ∃ (sa sb : list nat), "aPts" ∷ ℓa ↦ₚ sa ∗ "bPts" ∷ ℓb ↦ₚ sb)%I.

  Lemma prove_crash_condition {hD : nvmDeltaG Σ} ℓa ℓb (ssA ssB : list nat) :
    know_protocol ℓa ϕa -∗
    know_protocol ℓb (ϕb ℓa) -∗
    ℓa ↦ₚ ssA -∗
    ℓb ↦ₚ ssB -∗
    <PC> hG, crash_condition ℓa ℓb.
  Proof.
    iIntros "aPred bPred aPts bPts".
    iCrash.
    iDestruct "aPts" as (sA ?) "[aPts recA]".
    iDestruct "bPts" as (sB ?) "[bPts recB]".
    iDestruct (recovered_at_or_lost with "recA aPred") as "aPred".
    iDestruct (recovered_at_or_lost with "recB bPred") as "bPred".
    iFrame "aPred bPred". iExists [sA], [sB]. iFrame "aPts bPts".
  Qed.

  (* NOTE: This example is currently broken since the crash condition used is
  not objective. We should use the post crash modality in the crash condition
  (maybe built in to WPC). *)
  Lemma wp_incr ℓa ℓb s E :
    ⊢ know_protocol ℓa ϕa -∗
      know_protocol ℓb (ϕb ℓa) -∗
      ℓa ↦ₚ [0] -∗
      ℓb ↦ₚ [0] -∗
      WPC (incr_both ℓa ℓb) @ s; E
        {{ λ _, ℓa ↦ₚ [0; 1] ∗ ℓb ↦ₚ [0; 1] }}
        {{ <PC> _, crash_condition ℓa ℓb }}.
  Proof.
    iIntros "#aPred #bPred aPts bPts".
    rewrite /incr_both.

    (* The first store *)
    wpc_bind (_ <- _)%E.
    iApply wpc_atomic_no_mask.
    iSplit. { iApply (prove_crash_condition with "aPred bPred aPts bPts"). }
    iApply (@wp_store_na with "[$aPts $aPred]").
    { reflexivity. }
    { suff leq : (0 ≤ 1); first apply leq. lia. }
    { done. }
    simpl.
    iNext. iIntros "aPts".
    iSplit. { iModIntro. iApply (prove_crash_condition with "aPred bPred aPts bPts"). }
    iModIntro.
    wpc_pures.
    { iApply (prove_crash_condition with "aPred bPred aPts bPts"). }

    (* The write back *)
    wpc_bind (WB _)%E.
    iApply wpc_atomic_no_mask.
    iSplit. { iApply (prove_crash_condition with "aPred bPred aPts bPts"). }
    iApply (wp_wb_ex with "aPts"); first reflexivity.
    iNext.
    iIntros "[aPts afterFence]".
    iSplit; first iApply (prove_crash_condition with "aPred bPred aPts bPts").
    iModIntro.
    wpc_pures.
    { iApply (prove_crash_condition with "aPred bPred aPts bPts"). }

    (* The fence. *)
    wpc_bind (Fence)%E.
    iApply wpc_atomic_no_mask.
    iSplit; first iApply (prove_crash_condition with "aPred bPred aPts bPts").
    iApply (wp_fence with "afterFence").
    iNext.
    iIntros "#pLowerBound".
    iSplit. {
      iModIntro. iApply (prove_crash_condition with "aPred bPred aPts bPts"). }
    iModIntro.
    wpc_pures. { iApply (prove_crash_condition with "aPred bPred aPts bPts"). }

    (* The last store *)
    iApply wpc_atomic_no_mask.
    iSplit. { iApply (prove_crash_condition with "aPred bPred aPts bPts"). }
    iApply (wp_store_na _ _ _ _ _ _ (ϕb _) with "[$bPts]").
    { reflexivity. }
    { suff leq : (0 ≤ 1); first apply leq. lia. }
    { iFrame "#". iPureGoal; first done. naive_solver. }
    iNext. iIntros "bPts".
    iSplit.
    { iModIntro. iApply (prove_crash_condition with "aPred bPred aPts bPts"). }
    iModIntro.
    iFrame "aPts bPts".
  Qed.

  Lemma wpc_recover `{hD : nvmDeltaG Σ} ℓa ℓb s E :
    crash_condition ℓa ℓb -∗
    WPC recover ℓa ℓb @ s; E
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
    iSplit; first iApply (prove_crash_condition with "aPred bPred aPts bPts").

    iApply (wp_load_na _ _ sa _ (λ v, ⌜v = #sA⌝)%I with "[$aPts $aPred]"); first done.
    { iModIntro. naive_solver. }
    iIntros "!>" (?) "[aPts ->]".
    iSplit.
    { iModIntro. iApply (prove_crash_condition with "aPred bPred aPts bPts"). }

    iModIntro.
    wpc_pures.
    { iApply (prove_crash_condition with "aPred bPred aPts bPts"). }

    (* Load [ℓb]. *)
    wpc_bind (! _)%E.
    iApply wpc_atomic_no_mask.
    iSplit; first iApply (prove_crash_condition with "aPred bPred aPts bPts").
    iApply (wp_load_na _ _ sb _ (λ v, ∃ sB', ⌜ sB ⊑ sB' ⌝ ∗ ⌜v = #sB⌝ ∗ know_flush_lb ℓa sB')%I
              with "[$bPts $bPred]"); first done.
    { iModIntro. iIntros (?) "(-> & (%sB' & % & #?))".
      iSplit. { iExists _. iFrame "#". naive_solver. }
      rewrite /ϕb. iFrame "#". naive_solver. }
    iIntros "!>" (?) "(bPts & (%sB' & %incl2 & -> & lub))".
    iSplit.
    { iModIntro. iApply (prove_crash_condition with "aPred bPred aPts bPts"). }

    iModIntro.
    wpc_pures; first iApply (prove_crash_condition with "aPred bPred aPts bPts").

    iDestruct (mapsto_ex_flush_lb_incl with "lub aPts") as %incl; first done.
    rewrite bool_decide_eq_false_2.
    2: { rewrite subseteq_nat_le in incl. rewrite subseteq_nat_le in incl2. lia. }

    wpc_pures; first iApply (prove_crash_condition with "aPred bPred aPts bPts").

    by iModIntro.
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

  Lemma incr_safe s E ℓa ℓb :
    ⊢ know_protocol ℓa ϕa -∗
      know_protocol ℓb (ϕb ℓa) -∗
      ℓa ↦ₚ [0] -∗
      ℓb ↦ₚ [0] -∗
      wpr s E (incr_both ℓa ℓb) (recover ℓa ℓb)
        (λ _, ℓa ↦ₚ [0; 1] ∗ ℓb ↦ₚ [0; 1]) (λ _ _, True%I).
  Proof.
    iIntros "a b c d".
    iApply (idempotence_wpr _ _ _ _ _ _ (λ _, <PC> _, crash_condition ℓa ℓb)%I
              with "[a b c d] []").
    { iApply (wp_incr _ _ s E with "a b c d"). }
    do 2 iModIntro.
    iIntros (hG') "R".
    iNext.
    iCrash.
    iApply (wpc_recover with "R").
  Qed.

End simple_increment.
