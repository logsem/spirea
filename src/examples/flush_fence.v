From iris.proofmode Require Import tactics.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances.
From self.base Require Import adequacy. (* To get [recv_adequace]. *)
From self.high Require Import proofmode wpc_proofmode.
From self.high Require Import dprop resources crash_weakestpre weakestpre
     weakestpre_na recovery_weakestpre lifted_modalities modalities
     post_crash_modality protocol no_buffer abstract_state_instances locations protocol adequacy.
From self.high.modalities Require Import fence.

Section program.

  Definition incr_both (ℓa ℓb : loc) : expr :=
    #ℓa <-_NA #1 ;;
    Flush #ℓa ;;
    Fence ;;
    #ℓb <-_NA #1.

  Definition recover (ℓa ℓb : loc) : expr :=
    let: "a" := !_NA #ℓa in
    let: "b" := !_NA #ℓb in
    if: "a" < "b"
    then #() #() (* Get stuck. *)
    else #().

End program.

(* This is a simple example with a flush and a fence. *)
Section specification.
  Context `{nvmG Σ}.

  (* After a crash the following is possible: [a = 0, b = 0], [a = 1, b = 0],
  and [a = 1, b = 1]. The case that is _not_ possible is: [a = 0, b = 1]. *)

  (* Predicate used for the location [a]. *)
  Definition ϕa : LocationProtocol nat :=
    {| p_inv := λ (n : nat) v, ⌜v = #n⌝%I;
       p_bumper n := n |}.

  Global Instance ϕa_conditions : ProtocolConditions ϕa.
  Proof. split; try apply _. iIntros. by iApply post_crash_flush_pure. Qed.

  (* Predicate used for the location [b]. *)
  Definition ϕb ℓa : LocationProtocol nat :=
    {| p_inv := λ (n : nat) v, (⌜v = #n⌝ ∗ ∃ m, ⌜ n ≤ m ⌝ ∗ flush_lb ℓa ϕa m)%I;
       p_bumper n := n |}.

  Global Instance ϕb_conditions ℓa : ProtocolConditions (ϕb ℓa).
    split; try apply _.
    iIntros (??) "[% lb]".
    iDestruct "lb" as (m ?) "lb".
    iModIntro.
    iDestruct "lb" as "[H ?]".
    iSplitPure; first done.
    iExists _.
    iDestruct (persist_lb_to_flush_lb with "H") as "$".
    iPureIntro. etrans; done.
  Qed.

  Definition crash_condition ℓa ℓb : dProp Σ :=
    ("pts" ∷ ∃ (na nb : nat),
      "aPer" ∷ persist_lb ℓa ϕa na ∗
      "bPer" ∷ persist_lb ℓb (ϕb ℓa) nb ∗
      "aPts" ∷ ℓa ↦_{ϕa} [na] ∗
      "bPts" ∷ ℓb ↦_{ϕb ℓa} [nb])%I.

  Lemma prove_crash_condition ℓa ℓb na nb (ssA ssB : list nat) :
    (* We need to know that both lists are strictly increasing list. *)
    ((∃ n, ssA = [n]) ∨ ssA = [0; 1]) →
    ((∃ m, ssB = [m]) ∨ ssB = [0; 1]) →
    persist_lb ℓa ϕa na -∗
    persist_lb ℓb (ϕb ℓa) nb -∗
    ℓa ↦_{ϕa} ssA -∗
    ℓb ↦_{ϕb ℓa} ssB -∗
    <PC> crash_condition ℓa ℓb.
  Proof.
    iIntros (ssAEq ssBEq) "perA perB aPts bPts".
    iModIntro.
    iDestruct "perA" as "[perA (% & ? & #recA)]".
    iDestruct "perB" as "[perB (% & ? & #recB)]".
    iDestruct (crashed_in_if_rec with "recA aPts") as (?? prefA) "[recA' ptsA]".
    iDestruct (crashed_in_agree with "recA recA'") as %<-.
    iDestruct (crashed_in_if_rec with "recB bPts") as (?? prefB) "[recB' ptsB]".
    iDestruct (crashed_in_agree with "recB recB'") as %<-.
    iExistsN.
    iDestruct (crashed_in_persist_lb with "recA'") as "$".
    iDestruct (crashed_in_persist_lb with "recB'") as "$".
    rewrite !list_fmap_id.
    simpl.
    iSplitL "ptsA".
    - destruct ssAEq as [[? ->] | ->].
      * apply prefix_app_singleton in prefA as [-> ->].
        iFrame "ptsA".
      * apply prefix_app_two in prefA as [[-> ->] | [-> ->]];
          first iFrame "ptsA".
        iDestruct (crashed_in_persist_lb with "recA") as "P".
        iApply (mapsto_na_persist_lb with "ptsA P").
        simpl.
        rewrite /sqsubseteq.
        lia.
    - destruct ssBEq as [[? ->] | ->].
      * apply prefix_app_singleton in prefB as [-> ->].
        iFrame.
      * apply prefix_app_two in prefB as [[-> ->] | [-> ->]];
          first iFrame "ptsB".
        iDestruct (crashed_in_persist_lb with "recB") as "P".
        iApply (mapsto_na_persist_lb with "ptsB P").
        simpl.
        rewrite /sqsubseteq.
        lia.
  Qed.

  Ltac solve_cc :=
    try iModIntro (|={_}=> _)%I;
    iApply (prove_crash_condition with "aPer bPer aPts bPts");
      naive_solver.

  Lemma wp_incr_both ℓa ℓb s E :
    ⊢ persist_lb ℓa ϕa 0 -∗
      persist_lb ℓb (ϕb ℓa) 0 -∗
      ℓa ↦_{ϕa} [0] -∗
      ℓb ↦_{ϕb ℓa} [0] -∗
      WPC (incr_both ℓa ℓb) @ s; E
        {{ λ _, ℓa ↦_{ϕa} [0; 1] ∗ ℓb ↦_{ϕb ℓa} [0; 1] }}
        {{ <PC> crash_condition ℓa ℓb }}.
  Proof.
    iIntros "#aPer #bPer aPts bPts".
    rewrite /incr_both.

    (* The first store *)
    wpc_bind (_ <-_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit; first solve_cc.
    iApply (@wp_store_na with "[$aPts]").
    { reflexivity. }
    { suff leq : (0 ≤ 1); first apply leq. lia. }
    { done. }
    simpl.
    iNext. iIntros "aPts".
    iSplit; first solve_cc.
    iModIntro.
    wpc_pures; first solve_cc.

    (* The write back *)
    wpc_bind (Flush _)%E.
    iApply wpc_atomic_no_mask.
    iSplit; first solve_cc.
    iApply (wp_flush_na _ _ _ _ [0] with "[$aPts]").
    iNext.
    iIntros "(aPts & #pLowerBound & _)".
    iSplit; first solve_cc.
    iModIntro.
    wpc_pures; first solve_cc.

    (* The fence. *)
    wpc_bind (Fence)%E.
    iApply wpc_atomic_no_mask.
    iSplit; first solve_cc.
    iApply wp_fence. iModIntro. iModIntro.
    iSplit; first solve_cc.
    iModIntro.
    wpc_pures; first solve_cc.

    (* The last store *)
    iApply wpc_atomic_no_mask.
    iSplit; first solve_cc.
    iApply (wp_store_na with "[$bPts]").
    { reflexivity. }
    { suff leq : (0 ≤ 1); first apply leq. lia. }
    { iFrame "#". iPureGoal; first done. naive_solver. }
    iNext. iIntros "bPts".
    iSplit; first solve_cc.
    iModIntro.
    iFrame "aPts bPts".
  Qed.

  Lemma wpc_recover ℓa ℓb s E :
    crash_condition ℓa ℓb -∗
    WPC recover ℓa ℓb @ s; E
      {{ _, True }}
      {{ <PC> crash_condition ℓa ℓb }}.
  Proof.
    iNamed 1.
    rewrite /recover.
    (* iDestruct (mapsto_na_last with "aPts") as %[sA saEq]. *)
    (* iDestruct (mapsto_na_last with "bPts") as %[sB sbEq]. *)

    (* Load [ℓa]. *)
    wpc_bind (!_NA _)%E.
    iApply wpc_atomic_no_mask.

    iSplit; first solve_cc.

    iApply (wp_load_na _ _ _ _ (λ v, ⌜v = #na⌝)%I with "[$aPts]"); first done.
    { iModIntro. naive_solver. }
    iIntros "!>" (?) "[aPts ->]".
    iSplit; first solve_cc.

    iModIntro.
    wpc_pures; first solve_cc.

    (* Load [ℓb]. *)
    wpc_bind (!_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit; first solve_cc.
    iApply (wp_load_na _ _ _ _ (λ v, ∃ nb', ⌜ nb ⊑ nb' ⌝ ∗ ⌜v = #nb⌝ ∗ flush_lb ℓa _ nb')%I
              with "[$bPts]"); first done.
    { iModIntro. iIntros (?) "(-> & (%sB' & % & #?))".
      iSplit. { iExists _. iFrame "#". naive_solver. }
      rewrite /ϕb. iFrame "#". naive_solver. }
    iIntros "!>" (?) "(bPts & (%sB' & %incl2 & -> & lub))".
    iSplit; first solve_cc.

    iModIntro.
    wpc_pures; first solve_cc.

    iDestruct (mapsto_na_flush_lb_incl [] with "lub aPts") as %incl.
    rewrite bool_decide_eq_false_2.
    2: { rewrite subseteq_nat_le in incl. rewrite subseteq_nat_le in incl2. lia. }

    wpc_pures; first solve_cc.

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
    ⊢ persist_lb ℓa ϕa 0 -∗
      persist_lb ℓb (ϕb ℓa) 0 -∗
      ℓa ↦_{ϕa} [0] -∗
      ℓb ↦_{ϕb ℓa} [0] -∗
      wpr s E (incr_both ℓa ℓb) (recover ℓa ℓb)
        (λ _, ℓa ↦_{ϕa} [0; 1] ∗ ℓb ↦_{ϕb ℓa} [0; 1]) (λ _, True%I).
  Proof.
    iIntros "a b c d".
    iApply (idempotence_wpr _ _ _ _ _ _ (<PC> crash_condition ℓa ℓb)%I
              with "[a b c d] []").
    { iApply (wp_incr_both _ _ s E with "a b c d"). }
    iModIntro. iModIntro.
    iIntros "R".
    iModIntro.
    iApply (wpc_recover with "R").
  Qed.

End specification.

(* We now create a closed proof. *)

Definition init_heap ℓa ℓb : gmap loc val := {[ ℓa := #0; ℓb := #0 ]}.

Lemma incr_safe_proof ℓa ℓb :
  ℓa ≠ ℓb →
  recv_adequate NotStuck
                (incr_both ℓa ℓb `at` ⊥)
                (recover ℓa ℓb `at` ⊥)
                (initial_heap (init_heap ℓa ℓb),
                  const (MaxNat 0) <$> (init_heap ℓa ℓb))
                (λ v _, True) (λ v _, True).
Proof.
  intros neq.
  eapply (high_recv_adequacy_2 nvmΣ _ _ _ (λ _, True) (λ _, True) 0
                               (init_heap ℓa ℓb)
                               ({[ ℓa; ℓb ]})
                               ∅).
  { set_solver. }
  { set_solver. }
  iIntros (nD).
  set (ℓa_lif := {| loc_state := nat; loc_init := 0; loc_prot := ϕa |}).
  set (ℓb_lif := {| loc_state := nat; loc_init := 0; loc_prot := (ϕb ℓa) |}).
  set (lif := {[ℓa := ℓa_lif; ℓb := ℓb_lif ]} : gmap loc loc_info).
  exists lif.
  rewrite /lif.
  split; first set_solver.
  iIntros "M _ _".
  setoid_rewrite (restrict_id {[ℓa; ℓb]}); last set_solver.
  rewrite /init_heap.
  rewrite big_sepM_insert. 2: { apply lookup_singleton_ne. done. }
  iDestruct "M" as "[(% & %look & #pa & ptsA) M]".
  rewrite big_sepM_singleton.
  iDestruct "M" as "(% & %look' & #pb & ptsB)".
  simplify_eq.

  (* Simplify things. *)
  rewrite lookup_insert in look.
  rewrite lookup_insert_ne in look'; last done.
  rewrite lookup_insert in look'.
  simplify_eq /=.
  rewrite big_sepM2_insert; try (apply lookup_singleton_ne; done).
  rewrite big_sepM2_singleton.

  iSplit.
  { simpl.
    iSplitPure; first done. iSplitPure; first done.
    iExists 0. iSplitPure; first done.
    iApply persist_lb_to_flush_lb. iApply "pa". }

  iApply (wpr_mono with "[ptsA ptsB]").
  { iApply (incr_safe with "pa pb ptsA ptsB"). }
  iSplit.
  - iIntros. done.
  - iModIntro. done.
Qed.

(* Print Assumptions incr_safe_proof. *)
