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
  Context `{nvmG Σ, nvmDeltaG}.

  (* After a crash the following is possible: [a = 0, b = 0], [a = 1, b = 0],
  and [a = 1, b = 1]. The case that is _not_ possible is: [a = 0, b = 1]. *)

  (* Predicate used for the location [a]. *)
  Program Definition ϕa : LocationProtocol nat :=
    {| pred := λ n v _, ⌜v = #n⌝%I;
       bumper n := n |}.
  Next Obligation. iIntros. by iApply post_crash_flush_pure. Qed.

  (* Predicate used for the location [b]. *)
  Program Definition ϕb ℓa : LocationProtocol nat :=
    {| pred := λ n v _, (⌜v = #n⌝ ∗ ∃ m, ⌜ n ≤ m ⌝ ∗ flush_lb ℓa ϕa m)%I;
       bumper n := n |}.
  Next Obligation.
    iIntros (????) "[% lb]".
    iDestruct "lb" as (m ?) "lb".
    iCrashFlush.
    iDestruct "lb" as "[H ?]".
    iPureGoal; first done.
    iExists _.
    iDestruct (persist_lb_to_flush_lb with "H") as "$".
    iPureIntro. etrans; done.
  Qed.

  Definition crash_condition {hD : nvmDeltaG} ℓa ℓb : dProp Σ :=
    ("pts" ∷ ∃ nas nbs (na nb : nat),
      "lastA" ∷ ⌜ last nas = Some na ⌝ ∗
      "lastB" ∷ ⌜ last nbs = Some nb ⌝ ∗
      "aPer" ∷ persist_lb ℓa ϕa na ∗
      "bPer" ∷ persist_lb ℓb (ϕb ℓa) nb ∗
      "aPts" ∷ ℓa ↦_{ϕa} nas ∗
      "bPts" ∷ ℓb ↦_{ϕb ℓa} nbs)%I.

  Lemma prove_crash_condition {hD : nvmDeltaG} ℓa ℓb na nb (ssA ssB : list nat) :
    persist_lb ℓa ϕa na -∗
    persist_lb ℓb (ϕb ℓa) nb -∗
    ℓa ↦_{ϕa} ssA -∗
    ℓb ↦_{ϕb ℓa} ssB -∗
    <PC> hG, crash_condition ℓa ℓb.
  Proof.
    iIntros "perA perB aPts bPts".
    iCrash.
    iDestruct "perA" as "[perA (% & ? & #recA)]".
    iDestruct "perB" as "[perB (% & ? & #recB)]".
    iDestruct (crashed_in_if_rec with "recA aPts") as (????) "[recA' ptsA]".
    iDestruct (crashed_in_agree with "recA recA'") as %<-.
    iDestruct (crashed_in_if_rec with "recB bPts") as (????) "[recB' ptsB]".
    iDestruct (crashed_in_agree with "recB recB'") as %<-.
    iExistsN.
    iDestruct (crashed_in_persist_lb with "recA'") as "$".
    iDestruct (crashed_in_persist_lb with "recB'") as "$".
    rewrite !list_fmap_id.
    iFrame "%∗".
  Qed.

  Lemma wp_incr_both ℓa ℓb s E :
    ⊢ persist_lb ℓa ϕa 0 -∗
      persist_lb ℓb (ϕb ℓa) 0 -∗
      ℓa ↦_{ϕa} [0] -∗
      ℓb ↦_{ϕb ℓa} [0] -∗
      WPC (incr_both ℓa ℓb) @ s; E
        {{ λ _, ℓa ↦_{ϕa} [0; 1] ∗ ℓb ↦_{ϕb ℓa} [0; 1] }}
        {{ <PC> _, crash_condition ℓa ℓb }}.
  Proof.
    iIntros "#aPer #bPer aPts bPts".
    rewrite /incr_both.

    (* The first store *)
    wpc_bind (_ <-_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit. { iApply (prove_crash_condition with "aPer bPer aPts bPts"). }
    iApply (@wp_store_na with "[$aPts]").
    { reflexivity. }
    { suff leq : (0 ≤ 1); first apply leq. lia. }
    { done. }
    simpl.
    iNext. iIntros "aPts".
    iSplit. { iModIntro. iApply (prove_crash_condition with "aPer bPer aPts bPts"). }
    iModIntro.
    wpc_pures.
    { iApply (prove_crash_condition with "aPer bPer aPts bPts"). }

    (* The write back *)
    wpc_bind (Flush _)%E.
    iApply wpc_atomic_no_mask.
    iSplit. { iApply (prove_crash_condition with "aPer bPer aPts bPts"). }
    iApply (wp_flush_ex with "aPts"); first reflexivity.
    iNext.
    iIntros "(aPts & #pLowerBound & _)".
    iSplit; first iApply (prove_crash_condition with "aPer bPer aPts bPts").
    iModIntro.
    wpc_pures.
    { iApply (prove_crash_condition with "aPer bPer aPts bPts"). }

    (* The fence. *)
    wpc_bind (Fence)%E.
    iApply wpc_atomic_no_mask.
    iSplit; first iApply (prove_crash_condition with "aPer bPer aPts bPts").
    iApply wp_fence. iModIntro. iModIntro.
    iSplit. {
      iModIntro. iApply (prove_crash_condition with "aPer bPer aPts bPts"). }
    iModIntro.
    wpc_pures. { iApply (prove_crash_condition with "aPer bPer aPts bPts"). }

    (* The last store *)
    iApply wpc_atomic_no_mask.
    iSplit. { iApply (prove_crash_condition with "aPer bPer aPts bPts"). }
    iApply (wp_store_na with "[$bPts]").
    { reflexivity. }
    { suff leq : (0 ≤ 1); first apply leq. lia. }
    { iFrame "#". iPureGoal; first done. naive_solver. }
    iNext. iIntros "bPts".
    iSplit.
    { iModIntro. iApply (prove_crash_condition with "aPer bPer aPts bPts"). }
    iModIntro.
    iFrame "aPts bPts".
  Qed.

  Lemma wpc_recover `{hD : nvmDeltaG} ℓa ℓb s E :
    crash_condition ℓa ℓb -∗
    WPC recover ℓa ℓb @ s; E
      {{ _, True }}
      {{ <PC> H0, crash_condition ℓa ℓb }}.
  Proof.
    iNamed 1.
    rewrite /recover.
    iDestruct (mapsto_na_last with "aPts") as %[sA saEq].
    iDestruct (mapsto_na_last with "bPts") as %[sB sbEq].

    (* Load [ℓa]. *)
    wpc_bind (!_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit; first iApply (prove_crash_condition with "aPer bPer aPts bPts").

    iApply (wp_load_na _ _ _ _ (λ v, ⌜v = #sA⌝)%I with "[$aPts]"); first done.
    { iModIntro. naive_solver. }
    iIntros "!>" (?) "[aPts ->]".
    iSplit.
    { iModIntro. iApply (prove_crash_condition with "aPer bPer aPts bPts"). }

    iModIntro.
    wpc_pures.
    { iApply (prove_crash_condition with "aPer bPer aPts bPts"). }

    (* Load [ℓb]. *)
    wpc_bind (!_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit; first iApply (prove_crash_condition with "aPer bPer aPts bPts").
    iApply (wp_load_na _ _ _ _ (λ v, ∃ sB', ⌜ sB ⊑ sB' ⌝ ∗ ⌜v = #sB⌝ ∗ flush_lb ℓa _ sB')%I
              with "[$bPts]"); first done.
    { iModIntro. iIntros (?) "(-> & (%sB' & % & #?))".
      iSplit. { iExists _. iFrame "#". naive_solver. }
      rewrite /ϕb. iFrame "#". naive_solver. }
    iIntros "!>" (?) "(bPts & (%sB' & %incl2 & -> & lub))".
    iSplit.
    { iModIntro. iApply (prove_crash_condition with "aPer bPer aPts bPts"). }

    iModIntro.
    wpc_pures; first iApply (prove_crash_condition with "aPer bPer aPts bPts").

    iDestruct (mapsto_na_flush_lb_incl with "lub aPts") as %incl; first done.
    rewrite bool_decide_eq_false_2.
    2: { rewrite subseteq_nat_le in incl. rewrite subseteq_nat_le in incl2. lia. }

    wpc_pures; first iApply (prove_crash_condition with "aPer bPer aPts bPts").

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
        (λ _, ℓa ↦_{ϕa} [0; 1] ∗ ℓb ↦_{ϕb ℓa} [0; 1]) (λ _ _, True%I).
  Proof.
    iIntros "a b c d".
    iApply (idempotence_wpr _ _ _ _ _ _ (λ _, <PC> _, crash_condition ℓa ℓb)%I
              with "[a b c d] []").
    { iApply (wp_incr_both _ _ s E with "a b c d"). }
    do 2 iModIntro.
    iIntros (hG') "R".
    iCrash.
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
  intros nnD .
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
  { iApply (incr_safe with "[$] [$] ptsA ptsB"). }
  iSplit.
  - iIntros. done.
  - iModIntro. done.
Qed.
