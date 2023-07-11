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

  Definition incr_both (ℓx ℓy : loc) : expr :=
    #ℓx <-_NA #37 ;;
    Flush #ℓx ;;
    Fence ;;
    #ℓy <-_NA #1.

  Definition recover (ℓx ℓy : loc) : expr :=
    if: (!_NA #ℓy) = #1
    then assert: (!_NA #ℓx = #37)
    else #().

End program.

(* This is a simple example with a flush and a fence. *)
Section specification.
  Context `{nvmG Σ}.

  (* After a crash the following is possible: [a = 0, b = 0], [a = 37, b = 0],
  and [a = 37, b = 1]. The case that is _not_ possible is: [a = 0, b = 1]. *)

  (* Predicate used for the location [a]. *)
  Definition ϕx : LocationProtocol bool :=
    {| p_inv := λ (σ : bool) v, ⌜σ = false ∧ v = #0 ∨ (σ = true ∧ v = #37)⌝%I;
       p_bumper n := n |}.

  Global Instance ϕx_conditions : ProtocolConditions ϕx.
  Proof. split; try apply _. iIntros. by iApply post_crash_flush_pure. Qed.

  (* Predicate used for the location [b]. *)
  Definition ϕy ℓx : LocationProtocol bool :=
    {| p_inv := λ (σ : bool) v,
        (⌜ σ = false ∧ v = #0 ⌝ ∨ ⌜ σ = true ∧ v = #1 ⌝ ∗ flush_lb ℓx ϕx true)%I;
       p_bumper n := n |}.

  Global Instance ϕy_conditions ℓx : ProtocolConditions (ϕy ℓx).
  Proof.
    split; [apply _| apply _| ].
    iIntros (??) "I !>".
    iDestruct "I" as "[(-> & ->)|(%eq & lb & _)]".
    - iLeft. done.
    - iRight. iDestruct (persist_lb_to_flush_lb with "lb") as "$". done.
  Qed.

  Definition crash_condition ℓx ℓy : dProp Σ :=
    ("pts" ∷ ∃ (na nb : bool),
      "aPer" ∷ persist_lb ℓx ϕx na ∗
      "bPer" ∷ persist_lb ℓy (ϕy ℓx) nb ∗
      "aPts" ∷ ℓx ↦_{ϕx} [na] ∗
      "yPts" ∷ ℓy ↦_{ϕy ℓx} [nb])%I.

  Lemma prove_crash_condition ℓx ℓy na nb (ssA ssB : list bool) :
    (* We need to know that both lists are strictly increasing list. *)
    ((∃ n, ssA = [n]) ∨ ssA = [false; true]) →
    ((∃ m, ssB = [m]) ∨ ssB = [false; true]) →
    persist_lb ℓx ϕx na -∗
    persist_lb ℓy (ϕy ℓx) nb -∗
    ℓx ↦_{ϕx} ssA -∗
    ℓy ↦_{ϕy ℓx} ssB -∗
    <PC> crash_condition ℓx ℓy.
  Proof.
    iIntros (ssAEq ssBEq) "perA perB aPts yPts".
    iModIntro.
    iDestruct "perA" as "[perA (% & ? & #recA)]".
    iDestruct "perB" as "[perB (% & ? & #recB)]".
    iDestruct (crashed_in_if_rec with "recA aPts") as (?? prefA) "[recA' ptsA]".
    iDestruct (crashed_in_agree with "recA recA'") as %<-.
    iDestruct (crashed_in_if_rec with "recB yPts") as (?? prefB) "[recB' ptsB]".
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
    iApply (prove_crash_condition with "aPer bPer aPts yPts");
      naive_solver.

  Lemma wp_incr_both ℓx ℓy s E :
    ⊢ persist_lb ℓx ϕx false -∗
      persist_lb ℓy (ϕy ℓx) false -∗
      ℓx ↦_{ϕx} [false] -∗
      ℓy ↦_{ϕy ℓx} [false] -∗
      WPC (incr_both ℓx ℓy) @ s; E
        {{ λ _, ℓx ↦_{ϕx} [false; true] ∗ ℓy ↦_{ϕy ℓx} [false; true] }}
        {{ <PC> crash_condition ℓx ℓy }}.
  Proof.
    iIntros "#aPer #bPer aPts yPts".
    rewrite /incr_both.

    (* The first store *)
    wpc_bind (_ <-_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit; first solve_cc.
    iApply (wp_store_na _ _ _ _ _ true with "[$aPts]").
    { reflexivity. }
    { done. }
    { naive_solver. }
    simpl.
    iNext. iIntros "aPts".
    iSplit; first solve_cc.
    iModIntro.
    wpc_pures; first solve_cc.

    (* The write back *)
    wpc_bind (Flush _)%E.
    iApply wpc_atomic_no_mask.
    iSplit; first solve_cc.
    iApply (wp_flush_na _ _ _ _ [false] with "[$aPts]").
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
    iApply (wp_store_na _ _ _ _ _ true with "[$yPts]").
    { reflexivity. }
    { done. }
    { iRight. iFrame "#". done. }
    iNext. iIntros "yPts".
    iSplit; first solve_cc.
    iModIntro.
    iFrame "aPts yPts".
  Qed.

  Lemma wpc_recover ℓx ℓy s E :
    crash_condition ℓx ℓy -∗
    WPC recover ℓx ℓy @ s; E
      {{ _, True }}
      {{ <PC> crash_condition ℓx ℓy }}.
  Proof.
    iNamed 1.
    rewrite /recover.
    (* iDestruct (mapsto_na_last with "aPts") as %[sA saEq]. *)
    (* iDestruct (mapsto_na_last with "yPts") as %[sB sbEq]. *)

    (* Load [ℓy]. *)
    wpc_bind (!_NA _)%E.
    iApply wpc_atomic_no_mask.

    iSplit; first solve_cc.

    iApply (wp_load_na _ _ _ _ ((ϕy ℓx).(p_inv) nb)%I
              with "[$yPts]"); first done.
    { iIntros "!>" (?) "#I". iFrame "I". }
    iIntros "!>" (?) "(yPts & I)".
    iSplit; first solve_cc.
    iModIntro.
    wpc_pures; first solve_cc.

    (* We now case on the disjunction in the invariant for [y]. *)
    iDestruct "I" as "[(-> & ->)|([-> ->] & lb)]".
    { rewrite bool_decide_eq_false_2; last done.
      wpc_pures; first solve_cc.
      iModIntro. done. }
    unfold assert.
    wpc_pures; first solve_cc.
    iDestruct (mapsto_na_flush_lb_incl [] with "lb aPts") as %incl.
    replace na with true.

    (* Load [ℓx]. *)
    wpc_bind (!_NA _)%E.
    iApply wpc_atomic_no_mask. iSplit; first solve_cc.
    iApply (wp_load_na _ _ _ _ (λ v, ⌜v = #37⌝)%I with "[$aPts]"); first done.
    { iIntros "!>" (?) "[(% & %)|(% & %)]"; naive_solver. }
    iIntros "!>" (?) "[aPts ->]".
    iSplit; first solve_cc.

    iModIntro.
    wpc_pures; first solve_cc.
    iModIntro.
    done.
  Qed.

  Lemma incr_safe s E ℓx ℓy :
    ⊢ persist_lb ℓx ϕx false -∗
      persist_lb ℓy (ϕy ℓx) false -∗
      ℓx ↦_{ϕx} [false] -∗
      ℓy ↦_{ϕy ℓx} [false] -∗
      wpr s E (incr_both ℓx ℓy) (recover ℓx ℓy)
        (λ _, ℓx ↦_{ϕx} [false; true] ∗ ℓy ↦_{ϕy ℓx} [false; true]) (λ _, True%I).
  Proof.
    iIntros "a b c d".
    iApply (idempotence_wpr _ _ _ _ _ _ (<PC> crash_condition ℓx ℓy)%I
              with "[a b c d] []").
    { iApply (wp_incr_both _ _ s E with "a b c d"). }
    iModIntro. iModIntro.
    iIntros "R".
    iModIntro.
    iApply (wpc_recover with "R").
  Qed.

End specification.

(* We now create a closed proof. *)

Definition init_heap ℓx ℓy : gmap loc val := {[ ℓx := #0; ℓy := #0 ]}.

Lemma incr_safe_proof ℓx ℓy :
  ℓx ≠ ℓy →
  recv_adequate NotStuck
                (incr_both ℓx ℓy `at` ⊥)
                (recover ℓx ℓy `at` ⊥)
                (initial_heap (init_heap ℓx ℓy),
                  const (MaxNat 0) <$> (init_heap ℓx ℓy))
                (λ v _, True) (λ v _, True).
Proof.
  intros neq.
  eapply (high_recv_adequacy_2 nvmΣ _ _ _ (λ _, True) (λ _, True) 0
                               (init_heap ℓx ℓy)
                               ({[ ℓx; ℓy ]})
                               ∅).
  { set_solver. }
  { set_solver. }
  iIntros (nD).
  set (ℓx_lif := {| loc_state := bool; loc_init := false; loc_prot := ϕx |}).
  set (ℓy_lif := {| loc_state := bool; loc_init := false; loc_prot := ϕy ℓx |}).
  set (lif := {[ℓx := ℓx_lif; ℓy := ℓy_lif ]} : gmap loc loc_info).
  exists lif.
  rewrite /lif.
  split; first set_solver.
  iIntros "M _ _".
  setoid_rewrite (restrict_id {[ℓx; ℓy]}); last set_solver.
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
  { simpl. iSplitPure; naive_solver. }

  iApply (wpr_mono with "[ptsA ptsB]").
  { iApply (incr_safe with "pa pb ptsA ptsB"). }
  iSplit.
  - iIntros. done.
  - iModIntro. done.
Qed.

(* Uncomment the next line to see that the proof is truly closed. *)
(* Print Assumptions incr_safe_proof. *)
