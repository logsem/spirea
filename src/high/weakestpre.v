(* In this file we define our weakest precondition on top of the weakest
precondition included in Iris. *)

From stdpp Require Import gmap.
From iris.program_logic Require weakestpre.

From stdpp Require Import countable numbers gmap.
From iris Require Import invariants.
From iris.proofmode Require Import tactics monpred.
From iris.algebra Require Import gmap gset excl auth.
From iris.program_logic Require weakestpre.
From iris.heap_lang Require Import locations.
From iris_named_props Require Import named_props.

From self.algebra Require Export ghost_map.
From self Require Export extra ipm_tactics solve_view_le.
From self.high Require Export dprop.
From self Require Export view.
From self Require Export lang.
From self.base Require Import primitive_laws.
From self.lang Require Import syntax tactics lemmas.
From self.high Require Import resources crash_weakestpre lifted_modalities
     monpred_simpl modalities protocol locations.

Section wp.
  Context `{!nvmG Σ, nvmDeltaG}.

  Implicit Types (Φ : val → dProp Σ) (e : expr).

  (* We prove a few basic facts about our weakest precondition. *)
  Global Instance wp_ne s E e n :
    Proper (pointwise_relation _ (dist n) ==> dist n) (wp s E e).
  Proof. rewrite wp_eq. solve_proper. Qed.
  Global Instance wp_proper s E e :
    Proper (pointwise_relation val (≡) ==> (≡)) (wp s E e).
  Proof. rewrite wp_eq. solve_proper. Qed.

  (* For the WP in Iris the other direction also holds, but not for this WP *)
  Lemma wp_value_fupd' s E Φ v : (|NC={E}=> Φ v) ⊢ WP of_val v @ s; E {{ Φ }}.
  Proof.
    rewrite wp_eq /wp_def.
    iIntros "H".
    iApply wpc_value.
    iSplit.
    - iMod "H". iModIntro. done.
    - iModIntro. done.
  Qed.

  Lemma wp_bind K s E1 (e : expr) Φ :
    WP e @ s; E1 {{ v, WP fill K (of_val v) @ s; E1 {{ Φ }} }}
    ⊢ WP fill K e @ s; E1 {{ Φ }}.
  Proof. rewrite wp_eq /wp_def. iIntros "H". iApply wpc_bind. done. Qed.

  Lemma wp_value_fupd s E Φ e v :
    IntoVal e v → (|NC={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}.
  Proof. intros <-. apply wp_value_fupd'. Qed.

  (* If the expression is a value then showing the postcondition for the value
  suffices. *)
  Lemma wp_value s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
  Proof. iIntros "H". iApply wp_value_fupd'. iModIntro. iFrame. Qed.

  (* Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, fupd E E (Φ v) }} ⊢ WP e @ s; E {{ Φ }}. *)
  (* Proof. *)
  (*   (* iIntros "H". iApply (wp_strong_mono s s E with "H"); auto. by iIntros (v) ">H". Qed. *) *)

  Notation PureExecBase P nsteps e1 e2 :=
    (∀ TV, PureExec P nsteps (ThreadState e1 TV) (ThreadState e2 TV)).

  (* Upstream this to Iris. *)
  Lemma monPred_at_step_fupd i Eo Ei (P : dProp Σ) :
    (|={Eo}[Ei]▷=> P) i ⊣⊢ |={Eo}[Ei]▷=> P i.
  Proof. by rewrite monPred_at_fupd monPred_at_later monPred_at_fupd. Qed.

  Lemma monPred_at_step_fupdN E E' n (P : dProp Σ) j :
    ((|={E}[E']▷=>^n P) j ⊣⊢ (|={E}[E']▷=>^n (P j)))%I.
  Proof.
    induction n as [|n IH]; [done|]. by rewrite monPred_at_step_fupd IH.
  Qed.

  Global Instance make_monPred_at_step_fupd `{BiFUpd PROP} i E1 E2 (P : dProp Σ) 𝓟 :
    MakeMonPredAt i P 𝓟 → MakeMonPredAt i (|={E1}[E2]▷=> P)%I (|={E1}[E2]▷=> 𝓟)%I.
  Proof. by rewrite /MakeMonPredAt monPred_at_step_fupd=> <-. Qed.

  Global Instance make_monPred_at_step_fupdN `{BiFUpd PROP} i E1 E2 n (P : dProp Σ) 𝓟 :
    MakeMonPredAt i P 𝓟 → MakeMonPredAt i (|={E1}[E2]▷=>^n P)%I (|={E1}[E2]▷=>^n 𝓟)%I.
  Proof.
    rewrite /MakeMonPredAt. rewrite monPred_at_step_fupdN => h.
  Abort.
  (* rewrite h. <-. Qed. *)

  (* Note: This proof broke when [interp] was added to the recovery condition in
  the definition of our WPR. It should still be probable though. Maybe by doing
  induction in [n] and using [wpc_pure_step_fupd] from Perennial. *)
  Lemma wp_pure_step_fupd `{!Inhabited (state Λ)} s E E' e1 e2 φ n Φ :
    PureExecBase φ n e1 e2 →
    φ →
    (|={E}[E']▷=>^n WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    rewrite wp_eq /wp_def wpc_eq /wpc_def => Hexec Hφ. iStartProof (iProp _).
    simpl.
    (* iIntros (TV). *)
    iIntros (TV) "H". iIntros (TV').
    iRevert "H".
    specialize (Hexec TV' Hφ).
    iInduction n as [|n] "IH" forall (e1 TV Hexec).
    { inversion Hexec. simpl. iIntros "H". iApply "H". }
    iIntros "H % HV" .
    pose proof (Hexec) as step.
    inversion step.
    subst.
    destruct y as [e1' TV1'].
    assert (TV1' = TV'). {
      eauto using pure_step_thread_view, nsteps_pure_step_thread_view,
                  thread_view_sqsubseteq_antisym. }
    subst.
    iApply wpc_pure_step_fupd.
    { econstructor; last done. eassumption. }
    { constructor. }
    iSplit.
    2: { iFrame. done. }
    simpl.
    iApply (step_fupd_mask_mono E E E'); [set_solver|done|].
    rewrite monPred_at_step_fupd.
    iApply (step_fupd_wand with "H"). iIntros "H".
    iApply ("IH" with "[//] H [//] HV").
  Qed.

  (* This lemma is like the [wp_pure_step_later] in Iris except its premise uses
  [PureExecBase] instead of [PureExec]. *)
  Lemma wp_pure_step_later s E e1 e2 φ n Φ :
    PureExecBase φ n e1 e2 →
    φ →
    ▷^n WP e2 @ s; E {{ Φ }} ⊢ WP e1 @ s; E {{ Φ }}.
  Proof.
    intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
    induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
  Qed.

  (* This lemma "unfolds" the high-level WP into the low-level WP when the
  former is applied to a thread view. *)
  Lemma wp_unfold_at e st E (Φ : val → dProp Σ) TV1 :
    (∀ TV2, ⌜ TV1 ⊑ TV2 ⌝ -∗ validV (store_view TV2) -∗
      WP e `at` TV2 @ st; E
        {{ res,
          let '(v `at` TV3)%V := res
          in ⌜ TV2 ⊑ TV3 ⌝ ∗ validV (store_view TV3) ∗ Φ v TV3 }}) -∗
    (WP e @ st; E {{ Φ }}) TV1.
  Proof.
    iStartProof (iProp _).
    iIntros "impl".
    rewrite wp_eq /wp_def wpc_eq.
    iIntros (TV2 incl2) "#val".
    rewrite monPred_at_pure.
    iApply program_logic.crash_weakestpre.wp_wpc.
    iApply "impl". done. iAssumption.
  Qed.

End wp.

Section wp_rules.
  Context `{AbstractState ST}.
  Context `{!nvmG Σ, hG : nvmDeltaG}.

  Implicit Types (ℓ : loc) (s : ST) (ϕ : ST → val → nvmDeltaG → dProp Σ).

  Lemma last_cons (A : Type) (l : list A) (a b : A) :
    last l = Some a → last (b :: l) = Some a.
  Proof. intros Hl. induction l; [done|by rewrite -Hl]. Qed.
  Lemma last_app (A : Type) (l1 l2 : list A) (a : A) :
    last l2 = Some a → last (l1 ++ l2) = Some a.
  Proof.
    intros Hl. induction l1; [done|].
    by erewrite <- app_comm_cons, last_cons.
  Qed.

  (* FIXME: This has been committed upstream, delete later when dependencies are updated. *)
  Lemma make_monPred_at_embed2 {I : biIndex} {PROP : bi} name (i : I) P (𝓟 : PROP) :
    MakeMonPredAt i P 𝓟 →
    MakeMonPredAt i (named name P) (named name 𝓟).
  Proof. done. Qed.

  Hint Extern 0 (MakeMonPredAt _ (named _ _) _) => apply make_monPred_at_embed2 : typeclass_instances.

  (* A read-only points-to predicate. *)
  (* Definition mapsto_ro ℓ (s : ST) ϕ : dProp Σ := *)
  (*   ∃ t, monPred_in ({[ ℓ := MaxNat t ]}, ∅, ∅) ∗ *)
  (*        ⎡know_pred ℓ ϕ⎤ ∗ ⎡know_state ℓ t s⎤. *)

  (* Notation "l ↦ro s | P" := (mapsto_ro l s P) (at level 20). *)

  (* Lemma know_state_Some `{Countable ST} hists ℓ t (s : ST) : *)
  (*   own abs_history_name (● (abs_hist_to_ra_old <$> hists) : encoded_historiesR) -∗ *)
  (*   know_state ℓ t s -∗ *)
  (*   ∃ m, ⌜hists !! ℓ = Some m⌝. *)
  (* Proof. *)
  (*   iIntros "A B". *)
  (*   destruct (hists !! ℓ) as [m|] eqn:Heq. *)
  (*   { iExists m. done. } *)
  (*   iDestruct (own_valid_2 with "A B") as %[Hincl _]%auth_both_valid_discrete. *)
  (*   apply singleton_included_l' in Hincl. *)
  (*   move: Hincl => [? [isSome ?]]. *)
  (*   rewrite lookup_fmap in isSome. *)
  (*   rewrite Heq in isSome. *)
  (*   inversion isSome. *)
  (* Qed. *)

  (* Lemma wp_load ℓ s ϕ st E R : *)
  (*   {{{ (∀ s' v, ϕ s' v -∗ ϕ s' v ∗ R s' v) ∗ *)
  (*       ℓ ↦ro s | ϕ }}} *)
  (*     Load (Val $ LitV $ LitLoc ℓ) @ st; E *)
  (*   {{{ s' v, RET v; ℓ ↦ro s' | ϕ ∗ R s' v }}}. *)
  (* Proof. *)
  (*   rewrite wp_eq /wp_def. *)
  (*   iStartProof (iProp _). *)
  (*   iIntros (post ((sv & pv) & bv)) "[Htrans #Hpts]". *)
  (*   iDestruct "Hpts" as (t) "(%seen & knowPred & knowState)". *)
  (*   iIntros (? ?) "Hpost". simpl. iIntros ([[sv' pv'] bv'] ?) "#Hv Hint". *)
  (*   iDestruct "Hint" as (hists preds) "(pointsToPreds & ? & authHists & authPreds)". *)
  (*   iDestruct (own_valid_2 with "authHists knowState") as %Hv. *)
  (*   iDestruct (know_state_Some with "[$] [$]") as %[hist look]. *)
  (*   iDestruct (big_sepM_delete with "pointsToPreds") as "[ℓPts pointsToPreds]"; first done. *)
  (*   iApply (wp_load with "[$ℓPts $Hv]"). *)
  (*   iNext. *)
  (*   iIntros (t' v') "[ℓPts %FOO]". *)
  (*   iFrame "Hv". *)
  (*   iSplitL "Hpost". *)
  (*   - iApply "Hpost". *)
  (*     admit. *)
  (*   - (* Re-establish interp. *) *)
  (*     rewrite /interp. *)
  (*     iExists _, _. *)
  (*     iFrame "authHists authPreds". *)
  (*     iFrame. *)
  (*     iApply big_sepM_delete; first done. *)
  (*     iFrame. *)
  (* Abort. *)

  (*
  Lemma wp_alloc `{!SqSubsetEq ST, !PreOrder (⊑@{ST})}
        ℓ v (s : ST) (Φ : ST → val → dProp Σ) st E :
    {{{ Φ s v }}}
      ref v @ st; E
    {{{ ι, RET ℓ; mapsto_na ι ℓ [] [] s Φ }}}
  Proof.

  Lemma wp_load ℓ ι ℓ ss ss' ϕ s E :
    {{{ mapsto_na ι ℓ ss ss' s Φ }}}
      !ℓ @ s; E
    {{{ v, RET v; mapsto_na ι ℓ ss ss' Φ ∗ ϕ s v }}}
  Proof.
  *)

  Lemma wp_flush_lb ℓ prot s st E :
    {{{ store_lb ℓ prot s }}}
      Flush #ℓ @ st; E
    {{{ RET #();
      <fence> flush_lb ℓ prot s ∗
      <fence_sync> persist_lb ℓ prot s
    }}}.
  Proof.
    intros Φ.
    iStartProof (iProp _).
    iIntros ([[sv pv] bv]) "lb".
    rewrite /store_lb.
    iDestruct "lb" as (tS offset) "H". iNamed "H". iNamed "lbBase".
    iDestruct "tSLe" as %tSLe.

    iIntros ([[??]?] ?) "HΦ".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl) "#val".

    iApply wp_extra_state_interp. { done. } { by apply prim_step_flush_no_fork. }
    (* We open [interp]. *)
    iNamed 1.

    (* Get the points-to predicate. *)
    iDestruct (know_protocol_extract with "locationProtocol")
      as "(_ & order & _)".
    iDestruct (ghost_map_lookup with "allOrders order") as %look.
    iDestruct (big_sepM2_dom with "ordered") as %domEq.
    iDestruct (big_sepM2_dom with "predsHold") as %domEq2.
    assert (is_Some (phys_hists !! ℓ)) as [physHist ?].
    { apply elem_of_dom. rewrite domEq2 domEq. apply elem_of_dom. naive_solver. }
    iDestruct (ghost_map_lookup with "offsets offset") as %?.
    iDestruct (big_sepM_lookup_acc with "ptsMap") as "[pts ptsMap]".
    { apply map_lookup_zip_with_Some. naive_solver. }

    iApply (wp_flush (extra := {| extra_state_interp := True |}) with "pts").
    iNext. iIntros "pts".
    iDestruct ("ptsMap" with "pts") as "ptsMap".

    assert (tS - offset ≤ SV !!0 ℓ) as tSLe2.
    { etrans; first apply tSLe.
      f_equiv. etrans; first apply H1. apply incl. }
    rewrite -assoc.
    iSplitPure.
    { repeat split; try done. apply view_le_lub_r. done. }
    iFrame "val".
    iSplitL "HΦ".
    { iEval (monPred_simpl) in "HΦ". iApply "HΦ".
      { iPureIntro. solve_view_le. }
      iSplitL.
      - simpl.
        rewrite /flush_lb.
        iExistsN.
        iFrame "locationProtocol".
        iFrame "knowFragHist".
        iFrame "offset".
        iSplitPure. { done. }
        iLeft. iPureIntro.
        repeat split; try apply view_empty_least.
        apply view_le_lub_r. apply view_le_lub_l.
        apply view_le_singleton.
        eexists _. rewrite lookup_singleton.
        split; first reflexivity. done.
      - simpl.
        iIntros "#pers".
        rewrite /persist_lb.
        iExistsN.
        iFrame "locationProtocol".
        iFrame "knowFragHist".
        iFrame "offset".
        iSplitPure; first done.
        simpl.
        iSplit.
        { simpl. iPureIntro.
          rewrite !lookup_zero_lub.
          rewrite lookup_zero_singleton.
          lia. }
        destruct (BV !! ℓ) as [[?]|] eqn:bvLook.
        * iApply (persisted_persisted_loc_weak with "pers").
          { apply lookup_join; last done.
            rewrite lookup_singleton. done. }
          lia.
        * iApply (persisted_persisted_loc_weak with "pers").
          { rewrite lookup_op.
            rewrite bvLook.
            rewrite right_id.
            rewrite lookup_singleton. done. }
          lia. }
    iExistsN.
    iFrame "#∗%".
  Qed.

  Lemma wp_flush_na ℓ prot s q ss st E :
    {{{ mapsto_na ℓ prot q (ss ++ [s]) }}}
      Flush #ℓ @ st; E
    {{{ RET #();
      mapsto_na ℓ prot q (ss ++ [s]) ∗ <fence> flush_lb ℓ prot s ∗
      <fence_sync> persist_lb ℓ prot s
    }}}.
  Proof.
    iIntros (Φ) "pts".
    iDestruct (mapsto_na_store_lb with "pts") as "#lb".
    iIntros "HP".
    iApply wp_flush_lb; first done.
    iNext.
    iIntros "lb'".
    iApply "HP".
    iFrame.
  Qed.

  Lemma wp_flush_at ℓ prot ss s st E :
    {{{ ℓ ↦_AT^{prot} (ss ++ [s]) }}}
      Flush #ℓ @ st; E
    {{{ RET #();
      ℓ ↦_AT^{prot} (ss ++ [s]) ∗
      <fence> flush_lb ℓ prot s ∗
      <fence_sync> persist_lb ℓ prot s  }}}.
  Proof.
    iIntros (Φ) "pts".
    iDestruct (mapsto_at_store_lb with "pts") as "#lb".
    iIntros "HP".
    iApply wp_flush_lb; first done.
    iNext.
    iIntros "lb'".
    iApply "HP".
    iFrame.
  Qed.

  Lemma wp_fence (st : stuckness) (E : coPset) (Φ : val → dProp Σ) :
    <fence> ▷ Φ #() -∗ WP Fence @ st; E {{ v, Φ v }}.
  Proof.
    iStartProof (iProp _). iIntros ([[sv pv] bv]).
    iIntros "H".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl) "#val".
    iApply (wp_fence with "[//]").
    simpl.
    iNext. iIntros (_).
    cbn.
    iFrame "#∗".
    iSplit. { iPureIntro. repeat split; try done. apply view_le_l. }
    iApply monPred_mono; last iApply "H".
    repeat split; try apply incl.
    f_equiv; apply incl.
  Qed.

  Lemma wp_fence_prop P st E :
    {{{ <fence> P }}}
      Fence @ st; E
    {{{ RET #(); P }}}.
  Proof.
    intros Φ.
    iStartProof (iProp _). iIntros ([[sv pv] bv]).
    rewrite monPred_at_wand.
    iIntros "P". iIntros (tv' incl) "HΦ".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl2) "#val".
    iApply (primitive_laws.wp_fence with "[//]").
    iNext. iIntros (_).
    cbn.
    iFrame "val".
    iSplit. { iPureIntro. repeat split; try done. apply view_le_l. }
    rewrite monPred_at_wand.
    iApply "HΦ".
    - iPureIntro. etrans. apply incl2. repeat split; try done.
      apply view_le_l.
    - iApply monPred_mono; last iApply "P".
      eassert ((sv, pv, bv) ⊑ _) as incl3. { etrans; [apply incl|apply incl2]. }
      destruct tv' as [[??]?].
      repeat split; try apply incl3.
      f_equiv; apply incl3.
  Qed.

  Lemma wp_fence_sync (st : stuckness) (E : coPset) (Φ : val → dProp Σ) :
    ▷ <fence_sync> Φ #() -∗ WP FenceSync @ st; E {{ v, Φ v }}.
  Proof.
    iStartProof (iProp _). iIntros ([[sv pv] bv]).
    iIntros "H".
    iApply wp_unfold_at.
    iIntros ([[SV PV] BV] incl) "#val".
    iApply (wp_fence_sync with "[//]").
    simpl.
    monPred_simpl.
    iNext. iIntros "pers".
    cbn.
    iFrame "#∗".
    iSplit. { iPureIntro. repeat split; try done. apply view_le_l. }
    iDestruct ("H" with "[pers]") as "H".
    { iApply persisted_weak; last iApply "pers". apply incl. }
    iApply monPred_mono; last iApply "H".
    repeat split; try apply incl.
    f_equiv; apply incl.
  Qed.

End wp_rules.
