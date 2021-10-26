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

From self Require Export extra ipm_tactics.
From self.high Require Export dprop.
From self Require Export view.
From self Require Export lang.
From self.base Require Import tactics.
From self.base Require Import primitive_laws.
From self.lang Require Import syntax.
From self.high Require Import resources crash_weakestpre lifted_modalities
     monpred_simpl modalities protocol.

Section wp.
  Context `{!nvmFixedG Σ, nvmDeltaG Σ}.

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

  Lemma wp_value_fupd s E Φ e v :
    IntoVal e v → (|NC={E}=> Φ v) ⊢ WP e @ s; E {{ Φ }}.
  Proof. intros <-. apply wp_value_fupd'. Qed.

  (* If the expression is a value then showing the postcondition for the value
  suffices. *)
  Lemma wp_value s E Φ v : Φ v ⊢ WP (of_val v) @ s; E {{ Φ }}.
  Proof. iIntros "H". iApply wp_value_fupd'. iModIntro. iFrame. Qed.

  (* Lemma wp_fupd s E e Φ : WP e @ s; E {{ v, fupd E E (Φ v) }} ⊢ WP e @ s; E {{ Φ }}. *)
  (* Proof. Admitted. *)
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
    iIntros "H % HV".
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

End wp.

(* Definition lastR (ST : Type) : cmra := *)
(*   prodR fracR (agreeR (prodO (leibnizO ST) valO)). *)

Section wp_rules.
  Context `{AbstractState ST}.
  Context `{!nvmFixedG Σ, hG : nvmDeltaG Σ}.

  Implicit Types (ℓ : loc) (s : ST) (ϕ : ST → val → nvmDeltaG Σ → dProp Σ).

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

  Lemma predicate_holds_phi ϕ s encS (encϕ : predO) v TV :
    encS = encode s →
    (encϕ ≡ encode_predicate ϕ)%I -∗
    (encoded_predicate_holds encϕ encS v TV ∗-∗ ϕ s v _ TV).
  Proof.
    iIntros (eqEncS) "predsEquiv".
    iSplit.
    - iDestruct 1 as (P) "[%eqP PH]".
      do 2 iEval (setoid_rewrite discrete_fun_equivI) in "predsEquiv".
      iSpecialize ("predsEquiv" $! encS v).
      rewrite /encode_predicate.
      rewrite {2}eqEncS.
      rewrite decode_encode.
      simpl.
      rewrite eqP.
      rewrite option_equivI.
      iEval (setoid_rewrite discrete_fun_equivI) in "predsEquiv".
      iSpecialize ("predsEquiv" $! hG).
      by iRewrite -"predsEquiv".
    - iIntros "phi".
      rewrite /encoded_predicate_holds.
      do 2 iEval (setoid_rewrite discrete_fun_equivI) in "predsEquiv".
      iSpecialize ("predsEquiv" $! encS v).
      rewrite /encode_predicate. rewrite eqEncS. rewrite decode_encode.
      simpl.
      destruct (encϕ (encode s) v); rewrite option_equivI; last done.
      iExists _. iSplit; first done.
      iEval (setoid_rewrite discrete_fun_equivI) in "predsEquiv".
      iSpecialize ("predsEquiv" $! hG).
      by iRewrite "predsEquiv".
  Qed.

  Lemma wp_load_ex ℓ (b : bool) ss s Q ϕ `{!LocationProtocol ϕ} positive E :
    last ss = Some s →
    {{{ mapsto_ex b ℓ ss ∗
        know_protocol ℓ ϕ ∗
        (<obj> (∀ v, ϕ s v _ -∗ Q v ∗ ϕ s v _)) }}}
      Load (Val $ LitV $ LitLoc ℓ) @ positive; E
    {{{ v, RET v; mapsto_ex b ℓ ss ∗ Q v }}}.
  Proof.
    intros sLast Φ.
    iStartProof (iProp _). iIntros (TV).
    (* We destruct the exclusive points-to predicate. *)
    iIntros "(pts & [knowPred _] & pToQ)".
    iDestruct "pts" as (?tP ?tS absHist) "pts". iNamed "pts".
    iDestruct "haveTStore" as %haveTStore.
    rewrite monPred_at_wand. simpl.
    iIntros (TV' incl) "Φpost".
    rewrite monPred_at_later.
    rewrite wp_eq /wp_def.
    rewrite wpc_eq. simpl.
    iIntros ([[SV PV] BV] incl2) "#val".
    rewrite monPred_at_pure.
    iApply program_logic.crash_weakestpre.wp_wpc.

    (* We need to get the points-to predicate for [ℓ]. This is inside [interp]. *)
    iApply wp_extra_state_interp.
    { done. }
    { (* Try and simplify this with lemmas/automation. *)
      clear.
      intros ??????? [Ki [??] [??] ? ? step].
      subst.
      simpl in *.
      induction Ki using rev_ind.
      { simpl in *. subst. inv_impure_thread_step; try done.
        rewrite list_fmap_singleton.
        subst.
        congruence. }
      move: H.
      rewrite fill_app.
      simpl.
      destruct x; try done.
      simpl.
      rewrite /thread_fill_item.
      simpl.
      inversion 1.
      simpl in *.
      rewrite -nvm_fill_fill in H2.
      simpl in *.
      destruct Ki using rev_ind; try done.
      { simpl in *. subst. inv_impure_thread_step; try done. }
      simpl in *.
      rewrite fill_app in H2.
      simpl in *.
      destruct x; try done. }
    iNamed 1.
    iDestruct (own_all_preds_pred with "predicates knowPred") as
      (pred predsLook) "#predsEquiv".
    iDestruct (own_full_history_agree with "[$] [$]") as %absHistlook.

    iDestruct (big_sepM2_dom with "predsHold") as %domPhysHistEqAbsHist.
    assert (is_Some (phys_hists !! ℓ)) as [physHist physHistsLook].
    { rewrite -elem_of_dom domPhysHistEqAbsHist elem_of_dom. done. }

    iDestruct (big_sepM2_lookup_acc with "predsHold") as "[predMap predsHold]".
    { done. } { done. }
    iDestruct "predMap" as (pred' predsLook') "predMap".
    assert (pred = pred') as <-. { apply (inj Some). rewrite -predsLook. done. }
    (* clear predsLook'. *)

    iDestruct (big_sepM_lookup_acc with "ptsMap") as "[pts ptsMap]"; first done.
    iApply (wp_load (extra := {| extra_state_interp := True |}) with "[$pts $val]").
    iNext. iIntros (t' v' msg) "[pts (%look & %msgVal & %gt)]".
    rewrite /store_view. simpl.
    iDestruct ("ptsMap" with "pts") as "ptsMap".
    iFrame "val".

    (* We need to conclude that the only write we could read is [tS]. I.e., that
    [t' = tS]. *)
    assert (tS ≤ SV !!0 ℓ) as tSle.
    { destruct TV as [[??]?].
      destruct TV' as [[??]?].
      etrans; first done.
      rewrite /store_view /=.
      apply view_lt_lt. etrans; first apply incl; apply incl2. done. }
    assert (tS ≤ t') as lte.
    { etrans; first apply tSle. apply gt. }
    iDestruct (big_sepM2_dom with "predMap") as %domEq.
    assert (is_Some (absHist !! t')) as HI.
    { apply elem_of_dom.
      erewrite <- dom_fmap_L.
      erewrite <- domEq.
      apply elem_of_dom.
      naive_solver. }
    assert (t' = tS) as ->.
    { apply Nat.lt_eq_cases in lte. destruct lte as [lt|]; last done.
      pose proof (nolater t' lt) as eq.
      rewrite eq in HI. inversion HI as [? [=]]. }
    assert (absHist !! tS = Some s) as lookS.
    { rewrite -sLast.
      apply map_slice_lookup_hi in slice.
      rewrite slice.
      done. }
    clear lte HI.

    iDestruct (big_sepM2_lookup_acc with "predMap") as "[predHolds predMap]";
      first done.
    { rewrite lookup_fmap. rewrite lookS. done. }
    iDestruct (predicate_holds_phi with "predsEquiv predHolds") as "phi";
      first done.
    rewrite monPred_at_objectively.
    iSpecialize ("pToQ" $! (msg_to_tv msg) (msg_val msg)).
    rewrite monPred_at_wand.
    iDestruct ("pToQ" with "[//] phi") as "[Q phi]".
    (* Reinsert into the predicate map. *)
    iDestruct ("predMap" with "[phi]") as "predMap".
    { iApply (predicate_holds_phi with "predsEquiv phi"). done. }
    (* Reinsert into the map. *)
    iDestruct ("predsHold" with "[predMap]") as "predsHold". { naive_solver. }

    iSplitR "ptsMap allOrders ordered predsHold history predicates
             sharedLocs crashedAt allBumpers bumpMono predPostCrash
             sharedLocsHistories"; last first.
    { repeat iExists _. iFrameNamed. }
    iSplit; first done.
    iApply "Φpost".
    iSplitR "Q".
    2: {
      (* This _should_ hold bc. the view in the message is smaller. But, we
      don't have that fact. *)
      admit.
    }
    iExists _, _, _.
    iFrameNamed.
    monPred_simpl.
    iDestruct (objective_at with "pers") as "$". { destruct b; apply _. }
    iPureIntro.
    etrans. eassumption.
    etrans. eassumption.
    eassumption.
  Admitted.

  Lemma wp_store_ex ℓ b ss v s__last s ϕ `{!LocationProtocol ϕ} st E :
    last ss = Some s__last →
    s__last ⊑ s →
    {{{ mapsto_ex b ℓ ss ∗ know_protocol ℓ ϕ ∗ ϕ s v _ }}}
      #ℓ <- v @ st; E
    {{{ RET #(); mapsto_ex b ℓ (ss ++ [s]) }}}.
  Proof.
    intros last stateGt Φ.
    iStartProof (iProp _). iIntros (TV).
    iIntros "[pts phi]".
  Admitted.
  (*   iDestruct "pts" as (?tGP ?tP ?tS absHist hist) "(pts & predsHold & %incrL & %lookupP & %lookupV & %nolater & %lastVal & hist & slice & %know & per)". *)
  (*   rewrite monPred_at_wand. simpl. *)
  (*   iIntros (TV' incl) "Φpost". *)
  (*   rewrite monPred_at_later. *)
  (*   rewrite wp_eq /wp_def. *)
  (*   rewrite wpc_eq. simpl. *)
  (*   iIntros ([[SV PV] BV] incl2) "#val interp". *)
  (*   rewrite monPred_at_pure. *)
  (*   iApply program_logic.crash_weakestpre.wp_wpc. *)
  (*   iApply (wp_store with "pts"). *)
  (* Qed. *)

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
    {{{ ι, RET ℓ; mapsto_ex ι ℓ [] [] s Φ }}}
  Proof.

  Lemma wp_load ℓ ι ℓ ss ss' ϕ s E :
    {{{ mapsto_ex ι ℓ ss ss' s Φ }}}
      !ℓ @ s; E
    {{{ v, RET v; mapsto_ex ι ℓ ss ss' Φ ∗ ϕ s v }}}
  Proof.
  *)

  Lemma wp_wb_lb ℓ s st E :
    {{{ know_store_lb ℓ s }}}
      WB #ℓ @ st; E
    {{{ RET #(); <fence> know_flush_lb ℓ s }}}.
  Proof.
  Admitted.

  Lemma wp_wb_ex ℓ b s ss st E :
    last ss = Some s →
    {{{ mapsto_ex b ℓ ss }}}
      WB #ℓ @ st; E
    {{{ RET #(); mapsto_ex b ℓ ss ∗ <fence> know_flush_lb ℓ s }}}.
  Proof.
    iIntros (eq Φ) "pts".
    iDestruct (mapsto_ex_store_lb with "pts") as "#lb"; first done.
    iIntros "HP".
    iApply wp_wb_lb; first done.
    iNext.
    iIntros "lb'".
    iApply "HP".
    iFrame.
  Qed.

  Lemma wp_fence P st E :
    {{{ <fence> P }}}
      Fence @ st; E
    {{{ RET #(); P }}}.
  Proof.
    intros Φ.
    iStartProof (iProp _). iIntros ([[sv pv] bv]).
    rewrite monPred_at_wand.
    iIntros "P". iIntros (tv' incl) "HΦ".
    monPred_simpl.
    rewrite wp_eq /wp_def.
    rewrite wpc_eq. simpl.
    iIntros ([[SV PV] BV] incl2) "#val".
    monPred_simpl. (* rewrite right_id. *)
    iApply program_logic.crash_weakestpre.wp_wpc.
    iApply (wp_fence with "[//]").
    iNext. iIntros (_).
    cbn.
    iFrame "#∗".
    iSplit. { iPureIntro. repeat split; try done. apply view_le_l. }
    iApply "HΦ".
    - iPureIntro. etrans. apply incl2. repeat split; try done.
      apply view_le_l.
    - iApply monPred_mono; last iApply "P".
      eassert ((sv, pv, bv) ⊑ _) as incl3. { etrans; [apply incl|apply incl2]. }
      destruct tv' as [[??]?].
      repeat split; try apply incl3.
      f_equiv; apply incl3.
  Qed.

End wp_rules.
