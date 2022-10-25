From iris.algebra Require Import excl.
From iris.proofmode Require Import tactics.
From iris.bi Require Import lib.fractional.

From self Require Import map_extra.
From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances.
From self.base Require Import proofmode wpc_proofmode wpr_lifting.
From self.high Require Import dprop crash_weakestpre viewobjective state_interpretation weakestpre crash_borrow
  monpred_simpl.
From self.high.modalities Require Import no_buffer.
From self.lang Require Import lang.

(* Implementation. *)

Definition mk_lock : expr :=
  λ: <>, ref_AT #0.

Definition acquire : expr :=
  rec: "f" "lock" :=
    if: CAS "lock" #0 #1
    then Fence;; #()
    else "f" "lock".

Definition release : expr := λ: "lock", "lock" <-_AT #0.

(* Specification. *)

Class lockG Σ := LockG { lock_tokG : inG Σ (exclR unitO) }.
Local Existing Instance lock_tokG.

Definition lockΣ : gFunctors := #[GFunctor (exclR unitO)].

Global Instance subG_lockΣ {Σ} : subG lockΣ Σ → lockG Σ.
Proof. solve_inG. Qed.

Section spec.
  Context `{nvmG Σ, lockG Σ} (N : namespace).

  Definition internal_token γ : iProp Σ := own γ (Excl ()).

  Lemma locked_exclusive (γ : gname) : internal_token γ -∗ internal_token γ -∗ False.
  Proof.
    iIntros "A B". iDestruct (own_valid_2 with "A B") as %?. done.
  Qed.

  (* The token that is exposed to client of type [dProp]. *)
  Definition locked γ : dProp Σ := ⎡ internal_token γ ⎤%I.

  Definition history_res γ (hist : history) (R : dProp Σ) nD : iProp Σ :=
    [∗ map] t ↦ msg ∈ hist,
      ⌜ msg.(msg_val) = #0 ⌝ ∗ ⌜ hist !! (t + 1)%nat = None ⌝ -∗
        internal_token γ ∗ R (msg_to_tv msg, nD).

  Definition lock_inv ℓ γ (R : dProp Σ) nD : iProp Σ :=
    ∃ hist,
      ℓ ↦h hist ∗
        ⌜ map_Forall (λ t msg,
            (msg.(msg_val) = #0 ∨ msg.(msg_val) = #1) ∧
            msg.(msg_persist_view) = msg.(msg_persisted_after_view) ∧
              msg.(msg_store_view) !!0 ℓ = t
          ) hist ⌝ ∗
      history_res γ hist R nD.

  Lemma history_inv_extract γ hist R nD t msg msg' :
    hist !! t = Some msg →
    msg.(msg_val) = #0 →
    msg'.(msg_val) = #1 →
    hist !! (t + 1) = None →
    history_res γ hist R nD -∗
    history_res γ (<[ t + 1 := msg' ]> hist) R nD ∗
      R (msg_to_tv msg, nD) ∗
      internal_token γ.
  Proof.
    intros ?? msg0 ?.
    rewrite /history_res.
    rewrite big_sepM_insert //.
    do 2 rewrite (big_sepM_delete _ hist) //.
    rewrite -assoc.
    iIntros "(Hi & Hmap)".
    iSplitL "". { rewrite msg0. iIntros "[%eq H]". inversion eq. }
    rewrite -assoc.
    iSplitL "". { rewrite lookup_insert. iIntros "[_ %eq]". inversion eq. }
    iDestruct ("Hi" with "[//]") as "[$ $]".
    iApply (big_sepM_impl with "Hmap").
    iIntros "!>" (???).
    destruct (decide (k = t)) as [->|]; last first.
    { rewrite lookup_insert_ne; last lia. iIntros "$". }
    rewrite lookup_insert.
    iIntros "H [HA %eq]".
    inversion eq.
  Qed.

  Program Definition is_lock (γ : gname) (v : val) (R : dProp Σ) : dProp Σ :=
    MonPredCurry (λ nD TV,
      ∃ (ℓ : loc), ⌜ v = #ℓ ⌝ ∗ inv N (lock_inv ℓ γ R nD)
    )%I _.

  Global Instance is_lock_persistent γ v R :
    Persistent (is_lock γ v R).
  Proof. apply monPred_persistent => i. apply _. Qed.

  Lemma mk_lock_spec (R : dProp Σ) s E `{BufferFree R} :
    {{{ R }}}
      mk_lock #() @ s; E
    {{{ γ lv, RET lv; is_lock γ lv R }}}.
  Proof.
    intros ?. iModel. iIntros "HR".
    introsIndex ??. iIntros "HΦ".
    iApply wp_unfold_at.
    iIntros ([[??]?] ?) "#Hval".
    rewrite /mk_lock.
    wp_pures.
    iApply wp_fupd.
    wp_apply (wp_alloc with "Hval").
    iIntros (ℓ ?) "(_ & _ & %vLook & pts)".
    iMod (own_alloc (Excl ())) as (γ) "Htok"; first done.
    iMod (inv_alloc N _ (lock_inv ℓ γ R gnames) with "[-HΦ]") as "#HI".
    { iIntros "!>". repeat iExists _.
      iFrame "pts".
      rewrite map_Forall_singleton.
      rewrite /history_res big_sepM_singleton /=.
      iSplitPure. { rewrite vLook. naive_solver. }
      iIntros "H".
      iFrame "Htok".
      (* Follows from monotinicity and buffer freeness of [R]. *)
      iApply (into_no_buffer_at R).
      iApply monPred_mono; last iFrame "HR".
      split; last done.
      solve_view_le. }
    simpl.
    iModIntro.
    iSplitPure; first done.
    iFrame "Hval".
    iSpecialize ("HΦ" $! γ #ℓ).
    monPred_simpl.
    iApply "HΦ"; first naive_solver.
    iExists _.
    iSplitPure; first reflexivity.
    iFrame "HI".
  Qed.

  Lemma acquire_spec γ (R : dProp Σ) lv `{BufferFree R} st E :
    ↑N ⊆ E →
    {{{ is_lock γ lv R }}}
      acquire lv @ st; E
    {{{ RET #(); R ∗ locked γ }}}.
  Proof.
    intros ??.
    iModel.
    simpl.
    iIntros "(%ℓ & -> & #Hinv)".
    simpl.
    introsIndex ??. iIntros "HΦ".
    iApply wp_unfold_at.
    iIntros ([[??]?]) "%incl #Hval".
    rewrite /acquire.
    wp_pure _.
    iLöb as "IH" forall (g g0 g1 incl) "Hval".
    wp_pures.
    simpl.
    (* Why can we not open the invariant here? *)
    (* Some instance is probably missing. *)
    (* iInv N as "Hl". *)
    wp_bind (CmpXchg #ℓ #0 #1).
    wp_apply wp_atomic.
    iInv N as "Hl" "Hcl".
    iModIntro.
    iDestruct "Hl" as (?) "(>Hpts & >%histinv & Hmap)".
    (* iDestruct "Hl" as (????) "(>%histInv & >Hpts & HIHI)". *)
    (* destruct histInv as (t & hi). *)
    wp_apply (wp_cmpxchg with "[%] [$Hval $Hpts]").
    { intros ????.
      eapply map_Forall_lookup_1 in histinv as ([-> | ->] & _ & _);
        naive_solver. }
    iIntros (tNew ??????) "(% & #Hval' & %Hlook & %Hlooknew & disj)".
    iDestruct "disj" as "[left | right]".
    - iDestruct "left" as (-> -> ->) "Hpts".
      iDestruct (history_inv_extract _ _ _ _ _ _
                           {|
                             msg_val := #1;
                             msg_store_view :=
                               <[ℓ:=MaxNat (tNew + 1)]> (g ⊔ SVm);
                             msg_persist_view := g0 ⊔ FVm;
                             msg_persisted_after_view := g0 ⊔ FVm
                           |}
                  with "Hmap") as "(Hmap & HR & tok)"; try done.
      iMod ("Hcl" with "[Hpts Hmap]").
      { iNext. iExists _. iFrame "Hpts".
        iFrame "Hmap". iPureIntro.
        rewrite map_Forall_insert /= //.
        split; last apply histinv.
        rewrite lookup_zero_insert.
        naive_solver. }
      iModIntro. rewrite /thread_fill_item. simpl.
      wp_pures.
      wp_apply primitive_laws.wp_fence; first done.
      iIntros "_".
      rewrite /thread_fill_item. simpl.
      wp_pures.
      iModIntro.
      iSplitPure. { solve_view_le. }
      iFrame "Hval'".
      monPred_simpl.
      iApply "HΦ".
      { iPureIntro. split; last done.
        etrans; first apply incl.
        solve_view_le. }
      iFrame "tok".
      rewrite /msg_to_tv /=.
      iApply monPred_mono; last iApply "HR".
      solve_view_le.
      split; last done.
      eapply map_Forall_lookup_1 in histinv as (hehw & eq & look); last done.
      simpl in eq, look.
      repeat split.
      * solve_view_le.
      * rewrite eq. solve_view_le.
      * solve_view_le.
    - iDestruct "right" as (-> ->) "Hpts".
      iMod ("Hcl" with "[Hpts Hmap]").
      { iNext. iExists _. iFrame (histinv) "Hpts Hmap". }
      iModIntro. rewrite /thread_fill_item. simpl.
      wp_pure _.
      simpl.
      wp_pure _.
      iApply program_logic.crash_weakestpre.wp_mono; last first.
      { iApply ("IH" with "[%] HΦ Hval'").
        solve_view_le. }
      iIntros ([??]).
      simpl.
      iIntros "(% & $ & $)".
      iPureIntro. solve_view_le.
  Qed.

  Lemma release_spec γ (R : dProp Σ) lv `{BufferFree R} st E :
    ↑N ⊆ E →
    {{{ is_lock γ lv R ∗ R ∗ locked γ }}}
      release lv @ st; E
    {{{ RET #(); True }}}.
  Proof.
    intros ??.
    iModel.
    iIntros "((%ℓ & -> & Hinv) & HR & Htok)".
    introsIndex ??. iIntros "HΦ".
    iApply wp_unfold_at.
    iIntros ([[??]?] ?) "#Hval".
    rewrite /release.
    wp_pures.
    simpl.
    (* Why can we not open the invariant here? *)
    (* Some instance is probably missing. *)
    (* iInv N as "Hl". *)
    iApply wp_atomic.
    iInv N as "Hl" "Hcl".
    iModIntro.
    iDestruct "Hl" as (?) "(>Hpts & >%histInv & Hmap)".
    wp_apply (wp_store_release with "[$Hval $Hpts]").
    iIntros (tNew) "(% & % & #Hval' & Hpts)".
    iMod ("Hcl" with "[Hpts Htok HR Hmap]").
    { iNext.
      iExists _.
      iFrameF "Hpts".
      rewrite /history_res big_sepM_insert // /=.
      iSplitPure.
      { rewrite map_Forall_insert // /=.
        split; last done.
        rewrite lookup_zero_insert.
        naive_solver. }
      iSplitL "HR Htok".
      { iIntros "H".
        iFrame "Htok".
        rewrite /msg_to_tv /=.
        iApply (into_no_buffer_at R _ _ _ g1).
        iApply monPred_mono; last iFrame "HR".
        split; last done.
        repeat destruct_thread_view.
        repeat split; simpl; solve_view_le. }
      iApply (big_sepM_impl with "Hmap").
      iIntros "!>" (???).
      setoid_rewrite lookup_insert_None.
      iIntros "H" ((I & HIHI & HIHIHIH)).
      iApply "H".
      iPureIntro.
      naive_solver. }
    iModIntro.
    iFrame "Hval'".
    iSplitPure; first solve_view_le.
    monPred_simpl.
    iApply "HΦ".
    { iPureIntro. split; last done. solve_view_le. }
    done.
  Qed.

End spec.
