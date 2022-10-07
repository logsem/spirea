From iris.algebra Require Import excl.
From iris.proofmode Require Import tactics.
From iris.bi Require Import lib.fractional.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances.
From self.base Require Import proofmode wpc_proofmode wpr_lifting.
From self.high Require Import dprop weakestpre monpred_simpl.
From self.high.modalities Require Import no_buffer.
From self.lang Require Import lang.

(* Implementation. *)

Definition mk_lock : expr :=
  ref_AT #0.

Definition acquire : expr :=
  rec: "f" "lock" :=
    if: CAS "lock" #0 #1
    then #()
    else "f" "lock".

Definition release : expr := λ: "lock", "lock" <-_AT #0.

(* Expresses that [hist] has no "gaps" and that the last message in the history
is [msg]. The location of a history that is only updated with RMW will have this
form. *)
Definition history_sequence (hist : history) msg :=
  ∃ t, hist !! t = Some msg ∧ ∀ t', t' < t → ∃ msg', hist !! t' = Some msg'.

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

  Definition lock_inv ℓ γ (R : dProp Σ) nD : iProp Σ :=
    (∃ hist vl SV FV,
      ⌜ history_sequence hist (Msg vl SV FV FV) ⌝ ∗
      ℓ ↦h hist ∗
        (⌜ vl = #1 ⌝ (* unlocked state *)
         ∨
         ⌜ vl = #0 ⌝ ∗ internal_token γ ∗ R ((SV, FV, ∅), nD) (* locked state *))
    )%I.

  Program Definition is_lock (γ : gname) (R : dProp Σ) (v : val) : dProp Σ :=
    MonPredCurry (λ nD TV,
      ∃ (ℓ : loc), ⌜ v = #ℓ ⌝ ∗ inv N (lock_inv ℓ γ R nD)
    )%I _.

  Lemma mk_lock_spec (R : dProp Σ) s E `{BufferFree R} :
    {{{ R }}}
      mk_lock @ s; E
    {{{ γ lv, RET lv; is_lock γ R lv }}}.
  Proof.
    intros ?.
    iModel.
    simpl.
    iIntros "HR".
    simpl.
    introsIndex ??. iIntros "HΦ".
    iApply wp_unfold_at.
    iIntros ([[??]?] ?) "#Hval".
    rewrite /mk_lock.
    iApply wp_fupd.
    wp_apply (wp_alloc with "Hval").
    iIntros (ℓ ?) "(_ & _ & _ & pts)".
    iMod (own_alloc (Excl ())) as (γ) "Htok"; first done.
    iMod (inv_alloc N _ (lock_inv ℓ γ R gnames) with "[-HΦ]") as "#HI".
    { iIntros "!>". repeat iExists _.
      iFrame "pts".
      iSplitPure.
      { simpl. exists 0. simpl. split; first naive_solver. intros ??. lia. }
      iRight. iSplitPure; first done.
      simpl.
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

  Lemma acquire_spec γ (R : dProp Σ) lv s E :
    {{{ is_lock γ R lv }}}
      acquire lv @ s; E
    {{{ v, RET v; R ∗ locked γ }}}.
  Proof.
    intros ?.
    iModel.
    simpl.
    iIntros "HR".
    simpl.
    introsIndex ??. iIntros "HΦ".
    iApply wp_unfold_at.
    iIntros ([[??]?] ?) "#Hval".
    rewrite /acquire.
  Admitted.

  Lemma release_spec γ (R : dProp Σ) lv `{BufferFree R} :
    {{{ is_lock γ R lv ∗ R ∗ locked γ }}}
      release lv
    {{{ v, RET v; True }}}.
  Proof.
    intros ?.
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
    assert (Inhabited val); first admit.
    iDestruct "Hl" as (????) "(>%Heq & >Hpts & HIHI)".
    wp_apply (wp_store_release with "[$Hval $Hpts]").
    iIntros (tNew) "(% & % & #Hval' & Hpts)".
    iMod ("Hcl" with "[Hpts Htok HR]").
    { iNext. iExists _, #0, _, _.
      iFrame "Hpts".
      iSplitPure.
      { exists tNew. split.
        - rewrite lookup_insert. done.
        - admit. }
      iRight.
      iSplitPure; first done.
      iFrame "Htok".
      iApply (into_no_buffer_at R).
      iApply monPred_mono; last iFrame "HR".
      split; last done.
      repeat destruct_thread_view.
      repeat split; try solve_view_le. }
    iModIntro.
    iFrame "Hval'".
    iSplitPure; first solve_view_le.
    iSpecialize ("HΦ" $! #()).
    monPred_simpl.
    iApply "HΦ".
    { iPureIntro. split; last done. solve_view_le. }
    done.
  Admitted.

End spec.
