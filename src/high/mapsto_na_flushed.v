(* This in an implementation of a concurrent non-blocking stack.

The stack is implemented as a linked list. *)

From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import tactics.

From self.high Require Import proofmode wpc_proofmode or_lost.
From self.high Require Import dprop abstract_state_instances modalities
     resources crash_weakestpre weakestpre weakestpre_na weakestpre_at
     recovery_weakestpre protocol no_buffer.
From self.high.modalities Require Import fence.

Definition mapsto_na_flushed `{nvmFixedG Σ, nvmDeltaG Σ, AbstractState ST}
           ℓ (prot : LocationProtocol ST) q (s : ST) : dProp Σ :=
  ∃ (ss : list ST),
    "%lastEq" ∷ ⌜ last ss = Some s ⌝ ∗
    "pts" ∷ ℓ ↦_{prot}^{q} ss ∗
    "#flushLb" ∷ flush_lb ℓ prot s.

Section mapsto_na_flushed.
  Context `{nvmFixedG Σ, nvmDeltaG Σ, AbstractState ST}.

  Global Instance buffer_free_mapsto_na_flushed ℓ prot q (s : ST) :
    BufferFree (mapsto_na_flushed ℓ prot q s).
  Proof. apply _. Qed.

  Lemma mapsto_na_flushed_agree ℓ prot q q' (s s' : ST) :
    mapsto_na_flushed ℓ prot q s -∗ mapsto_na_flushed ℓ prot q' s' -∗ ⌜ s = s' ⌝.
  Proof.
    rewrite /mapsto_na_flushed.
    iNamed 1.
    iDestruct 1 as (ss' last') "[pts' lb']".
    rewrite /mapsto_na. iNamed "pts".
    simplify_eq.
    iDestruct "pts'" as (??????) "(% & ? & ? & ? & %look & %nolater' & ? & ? & ? & ? & ? & ? & ? & ?)".
    simplify_eq.
    iDestruct (full_entry_unenc_agree with "hist [$]") as %<-.
    iPureIntro.
    apply (inj Some).
    rewrite -lookupV -look.
    f_equiv.
    eapply map_no_later_Some_agree; try done.
  Qed.

  Lemma mapsto_na_flushed_split ℓ prot p q (s : ST) :
    mapsto_na_flushed ℓ prot (p + q) s -∗
    mapsto_na_flushed ℓ prot p s ∗ mapsto_na_flushed ℓ prot q s.
  Proof.
    iDestruct 1 as (ss last) "[[pts1 pts2] #flushLb]".
    iSplitL "pts1"; iFrame "flushLb"; iExists ss; iFrame (last) "∗".
  Qed.

  Global Instance mapsto_na_flushed_fractional ℓ prot (s : ST) :
    Fractional (λ q, mapsto_na_flushed ℓ prot q s).
  Proof.
    rewrite /Fractional.
    intros p q.
    iSplit.
    - iApply mapsto_na_flushed_split.
    - iIntros "[L R]".
      iNamed "R".
      iDestruct "L" as (??) "[[pts1' pts2'] _]".
      (* This direction is more annoying to show (not impossible) *)
  Abort.

  Lemma mapsto_na_increasing_list ℓ p q (ss : list ST) :
    mapsto_na p ℓ q ss -∗ ⌜ increasing_list (⊑@{ST}) ss ⌝.
  Proof.
    rewrite /mapsto_na. iNamed 1. iPureIntro.
    eapply increasing_map_to_increasing_list; done.
  Qed.

  Global Instance mapsto_na_flushed_post_crash_flushed `{!AntiSymm (=) (⊑@{ST})}
         ℓ prot q (s : ST) :
    IntoCrashFlush
      (mapsto_na_flushed ℓ prot q s)
      (λ _, mapsto_na_flushed ℓ prot q (bumper prot s) ∗
            crashed_in prot ℓ s)%I.
  Proof.
    rewrite /IntoCrashFlush.
    iNamed 1.
    (* iDestruct 1 as (? ss eq) "[pts lb]". *)
    iDestruct "flushLb" as "-#flushLb".
    (* We could leave out these two lines, but [iCrashFlush] takes a looong time
    to find the [IntoCrashFlush] instance. *)
    iDestruct (mapsto_na_increasing_list with "pts") as %incr.
    iDestruct (post_crash_mapsto_na with "pts") as "pts".
    iDestruct (post_crash_flush_post_crash with "pts") as "pts".
    iCrashFlush.
    iDestruct "flushLb" as (s' le) "(#crashedIn & persistLb)".
    iDestruct (crashed_in_or_lost with "crashedIn pts") as "(%s'' & %elem & pts & chr2)".
    (* iDestruct (crashed_in_or_lost with "crashedIn pts") as "(%s'' & %in & pts & rec2)". *)
    iDestruct (crashed_in_agree with "crashedIn chr2") as %<-.
    assert (s = s') as <-.
    { apply (anti_symm (⊑@{ST})); first done.
      apply elem_of_list_lookup_1 in elem as (? & ?).
      apply: increasing_list_last_greatest; done. }
    iFrame.
    iExists [_]. iSplitPure; first done. iFrame "pts".
    iExists _. iFrame.
    iNamed "crashedIn".
    iFrame "locationProtocol knowFragHist".
    iDestruct (have_SV_0) as "$".
    rewrite /persist_lb.
    iDestruct "persistLb" as (?) "(? & ? & ? & ? & per)".
    iRight. iApply (primitive_laws.persisted_loc_weak with "per").
    lia.
  Qed.

End mapsto_na_flushed.

(* Global Instance mapsto_na_flushed_as_fractional `{nvmFixedG Σ, nvmDeltaG Σ, AbstractState ST} per l q v : *)
(*   AsFractional (mapsto_na per l q v) (λ q, mapsto_na per l q v)%I q. *)
(* Proof. split; [done | apply _]. Qed. *)
