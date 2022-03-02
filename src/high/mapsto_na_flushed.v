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

  (* Lemma mapsto_na_increasing_list ℓ p q (ss : list ST) : *)
  (*   mapsto_na p ℓ q ss -∗ ⌜ increasing_list (⊑@{ST}) ss ⌝. *)
  (* Proof. rewrite /mapsto_na. iNamed 1. iFrame (incrList). Qed. *)

  Global Instance mapsto_na_flushed_post_crash_flushed ℓ prot q (s : ST) :
    IntoCrashFlush
      (mapsto_na_flushed ℓ prot q s)
      (λ _, mapsto_na_flushed ℓ prot q (bumper prot s) ∗
            recovered_at ℓ (bumper prot s))%I.
  Proof.
    rewrite /IntoCrashFlush.
    iNamed 1.
    (* iDestruct 1 as (? ss eq) "[pts lb]". *)
    iDestruct "flushLb" as "-#flushLb".
    (* We could leave out these two lines, but [iCrashFlush] takes a looong time
    to find the [IntoCrashFlush] instance. *)
    (* iDestruct (mapsto_na_increasing_list with "pts") as %incr. *)
    iDestruct (post_crash_mapsto_na with "pts") as "pts".
    iDestruct (post_crash_flush_post_crash with "pts") as "pts".
    iCrashFlush.
    iDestruct "flushLb" as (s' le) "(#rec & persistLb)".
    iDestruct (recovered_at_or_lost with "rec pts") as "(%s'' & %in & pts & rec2)".
    iDestruct (recovered_at_agree with "rec rec2") as %eq.
    (* FIXME: We need to know that [s'] and [s''] are equal. *)
    (* iExists ([_]). iFrame "pts flushLb". *)
  Admitted.

End mapsto_na_flushed.

(* Global Instance mapsto_na_flushed_as_fractional `{nvmFixedG Σ, nvmDeltaG Σ, AbstractState ST} per l q v : *)
(*   AsFractional (mapsto_na per l q v) (λ q, mapsto_na per l q v)%I q. *)
(* Proof. split; [done | apply _]. Qed. *)
