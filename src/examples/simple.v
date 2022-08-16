From iris.proofmode Require Import tactics.
From iris.bi Require Import monpred.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances adequacy.
From self.high Require Import proofmode wpc_proofmode.
From self.high Require Import dprop resources crash_weakestpre weakestpre
     weakestpre_na recovery_weakestpre lifted_modalities modalities
     post_crash_modality protocol no_buffer abstract_state_instances locations protocol
     adequacy.
From self.high.modalities Require Import fence.

Definition prog : expr := let: "l" := ref_NA #1 in !_NA "l".

Definition pure : expr :=
  let: "a" := #1 in
  let: "b" := #7 in
  "a" + "b".

Section specs.
  Context `{!nvmG Σ}.

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

Lemma wpr_pure `{!nvmG Σ} s E :
  ⊢ wpr s E pure pure (λ v, ⌜ v = #8 ⌝)%I (λ v, ⌜ v = #8 ⌝)%I.
Proof.
  iApply idempotence_wpr.
  2: { iApply wpc_with_let. }
  { apply _. }
  iIntros "H".
  iModIntro.
  iApply wpc_with_let.
Qed.

Lemma wpr_pure_safe :
  recv_adequate NotStuck (pure `at` ⊥) (pure `at` ⊥) (∅, ∅)
                (λ v _, v.(val_val) = #8) (λ v _, v.(val_val) = #8).
Proof.
  apply (high_recv_adequacy nvmΣ NotStuck pure pure ∅ ∅ (λ v, v = #8) (λ v, v = #8) 0).
  - done.
  - iIntros (??) "_". iApply wpr_pure.
Qed.

Definition program (ℓ : loc) : expr :=
  #ℓ <-_NA #1 ;;
  Flush #ℓ ;;
  FenceSync ;;
  #().

Section fence_sync.
  Context `{!nvmG Σ}.

  (* Predicate used for the location [a]. *)
  Program Definition prot : LocationProtocol nat :=
    {| pred := λ n v, ⌜v = #n⌝%I;
       bumper n := n |}.
  Next Obligation. iIntros. by iApply post_crash_flush_pure. Qed.

  Lemma spec ℓ st E :
    {{{ ℓ ↦_{prot} [0] }}}
      program ℓ @ st; E
    {{{ RET #(); ℓ ↦_{prot} [1] }}}.
  Proof.
    iIntros (Φ) "pts Φpost".
    rewrite /program.
    wp_apply (wp_store_na with "[$pts]"); first done.
    { suff leq : (0 ≤ 1); first apply leq. lia. }
    { done. }
    iIntros "pts".
    wp_pures.
    wp_apply (wp_flush_na with "pts").
    iIntros "(pts & _ & lb) /=".
    wp_pures.
    wp_apply wp_fence_sync.
    iModIntro.
    simpl.
    wp_pures.
    iModIntro.
    iApply "Φpost".
    iApply (mapsto_na_persist_lb with "pts lb").
    cbn. lia.
  Qed.

End fence_sync.
