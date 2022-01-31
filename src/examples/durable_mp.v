From iris.proofmode Require Import tactics.
From iris.algebra Require Import excl.
From Perennial.program_logic Require Import staged_invariant.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances crash_borrow.
From self.high Require Import proofmode wpc_proofmode.
From self.high Require Import crash_weakestpre modalities weakestpre
     weakestpre_na weakestpre_at recovery_weakestpre protocol crash_borrow no_buffer
     abstract_state_instances.
From self.high.modalities Require Import fence no_buffer.

Section program.

  Definition leftProg (x y : loc) : expr :=
    #x <- #true ;;
    WB #x ;;
    Fence ;;
    #y <-{rel} #true.

  Definition rightProg (y z : loc) : expr :=
    if: !{acq} #y = #true
    then Fence ;; #z <- #true
    else #().

  Definition prog (x y z : loc) : expr :=
    Fork (rightProg y z) ;; leftProg x y.

  Definition recovery x z : expr :=
    if: ! z = #true
    then assert: ! x = #true
    else #().

End program.

Section proof.
  Context `{nvmFixedG Σ, nvmDeltaG Σ, inG Σ (exclR unitO)}.
  Context `{!stagedG Σ}.

  Context (x y z : loc) (γ__ex : gname).

  Definition inv_x (b : bool) (v : val) (hG : nvmDeltaG Σ) : dProp Σ :=
    ⌜v = #b⌝.

  Program Instance : LocationProtocol inv_x := { bumper n := n }.
  Next Obligation. iIntros. by iApply post_crash_flush_pure. Qed.

  Definition inv_y (b : bool) (v : val) (hG : nvmDeltaG Σ) : dProp Σ :=
    match b with
      false => ⌜ v = #false ⌝ ∗ ⎡ own γ__ex (Excl ()) ⎤
    | true => ⌜ v = #true ⌝ ∗ know_flush_lb x true
    end.

  Program Instance : LocationProtocol inv_y := { bumper n := n }.
  Next Obligation.
    iIntros (? [|] ?); simpl.
    - iIntros "[% lb]". iCrashFlush.
      iDestruct "lb" as "(% & %le & ? & ? & ? & ?)".
      destruct s__pc; last done.
      iFrame "∗%".
    - iIntros "[% H]". iCrashFlush. iFrame. done.
  Qed.

  Definition inv_z := inv_y.

  Definition crash_condition {hD : nvmDeltaG Σ} : dProp Σ :=
    ∃ (sx sz : list bool),
      "#xProt" ∷ know_protocol x inv_x ∗
      "#yProt" ∷ or_lost y (know_protocol y inv_y) ∗
      "#yShared" ∷ or_lost y (⎡ is_at_loc y ⎤) ∗
      "#zProt" ∷ know_protocol z inv_z ∗
      x ↦_{true} sx ∗
      z ↦_{true} sz.

  Definition right_crash_condition {hD : nvmDeltaG Σ} : dProp Σ :=
    ∃ (sz : list bool),
      "#yProt" ∷ or_lost y (know_protocol y inv_y) ∗
      "#yShared" ∷ or_lost y (⎡ is_at_loc y ⎤) ∗
      "#zProt" ∷ know_protocol z inv_z ∗
      z ↦_{true} sz.

  Definition left_crash_condition {hD : nvmDeltaG Σ} : dProp Σ :=
    ∃ (sx : list bool),
      "#yProt" ∷ or_lost y (know_protocol y inv_y) ∗
      "#yShared" ∷ or_lost y (⎡ is_at_loc y ⎤) ∗
      "#xProt" ∷ know_protocol x inv_x ∗
      x ↦_{true} sx.

  Lemma right_crash_condition_impl {hD : nvmDeltaG Σ} (ssZ : list bool) :
    know_protocol y inv_y -∗
    know_protocol z inv_z -∗
    know_store_lb y false -∗
    ⎡ is_at_loc y ⎤ -∗
    z ↦_{true} ssZ -∗
    <PC> hD, right_crash_condition.
  Proof.
    iIntros "yProt zProt yLb yShared zPts".
    iCrash.
    iDestruct "zPts" as (??) "[zPts zRec]".
    iExists _.
    iDestruct (recovered_at_or_lost with "zRec zProt") as "zProt".
    iFrame.
  Qed.

  Lemma left_crash_condition_impl {hD : nvmDeltaG Σ} (ssX : list bool) :
    know_protocol y inv_y -∗
    know_protocol x inv_x -∗
    know_store_lb y false -∗
    ⎡ is_at_loc y ⎤ -∗
    x ↦_{true} ssX -∗
    <PC> hD, left_crash_condition.
  Proof.
    iIntros "yProt xProt yLb yShared xPts".
    iCrash.
    iDestruct "xPts" as (??) "[xPts xRec]".
    iExists _.
    iDestruct (recovered_at_or_lost with "xRec xProt") as "xProt".
    iFrame.
  Qed.

  (* Prove right crash condition. *)
  Ltac whack_right_cc :=
    iSplit;
    first iApply (right_crash_condition_impl with "yProt zProt yLb yShared zPts").

  Ltac whack_left_cc :=
    iSplit;
    first iApply (left_crash_condition_impl with "yProt xProt yLb yShared xPts").

  Lemma right_prog_spec s E1 :
    know_protocol y inv_y -∗
    know_protocol z inv_z -∗
    know_store_lb y false -∗
    ⎡ is_at_loc y ⎤ -∗
    z ↦_{true} [false] -∗
    WPC rightProg y z @ s; E1
    {{ v, z ↦_{true} [false; true] ∨ z ↦_{true} [false] }}
    {{ <PC> _, right_crash_condition }}.
  Proof.
    iIntros "#yProt #zProt #yLb #yShared zPts".
    (* Evaluate the first load. *)
    rewrite /rightProg.
    wpc_bind (!{acq} _)%E.
    iApply wpc_atomic_no_mask. whack_right_cc.
    iApply (wp_load_at _ _ (λ s v, (⌜v = #true⌝ ∗ know_flush_lb x true) ∨ ⌜v = #false⌝)%I inv_y with "[$yProt $yShared $yLb]").
    { iModIntro. iIntros (?? incl) "a". rewrite /inv_y.
      destruct s'.
      - iDestruct "a" as "[% #?]". iFrame "#". naive_solver.
      - iDestruct "a" as "[% O]". naive_solver. }
    iNext.
    iIntros (??) "[yLb' disj]".
    iDestruct (post_fence_extract' _ (⌜v = #true ∨ v = #false⌝)%I with "disj []") as %[-> | ->].
    { iIntros "[[-> _]|->]"; naive_solver. }
    2: {
      (* We loaded [false] and this case is trivial. *)
      whack_right_cc.
      iModIntro.
      wpc_pures.
      { iApply (right_crash_condition_impl with "yProt zProt yLb yShared zPts"). }
      iModIntro.
      iRight. iFrame. }
    (* We loaded [true]. *)
    whack_right_cc.
    iModIntro.
    wpc_pures.
    { iApply (right_crash_condition_impl with "yProt zProt yLb yShared zPts"). }
    wpc_bind (Fence).
    iApply wpc_atomic_no_mask. whack_right_cc.
    iApply wp_fence. do 2 iModIntro.
    iDestruct "disj" as "[[_ #xLb] | %]"; last congruence.
    whack_right_cc.
    iModIntro.
    wpc_pures.
    { iApply (right_crash_condition_impl with "yProt zProt yLb yShared zPts"). }

    iApply wpc_atomic_no_mask. whack_right_cc.
    iApply (wp_store_na _ _ _ _ _ true inv_z with "[$zPts $zProt]"); eauto.
    { simpl. iFrame "xLb". done. }

    iIntros "!> zPts /=".
    whack_right_cc.
    iModIntro.
    iLeft. iFrame.
  Qed.

  Lemma prog_spec :
    ⎡ pre_borrow ⎤ ∗
    know_protocol x inv_x ∗ know_protocol y inv_y ∗ know_protocol z inv_z ∗
    x ↦_{true} [false] ∗
    know_store_lb y false ∗
    ⎡ is_at_loc y ⎤ ∗
    z ↦_{true} [false] -∗
    WPC prog x y z @ ⊤
    {{ v, True }}
    {{ <PC> _, crash_condition }}.
  Proof.
    iIntros "(pb & #xProt & #yProt & #zProt & xPts & #yLb & #yShared & zPts)".
    rewrite /prog.

    (* We create a crash borrow in order to transfer resources to the forked
    thread. *)
    iApply (wpc_crash_borrow_inits _ _ _ _ _ (<PC> _, right_crash_condition)%I
             with "pb [zPts]").
    { iAccu. }
    { iModIntro. iIntros "zPts".
      iDestruct "zProt" as "-#zProt".
      iDestruct "yProt" as "-#yProt".
      iDestruct "yShared" as "-#yShared".
      iCrash.
      iDestruct "zPts" as (??) "[zPts zRec]".
      iDestruct (recovered_at_or_lost with "zRec zProt") as "zProt".
      iExists _. iFrame. }
    iIntros "cb".

    iApply (wpc_crash_mono _ _ _ _ _ (<PC> _, left_crash_condition)%I).
    { iIntros "L R".
      iCrash.
      iDestruct "L"  as (?) "(H1 & H2 & H3 & xPts)".
      iDestruct "R" as (?) "(yProt & ySh & zProt & zPts)".
      iExists _, _.
      iFrame "H3".
      iFrame "yProt ySh zProt xPts zPts". }
    Unshelve. 2: { apply _. }

    wpc_bind (Fork _)%E.
    iApply (wpc_fork with "[cb]").
    - (* Show safety of the forked off thread. *)
      iApply (wpc_crash_borrow_open_modify with "cb"); first done.
      iNext. iSplit; first done.
      iIntros "zPts".
      (* rewrite (left_id True%I (∗)%I). *)

      iDestruct (right_prog_spec with "yProt zProt yLb yShared zPts") as "wp".
      iApply (wpc_mono' with "[] [] wp"); last naive_solver.
      iIntros (?) "[zPts | zPts]".
      * iExists (z ↦_{true} (_ : list bool)). iFrame.
        iSplit; last naive_solver.
        iIntros "!> zPts".
        iApply (right_crash_condition_impl with "yProt zProt yLb yShared zPts").
      * iExists (z ↦_{true} (_ : list bool)). iFrame.
        iSplit; last naive_solver.
        iIntros "!> zPts".
        iApply (right_crash_condition_impl with "yProt zProt yLb yShared zPts").
    - whack_left_cc. iNext.
      wpc_pures.
      { iApply (left_crash_condition_impl with "yProt xProt yLb yShared xPts"). }
      rewrite /leftProg.
      wpc_bind (_ <- _)%E.
      iApply wpc_atomic_no_mask. whack_left_cc.
      iApply (wp_store_na x _ _ _ _ true with "[$xProt $xPts]").
      { reflexivity. } { done. }
      { rewrite /inv_x. done. }
      simpl.
      iNext. iIntros "xPts".
      whack_left_cc.
      iModIntro.
      wpc_pures;
      first iApply (left_crash_condition_impl with "yProt xProt yLb yShared xPts").

      (* WB *)
      wpc_bind (WB _)%E.
      iApply wpc_atomic_no_mask.
      whack_left_cc.
      iApply (wp_wb_ex with "xPts"); first reflexivity.
      iNext.
      iIntros "[xPts #xLowerBound]".
      whack_left_cc.
      iModIntro.
      wpc_pures;
      first iApply (left_crash_condition_impl with "yProt xProt yLb yShared xPts").

      (* The fence. *)
      wpc_bind (Fence)%E.
      iApply wpc_atomic_no_mask. whack_left_cc.
      iApply wp_fence. do 2 iModIntro.
      whack_left_cc.
      iModIntro.
      wpc_pures;
      first iApply (left_crash_condition_impl with "yProt xProt yLb yShared xPts").

      wpc_bind (_ <-{rel} _)%E.
      iApply wpc_atomic_no_mask. whack_left_cc.
      iApply (wp_store_at _ false true).
      { iFrame.
        iPureGoal. { done. }
        iFrame "#".
        iSplitL.
        - iModIntro. simpl. naive_solver.
        - iIntros (? s_c v_c). simpl.
          destruct s_c; first naive_solver.
          iIntros "([? O1] & [??] & [? O2])".
          by iDestruct (own_valid_2 with "O1 O2") as %HI%exclusive_l. }
      iIntros "!> yLb2".
      whack_left_cc.
      done.
  Qed.

End proof.
