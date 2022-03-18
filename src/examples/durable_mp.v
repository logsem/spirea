(* This is the classic message passing example except with some differences.
   The sending thread ([leftProg] below) ensures that it only sends [x] after
   having flushed and fenced it. The receieving thread ([rightProg] below) saves
   and acknowledgement to [z] and with a fence ensures that it is only persisted
   after the send values is persisted.

   The recovery code ([recovery] below) relies on this being true and crashes
   otherwise. Hence showing safety of the recovery code ensures that the
   intuitive property that we expect to hold does indeed hold. *)

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
     abstract_state_instances locations protocol or_lost.
From self.high.modalities Require Import fence no_buffer.

Section program.

  Definition leftProg (x y : loc) : expr :=
    #x <-_NA #true ;;
    Flush #x ;;
    Fence ;;
    #y <-_AT #true.

  Definition rightProg (y z : loc) : expr :=
    if: !_AT #y = #true
    then Fence ;; #z <-_NA #true
    else #().

  Definition prog (x y z : loc) : expr :=
    Fork (rightProg y z) ;; leftProg x y.

  Definition recovery x z : expr :=
    if: !_NA z = #true
    then assert: !_NA x = #true
    else #().

End program.

Section proof.
  Context `{nvmFixedG Σ, nvmDeltaG Σ, inG Σ (exclR unitO)}.
  Context `{!stagedG Σ}.

  Context (x y z : loc) (γ__ex : gname).

  Program Definition inv_x : LocationProtocol bool :=
    {| pred (b : bool) v _ :=  ⌜v = #b⌝%I;
       bumper b := b; |}.
  Next Obligation. iIntros. by iApply post_crash_flush_pure. Qed.

  Program Definition inv_y :=
    {| pred (b : bool) (v : val) (hG : nvmDeltaG Σ) :=
        match b with
          false => ⌜ v = #false ⌝ ∗ ⎡ own γ__ex (Excl ()) ⎤
        | true => ⌜ v = #true ⌝ ∗ flush_lb x inv_x true
        end%I;
      bumper b := b; |}.
  Next Obligation.
    iIntros (? [|] ?); simpl.
    - iIntros "[% lb]". iCrashFlush.
      iDestruct "lb" as "(% & %le & ? & ?)".
      destruct s__pc; last done.
      iFrame "%".
      iApply persist_lb_to_flush_lb. iFrame.
    - iIntros "[% H]". iCrashFlush. iFrame. done.
  Qed.
  Next Obligation. intros ? [|]; apply _. Qed.

  Definition inv_z := inv_y.

  (* Note: The recovery code does not use the [y] location, hence the crash
  condition does not mention [y] as we don't need it to be available after a
  crash. *)
  Definition crash_condition {hD : nvmDeltaG Σ} : dProp Σ :=
    ∃ (bx bz : bool),
      "#xPer" ∷ persist_lb x inv_x bx ∗
      "#zPer" ∷ persist_lb z inv_z bz ∗
      x ↦_{inv_x} [bx] ∗
      z ↦_{inv_z} [bz].

  Definition left_crash_condition {hD : nvmDeltaG Σ} : dProp Σ :=
    ∃ (bx : bool),
      "#xPer" ∷ persist_lb x inv_x bx ∗
      "xPts" ∷ x ↦_{inv_x} [bx].

  Definition right_crash_condition {hD : nvmDeltaG Σ} : dProp Σ :=
    ∃ (bz : bool),
      "#zPer" ∷ persist_lb z inv_z bz ∗
      "zPts" ∷ z ↦_{inv_z} [bz].

  Lemma left_crash_condition_impl {hD : nvmDeltaG Σ} (sx : list bool) :
    persist_lb x inv_x false -∗
    x ↦_{inv_x} sx -∗
    <PC> hD, left_crash_condition.
  Proof.
    iIntros "xPer xPts".
    iCrash.
    iDestruct "xPer" as (??) "[xPer #xRec]".
    iDestruct (crashed_in_or_lost with "xRec xPts") as (??) "[xPts xRec']".
    iDestruct (crashed_in_agree with "xRec xRec'") as %->.
    iExists _. iFrame "∗#".
  Qed.

  Lemma right_crash_condition_impl {hD : nvmDeltaG Σ} (sz : list bool) :
    persist_lb z inv_z false -∗
    z ↦_{inv_z} sz -∗
    <PC> hD, right_crash_condition.
  Proof.
    iIntros "zPer zPts".
    iCrash.
    iDestruct "zPer" as (??) "[zPer #zRec]".
    iDestruct (crashed_in_or_lost with "zRec zPts") as (??) "[zPts zRec']".
    iDestruct (crashed_in_agree with "zRec zRec'") as %->.
    iExists _. iFrame "∗#".
  Qed.

  (* Prove right crash condition. *)
  Ltac whack_right_cc :=
    iSplit;
    first iApply (right_crash_condition_impl with "zPer zPts").

  Ltac whack_left_cc :=
    iSplit;
    first iApply (left_crash_condition_impl with "xPer xPts").

  Lemma right_prog_spec s E1 :
    store_lb y inv_y false -∗
    ⎡ is_at_loc y ⎤ -∗
    persist_lb z inv_z false -∗
    z ↦_{inv_z} [false] -∗
    WPC rightProg y z @ s; E1
    {{ v, z ↦_{inv_z} [false; true] ∨ z ↦_{inv_z} [false] }}
    {{ <PC> _, right_crash_condition }}.
  Proof.
    iIntros "#yLb #yShared #zPer zPts".
    (* Evaluate the first load. *)
    rewrite /rightProg.
    wpc_bind (!_AT _)%E.
    iApply wpc_atomic_no_mask. whack_right_cc.
    iApply (wp_load_at _ _ (λ s v, (⌜v = #true⌝ ∗ flush_lb x inv_x true) ∨ ⌜v = #false⌝)%I inv_y with "[$yShared $yLb]").
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
      { iApply (right_crash_condition_impl with "zPer zPts"). }
      iModIntro.
      iRight. iFrame. }
    (* We loaded [true]. *)
    whack_right_cc.
    iModIntro.
    wpc_pures.
    { iApply (right_crash_condition_impl with "zPer zPts"). }
    wpc_bind (Fence).
    iApply wpc_atomic_no_mask. whack_right_cc.
    iApply wp_fence. do 2 iModIntro.
    iDestruct "disj" as "[[_ #xLb] | %]"; last congruence.
    whack_right_cc.
    iModIntro.
    wpc_pures.
    { iApply (right_crash_condition_impl with "zPer zPts"). }

    iApply wpc_atomic_no_mask. whack_right_cc.
    iApply (wp_store_na _ inv_z _ _ _ true with "[$zPts]"); eauto.
    { simpl. iFrame "xLb". done. }

    iIntros "!> zPts /=".
    whack_right_cc.
    iModIntro.
    iLeft. iFrame.
  Qed.

  Lemma prog_spec :
    ⎡ pre_borrow ⎤ ∗
    (* know_protocol x inv_x ∗ know_protocol y inv_y ∗ know_protocol z inv_z ∗ *)
    persist_lb x inv_x false ∗
    x ↦_{inv_x} [false] ∗
    store_lb y inv_y false ∗
    ⎡ is_at_loc y ⎤ ∗
    persist_lb z inv_z false ∗
    z ↦_{inv_z} [false] -∗
    WPC prog x y z @ ⊤
    {{ v, True }}
    {{ <PC> _, crash_condition }}.
  Proof.
    iIntros "(pb & #xPer & xPts & #yLb & #yShared & #zPer & zPts)".
    rewrite /prog.

    (* We create a crash borrow in order to transfer resources to the forked
    thread. *)
    iApply (wpc_crash_borrow_inits _ _ _ _ _ (<PC> _, right_crash_condition)%I
             with "pb [zPts]").
    { iAccu. }
    { iModIntro. iIntros "zPts".
      iApply (right_crash_condition_impl with "zPer zPts"). }
    iIntros "cb".

    iApply (wpc_crash_mono _ _ _ _ _ (<PC> _, left_crash_condition)%I).
    { iIntros "L R".
      iCrash.
      iNamed "L".
      iNamed "R".
      iExists _, _.
      iFrame "∗#". }
    Unshelve. 2: { apply _. }

    wpc_bind (Fork _)%E.
    iApply (wpc_fork with "[cb]").
    - (* Show safety of the forked off thread. *)
      iApply (wpc_crash_borrow_open_modify with "cb"); first done.
      iNext. iSplit; first done.
      iIntros "zPts".

      iDestruct (right_prog_spec with "yLb yShared zPer zPts") as "wp".
      iApply (wpc_mono' with "[] [] wp"); last naive_solver.
      iIntros (?) "[zPts | zPts]".
      * iExists (z ↦_{_} (_ : list bool)). iFrame.
        iSplit; last naive_solver.
        iIntros "!> zPts".
        iApply (right_crash_condition_impl with "zPer zPts").
      * iExists (z ↦_{_} (_ : list bool)). iFrame.
        iSplit; last naive_solver.
        iIntros "!> zPts".
        iApply (right_crash_condition_impl with "zPer zPts").
    - whack_left_cc. iNext.
      wpc_pures.
      { iApply (left_crash_condition_impl with "xPer xPts"). }
      rewrite /leftProg.
      wpc_bind (_ <-_NA _)%E.
      iApply wpc_atomic_no_mask. whack_left_cc.
      iApply (wp_store_na x _ _ _ _ true with "[$xPts]").
      { reflexivity. } { done. }
      { rewrite /inv_x. done. }
      simpl.
      iNext. iIntros "xPts".
      whack_left_cc.
      iModIntro.
      wpc_pures;
        first iApply (left_crash_condition_impl with "xPer xPts").

      (* Flush *)
      wpc_bind (Flush _)%E.
      iApply wpc_atomic_no_mask.
      whack_left_cc.
      iApply (wp_flush_ex with "xPts"); first reflexivity.
      iNext.
      iIntros "[xPts #xLowerBound]".
      whack_left_cc.
      iModIntro.
      wpc_pures;
        first iApply (left_crash_condition_impl with "xPer xPts").

      (* The fence. *)
      wpc_bind (Fence)%E.
      iApply wpc_atomic_no_mask. whack_left_cc.
      iApply wp_fence. do 2 iModIntro.
      whack_left_cc.
      iModIntro.
      wpc_pures;
        first iApply (left_crash_condition_impl with "xPer xPts").

      wpc_bind (_ <-_AT _)%E.
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
