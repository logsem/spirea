(* This is then classic message passing example except with some differences.
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
     abstract_state_instances locations protocol.
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

  Definition recovery (x z : loc) : expr :=
    if: !_NA #z = #true
    then assert: !_NA #x = #true
    else #().

End program.

Section proof.
  Context `{nvmG Σ, inG Σ (exclR unitO)}.
  Context `{!stagedG Σ}.

  Context (x y z : loc) (γ__ex : gname).

  Definition inv_x : LocationProtocol bool :=
    {| p_inv (b : bool) v := ⌜ v = #b ⌝%I;
       p_bumper b := b; |}.

  Global Instance inv_x_cond : ProtocolConditions inv_x.
  Proof. split; try apply _. iIntros. by iApply post_crash_flush_pure. Qed.

  Definition inv_y :=
    {| p_inv (b : bool) (v : val) :=
        if b
        then ⌜ v = #true ⌝ ∗ flush_lb x inv_x true
        else ⌜ v = #false ⌝ ∗ ⎡ own γ__ex (Excl ()) ⎤;
      p_bumper := id; |}%I.

  Global Instance inv_y_cond : ProtocolConditions inv_y.
  Proof.
    split; try apply _.
    iIntros ([|] ?); simpl.
    - iIntros "[% lb]". iModIntro.
      iFrame "%".
      iApply persist_lb_to_flush_lb.
      iDestruct "lb" as "($ & ?)".
    - iIntros "[% H]". iModIntro. iFrame. done.
  Qed.

  (* Definition inv_z := inv_y. *)
  Definition inv_z : LocationProtocol bool :=
    {| p_inv (b : bool) v :=
        if b
        then ⌜ v = #true ⌝ ∗ flush_lb x inv_x true
        else ⌜ v = #false ⌝;
       p_bumper := id |}%I.

  Global Instance inv_z_cond : ProtocolConditions inv_z.
    split; try apply _.
    iIntros ([|] ?); simpl.
    - iIntros "[% lb]". iModIntro.
      iFrame "%".
      iApply persist_lb_to_flush_lb.
      iDestruct "lb" as "($ & ?)".
    - iIntros "H". iModIntro. done.
  Qed.

  (* Note: The recovery code does not use the [y] location, hence the crash
  condition does not mention [y] as we don't need it to be available after a
  crash. *)
  Definition crash_condition : dProp Σ :=
    ∃ (xss zss : list bool) (bx bz : bool),
      "#xPer" ∷ persist_lb x inv_x bx ∗
      "#zPer" ∷ persist_lb z inv_z bz ∗
      "xPts" ∷ x ↦_{inv_x} (xss ++ [bx]) ∗
      "zPts" ∷ z ↦_{inv_z} (zss ++ [bz]).

  Definition left_crash_condition : dProp Σ :=
    ∃ xss (bx : bool),
      "#xPer" ∷ persist_lb x inv_x bx ∗
      "xPts" ∷ x ↦_{inv_x} (xss ++ [bx]).

  Definition right_crash_condition : dProp Σ :=
    ∃ zss (bz : bool),
      "#zPer" ∷ persist_lb z inv_z bz ∗
      "zPts" ∷ z ↦_{inv_z} (zss ++ [bz]).

  Lemma crash_condition_impl xss zss bx bz :
    persist_lb x inv_x bx -∗
    persist_lb z inv_z bz -∗
    x ↦_{ inv_x} (xss ++ [bx]) -∗
    z ↦_{ inv_z} (zss ++ [bz]) -∗
    <PC> crash_condition.
  Proof.
    iIntros "xPer zPer xPts zPts".
    iCrashIntro.
    iDestruct "xPer" as "[#xPer (% & % & #xRec)]".
    iDestruct (crashed_in_if_rec with "xRec xPts") as (???) "[cras xPts]".
    iDestruct (crashed_in_agree with "xRec cras") as %->.
    iDestruct (crashed_in_persist_lb with "xRec") as "#per2".
    iClear "xPer".

    iDestruct "zPer" as "[#zPer (% & % & #zRec)]".
    iDestruct (crashed_in_if_rec with "zRec zPts") as (???) "[cras1 zPts]".
    iDestruct (crashed_in_agree with "zRec cras1") as %->.
    iDestruct (crashed_in_persist_lb with "zRec") as "#per3".

    rewrite /crash_condition.
    iExists _, _, _, _.
    iFrameF "per2".
    iFrameF "per3".

    rewrite !list_fmap_id.
    iFrame "xPts".
    iFrame "zPts".
  Qed.

  Lemma left_crash_condition_impl (sx : list bool) :
    persist_lb x inv_x false -∗
    x ↦_{inv_x} sx -∗
    <PC> left_crash_condition.
  Proof.
    iIntros "xPer xPts".
    iModIntro.
    iDestruct "xPer" as "[#xPer (% & % & #xRec)]".
    iDestruct (crashed_in_if_rec with "xRec xPts") as (???) "[cras xPts]".
    iDestruct (crashed_in_agree with "xRec cras") as %->.
    iDestruct (crashed_in_persist_lb with "xRec") as "#per2".
    iExists _, _. iFrame "∗#".
  Qed.

  Lemma right_crash_condition_impl (sz : list bool) :
    persist_lb z inv_z false -∗
    z ↦_{inv_z} sz -∗
    <PC> right_crash_condition.
  Proof.
    iIntros "zPer zPts".
    iModIntro.
    iDestruct "zPer" as "[#zPer (% & % & #zRec)]".
    iDestruct (crashed_in_if_rec with "zRec zPts") as (???) "[cras zPts]".
    iDestruct (crashed_in_agree with "zRec cras") as %->.
    iDestruct (crashed_in_persist_lb with "zRec") as "#per2".
    iExists _, _. iFrame "∗#".
  Qed.

  (* Prove right crash condition. *)
  Ltac solve_right_cc :=
    iSplit;
    first iApply (right_crash_condition_impl with "zPer zPts").

  Ltac solve_left_cc :=
    iSplit;
    first iApply (left_crash_condition_impl with "xPer xPts").

  Ltac solve_cc :=
    iSplit;
    iApply (crash_condition_impl with "xPer zPer xPts zPts").

  Lemma right_prog_spec s E1 :
    y ↦_AT^{inv_y} [false] -∗
    persist_lb z inv_z false -∗
    z ↦_{inv_z} [false] -∗
    WPC rightProg y z @ s; E1
    {{ v, z ↦_{inv_z} [false; true] ∨ z ↦_{inv_z} [false] }}
    {{ <PC> right_crash_condition }}.
  Proof.
    iIntros "yPts #zPer zPts".
    (* Evaluate the first load. *)
    rewrite /rightProg.
    wpc_bind (!_AT _)%E.
    iApply wpc_atomic_no_mask.
    solve_right_cc.
    iApply (wp_load_at_simple _ _
              (λ s v, (⌜v = #true⌝ ∗ flush_lb x inv_x true) ∨ ⌜v = #false⌝)%I
              inv_y with "[$yPts]").
    { iModIntro. iIntros (?? incl) "a". rewrite /inv_y.
      destruct sL.
      - iDestruct "a" as "[% #?]". iFrame "#". naive_solver.
      - iDestruct "a" as "[% O]". naive_solver. }
    iNext.
    iIntros (? v) "[yPts disj]".
    iDestruct (post_fence_extract' _ (⌜v = #true ∨ v = #false⌝)%I with "disj []") as %[-> | ->].
    { iIntros "[[-> _]|->]"; naive_solver. }
    2: {
      (* We loaded [false] and this case is trivial. *)
      solve_right_cc.
      iModIntro.
      wpc_pures.
      { iApply (right_crash_condition_impl with "zPer zPts"). }
      iModIntro.
      iRight. iFrame. }
    (* We loaded [true]. *)
    solve_right_cc.
    iModIntro.
    wpc_pures.
    { iApply (right_crash_condition_impl with "zPer zPts"). }
    wpc_bind (Fence).
    iApply wpc_atomic_no_mask. solve_right_cc.
    iApply wp_fence. do 2 iModIntro.
    iDestruct "disj" as "[[_ #xLb] | %]"; last congruence.
    solve_right_cc.
    iModIntro.
    wpc_pures.
    { iApply (right_crash_condition_impl with "zPer zPts"). }

    iApply wpc_atomic_no_mask. solve_right_cc.
    iApply (wp_store_na _ inv_z _ _ _ true with "[$zPts]"); eauto.
    { simpl. iFrame "xLb". done. }

    iIntros "!> zPts /=".
    solve_right_cc.
    iModIntro.
    iLeft. iFrame.
  Qed.

  Lemma prog_spec :
    pre_borrow_d ∗
    persist_lb x inv_x false ∗
    x ↦_{inv_x} [false] ∗
    y ↦_AT^{inv_y} [false] ∗
    persist_lb z inv_z false ∗
    z ↦_{inv_z} [false] -∗
    WPC prog x y z @ ⊤
    {{ v, True }}
    {{ <PC> crash_condition }}.
  Proof.
    iIntros "(pb & #xPer & xPts & #yPts & #zPer & zPts)".
    rewrite /prog.

    (* We create a crash borrow in order to transfer resources to the forked
    thread. *)
    iApply (wpc_crash_borrow_inits _ _ _ _ _ (<PC> right_crash_condition)%I
             with "pb [zPts]").
    { iAccu. }
    { iModIntro. iIntros "zPts".
      iApply (right_crash_condition_impl with "zPer zPts"). }
    iIntros "cb".

    iApply (wpc_crash_mono _ _ _ _ _ (<PC> left_crash_condition)%I).
    { iIntros "L R".
      iModIntro.
      iNamed "L".
      iNamed "R".
      iExists _, _, _, _.
      iFrame "xPts".
      iFrame "zPts".
      iFrame "xPer".
      iFrame "zPer". }
    Unshelve. 2: { apply _. }

    wpc_bind (Fork _)%E.
    iApply (wpc_fork with "[cb]").
    - (* Show safety of the forked off thread. *)
      iApply (wpc_crash_borrow_open_modify with "cb"); first done.
      iNext. iSplit; first done.
      iIntros "zPts".

      iDestruct (right_prog_spec with "yPts zPer zPts") as "wp".
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
    - solve_left_cc. iNext.
      wpc_pures.
      { iApply (left_crash_condition_impl with "xPer xPts"). }
      rewrite /leftProg.
      wpc_bind (_ <-_NA _)%E.
      iApply wpc_atomic_no_mask. solve_left_cc.
      iApply (wp_store_na x _ _ _ _ true with "[$xPts]").
      { reflexivity. } { done. }
      { rewrite /inv_x. done. }
      iNext. iIntros "xPts".
      solve_left_cc.
      iModIntro.
      wpc_pures;
        first iApply (left_crash_condition_impl with "xPer xPts").

      (* Flush *)
      wpc_bind (Flush _)%E.
      iApply wpc_atomic_no_mask.
      solve_left_cc.
      iApply (wp_flush_na with "xPts").
      iNext.
      iIntros "(xPts & #xLowerBound & ?)".
      solve_left_cc.
      iModIntro.
      wpc_pures;
        first iApply (left_crash_condition_impl with "xPer xPts").

      (* The fence. *)
      wpc_bind (Fence)%E.
      iApply wpc_atomic_no_mask. solve_left_cc.
      iApply wp_fence. do 2 iModIntro.
      solve_left_cc.
      iModIntro.
      wpc_pures;
        first iApply (left_crash_condition_impl with "xPer xPts").

      wpc_bind (_ <-_AT _)%E.
      iApply wpc_atomic_no_mask. solve_left_cc.
      iApply (wp_store_at _ inv_y [] false true with "[$yPts]").
      {
        iFrame "#".
        iSplitPure; first done.
        iSplitPure; first done.
        iIntros (? s_c v_c). simpl.
        destruct s_c; first naive_solver.
        iIntros "? ([? O1] & [??] & [? O2])".
        by iDestruct (own_valid_2 with "O1 O2") as %HI%exclusive_l. }
      iIntros "!> yLb2".
      solve_left_cc.
      done.
  Qed.

  Definition foo (b : bool) : iProp Σ := if b then ⌜ 1 = 1 ⌝ %I else ⌜ 2 = 2 ⌝%I.

  Instance if_else_persistent {PROP : bi} (b : bool) (P Q : PROP) :
    Persistent P →
    Persistent Q →
    Persistent (if b then P else Q).
  Proof. intros ??. destruct b; done. Qed.

  Lemma recovery_prog_spec s E :
    crash_condition -∗
    WPC recovery x z @ s; E
      {{ _, True }}
      {{ <PC> crash_condition }}.
  Proof.
    iNamed 1.
    rewrite /recovery.
    wpc_bind (!_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit.
    { iApply (crash_condition_impl with "xPer zPer xPts zPts"). }

    iApply (wp_load_na with "[$zPts]").
    { apply last_snoc. }
    { iModIntro.
      iIntros (?). iIntros "#H". iFrame "H". rewrite right_id. iApply "H". }
    iNext. iIntros (?) "[zPts pred]".
    iSplit.
    { iModIntro. iApply (crash_condition_impl with "xPer zPer xPts zPts"). }
    iModIntro.
    destruct bz.
    - iDestruct "pred" as "[-> lb]".
      rewrite /assert.
      wpc_pures.
      { iApply (crash_condition_impl with "xPer zPer xPts zPts"). }
      wpc_bind (!_NA _)%E.
      iApply wpc_atomic_no_mask.
      iSplit.
      { iApply (crash_condition_impl with "xPer zPer xPts zPts"). }
      iDestruct (mapsto_na_flush_lb_incl with "lb xPts") as %[= ->].

      iApply (wp_load_na with "[$xPts]").
      { apply last_snoc. }
      { iModIntro. simpl.
        iIntros (?). iIntros "#H". iFrame "H". rewrite right_id. iApply "H". }
      iNext. iIntros (?) "[xPts ->]".
      iSplit.
      { iModIntro. iApply (crash_condition_impl with "xPer zPer xPts zPts"). }
      iModIntro.
      wpc_pures.
      { iApply (crash_condition_impl with "xPer zPer xPts zPts"). }
      by iModIntro.
    - iDestruct "pred" as %->.
      wpc_pures.
      { iApply (crash_condition_impl with "xPer zPer xPts zPts"). }
      by iModIntro.
  Qed.

End proof.
