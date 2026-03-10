(* This is then classic message passing example except with some differences.
   The sending thread ([leftProg] below) ensures that it only sends [x] after
   having flushed and fenced it. The receieving thread ([rightProg] below) saves
   and acknowledgement to [z] and with a fence ensures that it is only persisted
   after the send values is persisted.

   The recovery code ([recovery] below) relies on this being true and crashes
   otherwise. Hence showing safety of the recovery code ensures that the
   intuitive property that we expect to hold does indeed hold. *)

From Equations Require Import Equations.
From iris.proofmode Require Import proofmode monpred coq_tactics.
From iris.algebra Require Import gmap_view excl.
From iris_named_props Require Import named_props.
From nextgen Require Import cmra_morphism_extra gmap_view_transformation.

From self Require Import extra solve_view_le encode_relation map_extra view_slice.

From self.lang Require Import syntax tactics lemmas.

From self.base Require Import generational_resources primitive_laws.

From self.high Require Import wrappers monpred_simpl protocol locations crash_weakestpre weakestpre wpc_proofmode.
From self.high.modalities Require Import post_fence_sync_advanced.
From self.high.lib Require Import abstract_state abstract_state_instances increasing_map protocols.
From self.high Require Import weakestpre_at weakestpre_na weakestpre_exp proofmode.

From self Require Export lang.
From self.high Require Export dprop.

Section program.
  Definition leftProg (y z : loc) : expr :=
    if: !_AT #y = #true
    then Fence ;; #z <-_NA #true
    else #().

  Definition rightProg (x y : loc) : expr :=
    #x <-_NA #true ;;
    Flush #x ;;
    Fence ;;
    #y <-_AT #true.

  Definition prog (x y z : loc) : expr :=
    Fork (rightProg x y) ;; leftProg y z.
  
  Definition recovery (x z : loc) : expr :=
    if: !_NA #z = #true
    then assert: !_NA #x = #true
    else #().
End program.

Class tokenG (Σ: gFunctors) (Ω: gGenCmras Σ) := {
  token_inG :: genInDepsG Σ Ω (exclR unitO) [#];
}.

Definition token_trans: exclR unitO → exclR unitO := λ _, Excl ().

Section proof.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ, !tokenG Σ Ω}.
  Context (x y z : loc) (γ__x γ__y γ__z : gname).

  Definition inv_x : LocationProtocol bool :=
    {| p_full (b : bool) v := ⌜ v = #b ⌝%I;
       p_read (b : bool) v := ⌜ v = #b ⌝%I;
       p_pers (b : bool) v := ⌜ v = #b ⌝%I;
       p_bumper b := b; |}.

  #[global] Instance inv_x_cond : ProtocolConditions inv_x.
  Proof.
    split; try apply _; rewrite /p_full /p_read /p_pers /=.
    - intros.
      iSplit; first naive_solver.
      iIntros "[$ _]".
    - iIntros.
      iSplit.
      + by do 2 iModIntro.
      + iIntros (??) "!> % % %".
        by do 2 iModIntro.
    - iIntros.
      by iModIntro.
  Qed.

  Definition token_pack γ: dProp Σ := ⎡ gen_own γ (Excl ()) ∗ rely_self γ (λ t, t = token_trans) ⎤.

  Lemma token_pack_excl γ:
    token_pack γ -∗ token_pack γ -∗ False.
  Proof.
    iIntros "[own1 _] [own2 _]".
    iDestruct (gen_own_valid_2 with "[$] [$]") as %[]%exclusive_l.
  Qed.

  #[global] Instance token_nextgen γ:
    IntoNextgen (token_pack γ) (token_pack γ).
  Proof.
    rewrite /IntoNextgen.
    iIntros "[own rely]".
    iModIntro.
    iDestruct "own" as (t) "[picked own]".
    iDestruct "rely" as "[$ (% & % & picked')]".
    iPickedInAgree "picked picked'".
    subst.
    rewrite /token_trans /=.
    done.
  Qed.
  
  #[global] Instance token_nextgen_flush γ:
    IntoNGFlush (token_pack γ) (token_pack γ).
  Proof.
    rewrite /IntoNGFlush.
    iIntros "[own rely]".
    iApply nextgen_flush_nextgen.
    iModIntro.
    iDestruct "own" as (t) "[picked own]".
    iDestruct "rely" as "[$ (% & % & picked')]".
    iPickedInAgree "picked picked'".
    subst.
    rewrite /token_trans /=.
    done.
  Qed.

  #[global] Instance token_pack_objective γ:
    Objective (token_pack γ).
  Proof. apply _. Qed.
  
  
  #[global] Instance token_pack_buffer_free γ:
    BufferFree (token_pack γ).
  Proof. apply _. Qed.
  
  Definition x_pack: dProp Σ :=
    (∃ ss, x ↦_{inv_x} (ss ++ [true])) ∗ flush_lb x inv_x true.

  #[global] Instance x_pack_buffer_free:
    BufferFree (x_pack).
  Proof.
    rewrite /IntoNoBuffer.
    iIntros "[[% xPts] #xFlush]".
    iModIntro.
    iSplit; last done.
    by iExists _.
  Qed.
      
  #[global] Instance x_pack_nextgen_flush:
    IntoNGFlush (x_pack) (x_pack).
  Proof.
    rewrite /IntoNGFlush /x_pack.
    iIntros "[[% xPts] #xFlush]".
    iModIntro.
    iDestruct "xFlush" as "[xPers (% & % & xCrashed)]".
    assert (s__pc = true) as -> by done.
    iDestruct (crashed_in_if_rec inv_x with "[$] [$]") as (???) "[xCrashed' xPts]".
    iDestruct (crashed_in_agree with "[$] [$]") as "->".
    rewrite /p_bumper list_fmap_id /=.
    iSplit; last by iApply persist_lb_to_flush_lb.
    by iExists _.
  Qed.
  
  Opaque x_pack token_pack.

  Definition inv_y :=
    {| p_full (b : bool) (v : val) :=
        ⌜ v = #b ⌝ ∗
        if b
        then (x_pack ∨ token_pack γ__x)
        else token_pack γ__y;
       p_read (b: bool) (v: val) := 
        ⌜ v = #b ⌝ ∗
        if b
        then (x_pack ∨ token_pack γ__x)
        else token_pack γ__y;
       p_pers (b: bool) (v: val) := ⌜ v = #b ⌝%I;
       p_bumper := id; |}%I.
  
  #[global] Instance inv_y_cond : ProtocolConditions inv_y.
  Proof.
    split; try apply _; rewrite /p_full /p_read /p_pers /=.
    - intros.
      iSplit.
      + iIntros "$".
        iIntros "$".
      + iIntros "[$ _]".
    - iIntros (??????) "[% H]".
      simplify_map_eq.
      iSplit.
      + destruct (σ_f); do 2 iModIntro; naive_solver.
      + iIntros (??) "!> [% H] % %".
        simplify_map_eq.
        destruct (σ_c); do 2 iModIntro; naive_solver.
    - iIntros ([|] ?) "[% H] !>"; naive_solver.
  Qed.

  Definition inv_z :=
    {| p_full (b : bool) (v : val) :=
        ⌜ v = #b ⌝ ∗
        if b
        then (x_pack ∨ token_pack γ__z)
        else True;
       p_read (b: bool) (v: val) := 
        ⌜ v = #b ⌝ ∗
        if b
        then (x_pack ∨ token_pack γ__z)
        else True;
       p_pers (b: bool) (v: val) := ⌜ v = #b ⌝%I;
       p_bumper := id; |}%I.
  
  #[global] Instance inv_z_cond : ProtocolConditions inv_z.
  Proof.
    split; try apply _; rewrite /p_full /p_read /p_pers /=.
    - intros.
      iSplit.
      + iIntros "$".
        iIntros "$".
      + iIntros "[$ _]".
    - iIntros (??????) "[% H]".
      simplify_map_eq.
      iSplit.
      + destruct (σ_f); do 2 iModIntro; naive_solver.
      + iIntros (??) "!> [% H] % %".
        simplify_map_eq.
        destruct (σ_c); do 2 iModIntro; naive_solver.
    - iIntros ([|] ?) "[% H] !>"; naive_solver.
  Qed.
  
  (* Note: The recovery code does not use the [y] location, hence the crash
  condition does not mention [y] as we don't need it to be available after a
  crash. *)
  Definition crash_condition : dProp Σ :=
    ∃ (ss : list bool) (b : bool),
      "tok" ∷ token_pack γ__z ∗
      "#zPer" ∷ persist_lb z inv_z b ∗
      "zPts" ∷ z ↦_{inv_z} (ss ++ [b]).

  Lemma crash_condition_impl b ss :
    token_pack γ__z -∗
    persist_lb z inv_z b -∗
    z ↦_{inv_z} (ss) -∗
    <NG> crash_condition.
  Proof.
    iIntros "tok #zPers zPts".
    iModIntro.
    iDestruct "zPers" as "[zPers (% & % & xCrashed)]".
    iDestruct (crashed_in_if_rec inv_z with "[$] [$]") as (???) "[zCrashed' zPts]".
    iDestruct (crashed_in_agree with "[$] [$]") as "->".
    iDestruct (crashed_in_persist_lb with "xCrashed") as "#per2".
    rewrite /p_bumper list_fmap_id /=.
    iExists _, _.
    iFrameNamed.
    done.
  Qed.

  (* Prove right crash condition. *)
  Ltac solve_right_cc :=
    iSplit;
    first done.

  Ltac solve_left_cc :=
    iSplit;
    first
      iApply (crash_condition_impl with "tok zPer zPts").

  Ltac solve_cc := solve_left_cc.
    (* iSplit; *)
    (* iApply (crash_condition_impl with "xPer zPer xPts zPts"). *)

  Lemma right_prog_spec s E1 :
    x ↦_{inv_x} [false] -∗
    y ↦_AT^{inv_y} [false] -∗
    (WPC rightProg x y @ s; E1
    {{ _, True }}
    {{ True }}).
  Proof.
    iIntros "xPts #yPts".
    rewrite /rightProg.
    wpc_bind (_ <-_NA _)%E.
    iApply wpc_atomic_no_mask. solve_right_cc.
    iApply (wp_store_na x _ _ _ _ true with "[$xPts]").
    { reflexivity. } { done. }
    { rewrite /inv_x. done. }
    iNext. iIntros "xPts".
    solve_right_cc.
    iModIntro.
    wpc_pures; first done.

    (* Flush *)
    wpc_bind (Flush _)%E.
    iApply wpc_atomic_no_mask. solve_right_cc.
    iApply (wp_flush_na with "xPts").
    iNext.
    iIntros "(xPts & #xLowerBound & _)".
    solve_right_cc.
    iModIntro.
    wpc_pures; first done.

    (* The fence. *)
    wpc_bind (Fence)%E.
    iApply wpc_atomic_no_mask. solve_right_cc.
    iApply wp_fence. do 2 iModIntro.
    solve_right_cc.
    iModIntro.
    wpc_pures; first done.

    wpc_bind (_ <-_AT _)%E.
    iApply wpc_atomic_no_mask. solve_right_cc.
    iApply (wp_store_at _ inv_y [] false true with "[$yPts xPts]").
    {
      iFrame "#".
      iSplitL.
      { rewrite /p_full /=.
        iSplitPure; first done.
        iLeft.
        Transparent x_pack.
        iSplitL; last done.
        - by iExists [false]. }
      iSplitPure; first done.
      iIntros (? s_c v_c). simpl.
      destruct s_c; first naive_solver.
      iIntros "? ([? O1] & [??] & [? O2])".
      iDestruct (token_pack_excl with "[$] [$]") as %[]. }
    iIntros "!> yLb2".
    iSplit; done.
  Qed.

  Lemma prog_spec :
    token_pack γ__z ∗
    token_pack γ__x ∗
    x ↦_{inv_x} [false] ∗
    y ↦_AT^{inv_y} [false] ∗
    persist_lb z inv_z false ∗
    z ↦_{inv_z} [false] -∗
    WPC prog x y z @ ⊤
    {{ v, z ↦_{inv_z} [false; true] ∨ z ↦_{inv_z} [false] }}
    {{ <NG> crash_condition }}.
  Proof.
    iIntros "(tok & tok__x & xPts & #yPts & #zPer & zPts)".
    rewrite /prog.

    wpc_bind (Fork _)%E.
    iApply (wpc_fork with "[xPts]").
    - (* Show safety of the forked off thread. *)
      iDestruct (right_prog_spec with "xPts yPts") as "$wp".
    - solve_left_cc. iNext.
      wpc_pures; first iApply (crash_condition_impl with "tok zPer zPts").
      rewrite /leftProg.
      wpc_bind (!_AT _)%E.
      iApply wpc_atomic_no_mask.
      solve_left_cc.
      iApply (wp_load_at_simple _ _
                (λ (s: bool) v, ⌜ v = #s ⌝ ∗ if s then x_pack else True)%I
                inv_y with "[$yPts tok__x]").
      { iModIntro.
        iIntros ([|] ??) "[-> H]"; simpl; last naive_solver.
        iDestruct "H" as "[H | H]".
        - by iFrame.
        - iDestruct (token_pack_excl with "[$] [$]") as %[]. }
      iNext.
      iIntros (? v) "[_ [% disj]]". subst v.
      destruct sL.
      2: {
        (* We loaded [false] and this case is trivial. *)
        solve_left_cc.
        iModIntro.
        wpc_pures.
        { iApply (crash_condition_impl with "tok zPer zPts"). }
        iModIntro.
        iRight. iFrame. }
      (* We loaded [true]. *)
      solve_left_cc.
      iModIntro.
      wpc_pures.
      { iApply (crash_condition_impl with "tok zPer zPts"). }
      wpc_bind (Fence).
      iApply wpc_atomic_no_mask. solve_left_cc.
      iApply wp_fence. do 2 iModIntro.
      solve_left_cc.
      iModIntro.
      wpc_pures.
      { iApply (crash_condition_impl with "tok zPer zPts"). }

      iApply wpc_atomic_no_mask. solve_left_cc.
      iApply (wp_store_na _ inv_z _ _ _ true with "[$zPts disj]"); eauto.
      { simpl. iFrame "disj". done. }

      iIntros "!> zPts /=".
      solve_left_cc.
      iModIntro.
      iLeft. iFrame.
  Qed.

  Instance if_else_persistent {PROP : bi} (b : bool) (P Q : PROP) :
    Persistent P →
    Persistent Q →
    Persistent (if b then P else Q).
  Proof. intros ??. destruct b; done. Qed.

  (* TODO: with a more complicated crash condition, we can verify idempotence,
   * but it's not the point here so I'm simplifying it for now. *)
  Lemma recovery_prog_spec s E :
    crash_condition -∗
    WP recovery x z @ s; E
      {{ _, True }}.
  Proof.
    iNamed 1.
    rewrite /recovery.
    wp_bind (!_NA _)%E.
    
    iApply (wp_load_na _ _ _ _ (λ v, (⌜ v = #true ⌝ ∗ x_pack) ∨ ⌜ v = #false ⌝)%I with "[$zPts tok]").
    { apply last_snoc. }
    { iModIntro.
      simpl.
      iIntros (?) "[-> H]".
      destruct b; last naive_solver.
      iDestruct "H" as "[H | H]"; last iDestruct (token_pack_excl with "[$] [$]") as %[].
      iSplitL "H".
      - iLeft. naive_solver.
      - iSplitPure; first done.
        by iRight. }
    iNext. iIntros (?) "[zPts H]".
    iDestruct "H" as "[[-> H] | ->]".
    - rewrite /assert.
      wp_pures.
      Transparent x_pack.
      iDestruct ("H") as "[[% xPts] xFlush]".
      wp_bind (!_NA _)%E.
      
      iApply (wp_load_na with "[$xPts]").
      { apply last_snoc. }
      { iModIntro. simpl.
        iIntros (?). iIntros "#H". iFrame "H". rewrite right_id. iApply "H". }
      iNext. iIntros (?) "[xPts ->]".
      wp_pures.
      done.
    - by wp_pures.
  Qed.
End proof.
