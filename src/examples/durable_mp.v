(* This is then classic message passing example except with some differences.
   The sending thread ([leftProg] below) ensures that it only sends [x] after
   having flushed and fenced it. The receieving thread ([rightProg] below) saves
   and acknowledgement to [z] and with a fence ensures that it is only persisted
   after the send values is persisted.

   The recovery code ([recovery] below) relies on this being true and crashes
   otherwise. Hence showing safety of the recovery code ensures that the
   intuitive property that we expect to hold does indeed hold. *)

From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris_named_props Require Import named_props.
From self.nextgen Require Import nextgen_promises.

(* For [PerennialG] *)
From self.base Require Import primitive_laws wpr_lifting.
From self.high Require Import
  generational_resources dprop protocol locations crash_weakestpre weakestpre wpc_proofmode modalities.
From self.high.modalities Require Import fence_sync_atomic.
From self.high.lib Require Import abstract_state abstract_state_instances protocols.
From self.high Require Import weakestpre_at weakestpre_na.
From self.high Require Import recovery_weakestpre adequacy.

From self.lang Require Import syntax notation tactics lemmas lang.

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

Definition token_trans: exclR unitO → exclR unitO := id.

Section proof.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ, !tokenG Σ Ω}.
  Context (x y z : loc) (γ__x γ__y γ__z : gname).

  Definition inv_x : LocationProtocol bool :=
    {| p_full (b : bool) v := ⌜ v = #b ⌝%I;
       p_read (b : bool) v := ⌜ v = #b ⌝%I;
       p_pers (b : bool) v := ⌜ v = #b ⌝%I;
       p_bumper b := b; |}.

  #[global] Instance inv_x_cond ℓ : ProtocolConditions ℓ inv_x.
  Proof.
    split; try apply _; rewrite /p_full /p_read /p_pers /=.
    - intros.
      iSplit; first naive_solver.
      iIntros "[$ _]".
    - iIntros.
      iSplit.
      + by iIntros "!>!> _".
      + iIntros (??) "!> % % %".
        by iIntros "!>!> _".
    - iIntros.
      by iModIntro.
  Qed.

  Definition token_pack γ: dProp Σ := ⎡ gen_own γ (Excl ()) ∗ rely_self γ (λ t, t = token_trans) ⎤.

  Lemma token_pack_alloc:
    ⊢ |==> ∃ γ, token_pack γ.
  Proof.
    iMod (own_gen_alloc (DS := [#]) (Excl ()) [#] [##] with "[]") as (γ) "[Hown Htok]".
    { done. }
    { iIntros (Hcontr). inversion Hcontr. }
    iMod (token_strengthen_promise_0_deps _ _ (λ t, t = token_trans) with "Htok") as "Htok"; auto.
    { intros; done. }
    { exists id. split; last done.
      apply _. }
    iModIntro.
    iExists γ.
    iFrame.
    iApply (rely_to_rely_self).
    by iApply token_to_rely.
  Qed.
  
  Lemma token_pack_excl γ:
    token_pack γ -∗ token_pack γ -∗ False.
  Proof.
    iIntros "[own1 _] [own2 _]".
    iDestruct (gen_own_valid_2 with "[$] [$]") as %[]%exclusive_l.
  Qed.

  #[global] Instance token_nextgen γ:
    nextgen.IntoNextgen (token_pack γ) (token_pack γ).
  Proof.
    rewrite /nextgen.IntoNextgen.
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
    (∃ σs, x ↦_{inv_x} (σs ++ [true])) ∗ flush_lb x inv_x true.

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
    assert (σ__pc = true) as -> by done.
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
  
  #[global] Instance inv_y_cond ℓ : ProtocolConditions ℓ inv_y.
  Proof.
    split; try apply _; rewrite /p_full /p_read /p_pers /=.
    - intros.
      iSplit.
      + iIntros "$".
        iIntros "$".
      + iIntros "[$ _]".
    - iIntros "_" (??????) "[% H]".
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
        then flush_lb x inv_x true ∗ (x_pack ∨ token_pack γ__z)
        else True;
       p_read (b: bool) (v: val) := 
        ⌜ v = #b ⌝ ∗
        if b
        then flush_lb x inv_x true ∗ (x_pack ∨ token_pack γ__z)
        else True;
       p_pers (b: bool) (v: val) := ⌜ v = #b ⌝%I;
       p_bumper := id; |}%I.
  
  #[global] Instance inv_z_cond ℓ : ProtocolConditions ℓ inv_z.
  Proof.
    split; try apply _; rewrite /p_full /p_read /p_pers /=.
    - intros.
      iSplit.
      + iIntros "$".
        iIntros "$".
      + iIntros "[$ _]".
    - iIntros "_" (??????) "[% H]".
      simplify_map_eq.
      iSplit.
      + destruct (σ_f); iIntros "!>!> _"; last naive_solver.
        iSplitL; last done.
        iSplitR; first done.
        iDestruct "H" as "[[xPer _] $]".
        by iApply persist_lb_to_flush_lb.
      + iIntros (??) "!> [% H] % %".
        simplify_map_eq.
        destruct (σ_c); iIntros "!>!> _"; last naive_solver.
        iSplitL; last done.
        iSplitR; first done.
        iDestruct "H" as "[[xPer _] $]".
        by iApply persist_lb_to_flush_lb.
    - iIntros ([|] ?) "[% H] !>"; last done.
      subst v.
      iSplitR; first done.
      iDestruct "H" as "[[xPer _] $]".
      by iApply persist_lb_to_flush_lb.
  Qed.
  
  (* Note: The recovery code does not use the [y] location, hence the crash
  condition does not mention [y] as we don't need it to be available after a
  crash. *)
  Definition crash_condition : dProp Σ :=
    ∃ (σ__x σ__z: bool) (σs__z: list bool),
      "xPer" ∷ persist_lb x inv_x σ__x ∗
      "x_or_token" ∷ ((∃ σs__x, x ↦_{ inv_x } (σs__x ++ [σ__x])) ∨ token_pack γ__z) ∗
      "#zPer" ∷ persist_lb z inv_z σ__z ∗
      "zPts" ∷ z ↦_{inv_z} (σs__z ++ [σ__z]).

  Lemma crash_condition_impl σ__x σ__z σs__z:
    persist_lb x inv_x σ__x -∗
    token_pack γ__z -∗
    persist_lb z inv_z σ__z -∗
    z ↦_{inv_z} (σs__z) -∗
    <NG> crash_condition.
  Proof.
    iIntros "#xPer tok #zPer zPts".
    iModIntro.
    iDestruct "zPer" as "[zPer' (% & % & zCrashed)]".
    iDestruct (crashed_in_if_rec inv_z with "[$] [$]") as (???) "[zCrashed' zPts]".
    iDestruct (crashed_in_agree with "[$] [$]") as "->".
    iDestruct (crashed_in_persist_lb with "zCrashed") as "#zPer".
    iDestruct "xPer" as "[xPer (% & % & xCrashed)]".
    rewrite /p_bumper ?list_fmap_id /=.
    iExists _, σ_c, σs'.
    iFrame "xPer".
    iSplitL "tok".
    - by iRight.
    - iFrameNamed.
  Qed.

  (* Prove right crash condition. *)
  Ltac solve_right_cc :=
    iSplit;
    first done.

  Ltac solve_left_cc :=
    iSplit;
    first
      iApply (crash_condition_impl with "xPer tok zPer zPts").

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

  Lemma prog_spec s:
    token_pack γ__z ∗
    token_pack γ__x ∗
    x ↦_{inv_x} [false] ∗
    y ↦_AT^{inv_y} [false] ∗
    persist_lb x inv_x false ∗
    persist_lb z inv_z false ∗
    z ↦_{inv_z} [false] -∗
    WPC prog x y z @ s; ⊤
    {{ v, z ↦_{inv_z} [false; true] ∨ z ↦_{inv_z} [false] }}
    {{ <NG> crash_condition }}.
  Proof.
    iIntros "(tok & tok__x & xPts & #yPts & #xPer & #zPer & zPts)".
    rewrite /prog.

    wpc_bind (Fork _)%E.
    iApply (wpc_fork with "[xPts]").
    - (* Show safety of the forked off thread. *)
      iDestruct (right_prog_spec with "xPts yPts") as "$wp".
    - solve_left_cc. iNext.
      wpc_pures; first iApply (crash_condition_impl with "xPer tok zPer zPts").
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
        { iApply (crash_condition_impl with "xPer tok zPer zPts"). }
        iModIntro.
        iRight. iFrame. }
      (* We loaded [true]. *)
      solve_left_cc.
      iModIntro.
      wpc_pures.
      { iApply (crash_condition_impl with "xPer tok zPer zPts"). }
      wpc_bind (Fence).
      iApply wpc_atomic_no_mask. solve_left_cc.
      iApply wp_fence. do 2 iModIntro.
      solve_left_cc.
      iModIntro.
      wpc_pures.
      { iApply (crash_condition_impl with "xPer tok zPer zPts"). }

      iApply wpc_atomic_no_mask. solve_left_cc.
      iApply (wp_store_na _ inv_z _ _ _ true with "[$zPts disj]"); eauto.
      { iDestruct "disj" as "[xPts #$]".
        iSplitR; first done.
        by iLeft. }

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

  Lemma crash_condition_impl' σ__x σ__z σs__z σs__x:
    persist_lb x inv_x σ__x -∗
    x ↦_{inv_x} (σs__x) -∗
    persist_lb z inv_z σ__z -∗
    z ↦_{inv_z} (σs__z) -∗
    <NG> crash_condition.
  Proof.
    iIntros "#xPer xPts #zPer zPts".
    iModIntro.
    iDestruct "zPer" as "[zPer' (% & % & zCrashed)]".
    iDestruct (crashed_in_if_rec inv_z with "[$] [$]") as (???) "[zCrashed' zPts]".
    iDestruct (crashed_in_agree with "[$] [$]") as "->".
    iDestruct (crashed_in_persist_lb with "zCrashed") as "#zPer".
    iDestruct "xPer" as "[xPer' (% & % & xCrashed)]".
    iDestruct (crashed_in_if_rec inv_x with "xCrashed [$]") as (???) "[xCrashed' xPts]".
    iDestruct (crashed_in_agree with "xCrashed' xCrashed") as "->".
    iDestruct (crashed_in_persist_lb with "xCrashed") as "#xPer".
    rewrite /p_bumper ?list_fmap_id /=.
    iExists _, _, _.
    iFrame "xPer".
    iSplitL "xPts"; last iFrameNamed.
    iLeft.
    by iExists _.
  Qed.

  Lemma recovery_prog_spec s E :
    crash_condition -∗
    WPC recovery x z @ s; E
      {{ _, True }} {{ <NG> crash_condition }}.
  Proof.
    iNamed 1.
    iDestruct "x_or_token" as "[[% xPts] | tok]".
    - rewrite /recovery.
      wpc_bind (!_NA _)%E.
      iApply wpc_atomic_no_mask.
      iSplit.
      { iApply (crash_condition_impl' with "xPer xPts zPer zPts"). }
      iApply (wp_load_na _ _ _ _ (λ v, (⌜ v = #true ⌝ ∗ flush_lb x inv_x true) ∨ ⌜ v = #false ⌝)%I with "[$zPts]").
      { apply last_snoc. }
      { iModIntro.
        simpl.
        iIntros (?) "[-> H]".
        destruct σ__z; last naive_solver.
        iDestruct "H" as "[#xFlush H]".
        iSplitR; last naive_solver.
        naive_solver. }
      iNext. iIntros (?) "[zPts H]".
      iDestruct "H" as "[[-> #xFlush] | ->]".
      + iPoseProof (mapsto_na_flush_lb_incl with "xFlush xPts") as "%Horder".
        assert (σ__x = true) as -> by done.
        iSplit.
        { iModIntro. iApply (crash_condition_impl' with "xPer xPts zPer zPts"). }
        iModIntro.
        rewrite /assert.
        wpc_pures.
        { iApply (crash_condition_impl' with "xPer xPts zPer zPts"). }
        wpc_bind (!_NA _)%E.
        iApply wpc_atomic_no_mask. iSplit.
        { iApply (crash_condition_impl' with "xPer xPts zPer zPts"). }
        iApply (wp_load_na with "[$xPts]").
        { apply last_snoc. }
        { iModIntro. simpl.
          iIntros (?). iIntros "#H". iFrame "H". rewrite right_id. iApply "H". }
        iNext. iIntros (?) "[xPts ->]".
        iSplit.
        { iApply (crash_condition_impl' with "xPer xPts zPer zPts"). }
        iModIntro.
        wpc_pures.
        { iApply (crash_condition_impl' with "xPer xPts zPer zPts"). }
        done.
      + iSplit.
        { iApply (crash_condition_impl' with "xPer xPts zPer zPts"). }
        iModIntro.
        wpc_pures.
        { iApply (crash_condition_impl' with "xPer xPts zPer zPts"). }
        done.
    - rewrite /recovery.
      wpc_bind (!_NA _)%E.
      iApply wpc_atomic_no_mask.
      solve_left_cc.
      iApply (wp_load_na _ _ _ _ (λ v, (⌜ v = #true ⌝ ∗ x_pack) ∨ (⌜ v = #false ⌝ ∗ token_pack γ__z))%I with "[$zPts tok]").
      { apply last_snoc. }
      { iModIntro.
        simpl.
        iIntros (?) "[-> H]".
        destruct σ__z; last naive_solver.
        iDestruct "H" as "[$ [H | H]]"; last iDestruct (token_pack_excl with "[$] [$]") as %[].
        iSplitL "H".
        - iLeft. naive_solver.
        - iSplitPure; first done.
          by iRight. }
      iNext. iIntros (?) "[zPts H]".
      iDestruct "H" as "[[-> H] | [-> tok]]".
      + iDestruct ("H") as "[[% xPts] xFlush]".
        iSplit.
        { iModIntro. iApply (crash_condition_impl' with "xPer xPts zPer zPts"). }
        iModIntro.
        rewrite /assert.
        wpc_pures.
        { iApply (crash_condition_impl' with "xPer xPts zPer zPts"). }
        wpc_bind (!_NA _)%E.
        iApply wpc_atomic_no_mask. iSplit.
        { iApply (crash_condition_impl' with "xPer xPts zPer zPts"). }
        iApply (wp_load_na with "[$xPts]").
        { apply last_snoc. }
        { iModIntro. simpl.
          iIntros (?). iIntros "#H". iFrame "H". rewrite right_id. iApply "H". }
        iNext. iIntros (?) "[xPts ->]".
        iSplit.
        { iApply (crash_condition_impl' with "xPer xPts zPer zPts"). }
        iModIntro.
        wpc_pures.
        { iApply (crash_condition_impl' with "xPer xPts zPer zPts"). }
        done.
      + solve_left_cc.
        iModIntro.
        wpc_pures.
        { iApply (crash_condition_impl with "xPer tok zPer zPts"). }
        done.
  Qed.

  Definition φ (v: val): Prop := True.

  Lemma simple_prog_spec (s: stuckness):
    token_pack γ__z ∗
    token_pack γ__x ∗
    x ↦_{inv_x} [false] ∗
    y ↦_AT^{inv_y} [false] ∗
    persist_lb x inv_x false ∗
    persist_lb z inv_z false ∗
    z ↦_{inv_z} [false] -∗
    WPC prog x y z @ s; ⊤
    {{ v, ⌜ φ v ⌝ }}
    {{ <NG> crash_condition }}.
  Proof.
    iIntros "Hpre".
    iApply (wpc_mono'); last by iApply prog_spec.
    - done.
    - iIntros.
      done.
    - by iIntros.
  Qed.

  Lemma simple_rec_spec (s: stuckness):
    (<NG> crash_condition) -∗
    (<NG> (WPC recovery x z @ s; ⊤
    {{ v, ⌜ φ v ⌝ }}
    {{ <NG> crash_condition }})).
  Proof.
    iApply nextgen.nextgen_mono.
    iIntros "Hpre".
    iApply (wpc_mono'); last by iApply recovery_prog_spec.
    - done.
    - iIntros.
      done.
    - by iIntros.
  Qed.

  Lemma wpr_spec (s: stuckness):
    (token_pack γ__z ∗
     token_pack γ__x ∗
     x ↦_{inv_x} [false] ∗
     y ↦_AT^{inv_y} [false] ∗
     persist_lb x inv_x false ∗
     persist_lb z inv_z false ∗
     z ↦_{inv_z} [false]) ⊥ -∗
    validV ∅ -∗
    wpr s ⊤ (prog x y z `at` ⊥) (recovery x z `at` ⊥)
      (λ v, ⌜ φ v.(val_val) ⌝)%I
      True%I
      (λ v, ⌜ φ v.(val_val) ⌝)%I.
  Proof.
    iIntros "Hpre HvalidV".
    iPoseProof (idempotence_wpr with "[Hpre] [] HvalidV") as "Hwpr".
    - simpl.
      iApply (simple_prog_spec s with "Hpre").
    - iIntros "!>".
      rewrite monPred_at_wand.
      iIntros (TV ?) "cc".
      iModIntro.
      iApply (simple_rec_spec s with "cc").
    - simpl.
      iApply (wpr_strong_mono with "Hwpr").
      naive_solver.
  Qed.
End proof.

Section closed_proof.
  (* crude way to avoid typeclass confusion *)
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ, !tokenG Σ Ω}.
  Lemma closed_wpr_spec (s: stuckness) x y z:
    ⊢ |==> ∃ γ__x γ__y γ__z,
      (x ↦_{inv_x} [false] ∗
       persist_lb x inv_x false ∗
       y ↦_AT^{inv_y x γ__x γ__y} [false] ∗
       z ↦_{inv_z x γ__z} [false] ∗
       persist_lb z (inv_z x γ__z) false) ⊥ -∗
      validV ∅ -∗
      ((inv_x.(p_full) false #false ∗ inv_x.(p_pers) false #false) ∗
       ((inv_y x γ__x γ__y).(p_full) false #false ∗ (inv_y x γ__x γ__y).(p_pers) false #false) ∗
       ((inv_z x γ__z).(p_full) false #false ∗ (inv_z x γ__z).(p_pers) false #false)) ⊥ ∗
      wpr s ⊤ (prog x y z `at` ⊥) (recovery x z `at` ⊥)
        (λ v, ⌜ φ v.(val_val) ⌝)%I
        True%I
        (λ v, ⌜ φ v.(val_val) ⌝)%I.
  Proof.
    iMod (token_pack_alloc $! ⊥) as (γ__x) "x_pack".
    iMod (token_pack_alloc $! ⊥) as (γ__y) "y_pack".
    iMod (token_pack_alloc $! ⊥) as (γ__z) "z_pack".
    iModIntro.
    iExists γ__x, γ__y, γ__z.
    monPred_simpl.
    Opaque persist_lb mapsto_at.
    iIntros "(xPts & #xPer & #yPts & zPts & #zPer) #validV".
    iSplitR "x_pack z_pack xPts zPts".
    - rewrite /p_full /p_pers /=.
      iSplit; first naive_solver.
      iSplit; last naive_solver.
      iSplit; last naive_solver.
      iSplit; first naive_solver.
      iFrame.
    - iApply (wpr_spec with "[-]"); last done.
      monPred_simpl.
      iFrame "xPts zPts yPts xPer zPer z_pack x_pack".
  Qed.
End closed_proof.

Section adequacy.
  Context (x y z: loc) (s: stuckness).
  Context (Build_nvmHighGpreS: ∀ Σ Ω (nvmBase: nvmBaseGS Σ Ω), nvmHighGpreS Σ Ω).
  Definition σ__na: gmap loc val := {[ x := #false; z := #false ]}.
  Definition σ__at: gmap loc val := {[ y := #false ]}.
  Definition PV: view.view := {[ x := MaxNat 0; y := MaxNat 0; z := MaxNat 0 ]}.

  Opaque mapsto_at mapsto_na persist_lb token_pack.

  Theorem durable_mp_safe Σ Ω `{!nvmBaseGpreS Σ Ω, !Perennial_preG Σ Ω} `{!tokenG Σ Ω}:
    x ≠ y ∧ x ≠ z ∧ y ≠ z →
    recv_adequate s (prog x y z `at` ⊥) (recovery x z `at` ⊥) (initial_heap (σ__at ∪ σ__na), PV) (λ v _, φ v.(val_val)) (λ v _, φ v.(val_val)).
  Proof using Build_nvmHighGpreS.
    intros Hdistinct.
    apply (high_recv_adequacy_simple Build_nvmHighGpreS Σ Ω).
    { set_solver. }
    { set_solver. }
    intros ???.
    iMod (closed_wpr_spec s x y z) as (γ__x γ__y γ__z) "Hwpr".
    iModIntro.
    iExists {[ y := adequacy_alloc.MkLocInfo Σ Ω Hbase Hhigh _ _ _ _ (inv_y x γ__x γ__y) _ false ]}.
    iExists {[ x := adequacy_alloc.MkLocInfo Σ Ω Hbase Hhigh _ _ _ _ inv_x _ false; z := adequacy_alloc.MkLocInfo Σ Ω Hbase Hhigh _ _ _ _ (inv_z x γ__z) _ false ]}.
    iSplit; first (iPureIntro; set_solver).
    iSplit; first (iPureIntro; set_solver).
    iIntros "Hat Hna validV".
    rewrite /adequacy_alloc.init_at_assertions /adequacy_alloc.init_na_assertions.
    iEval (rewrite big_sepM2_singleton /=) in "Hat".
    iDestruct "Hat" as "[#pPer #yPts]".
    rewrite big_sepM2_insert ?lookup_insert_ne //; [ | naive_solver | naive_solver ].
    rewrite big_sepM2_singleton /=.
    iDestruct "Hna" as "[[#xPer xPts] [#zPer zPts]]".
    iDestruct ("Hwpr" with "[$xPts $xPer $yPts $zPts $zPer] validV") as "[(_ & [[_ y_pack] _] & _) Hwpr]".
    rewrite /adequacy_alloc.init_prots.
    rewrite big_sepM2_singleton /=.
    rewrite big_sepM2_insert ?lookup_insert_ne //; [ | naive_solver | naive_solver ].
    rewrite big_sepM2_singleton /=.
    iFrame.
    naive_solver.
  Qed.
End adequacy.

Print Assumptions durable_mp_safe.
