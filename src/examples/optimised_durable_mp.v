(* This is a variant of [durable_mp.v] where the flush and fence in the writing
   thread is moved to the reading thread.

   The writing thread ([leftProg] below) writes [x] and then publishes [y]
   *without* flushing/fencing [x]. The reading thread ([rightProg] below), upon
   observing [y = true], performs the flush and fence itself before recording an
   acknowledgement in [z].

   Because the flush/fence now happens in the reader, the message-passing
   protocol for [y] can only transfer a [store_lb] for [x] (not a persisted
   [flush_lb]); the [flush_lb] is established by the reader and handed on to [z].

 * This file is ported with help from claude code. *)
From iris_named_props Require Import named_props.
From iris.algebra Require Import excl.

From self.high.lib Require Import abstract_state abstract_state_instances.
From self.high Require Import protocol wpc_proofmode.
From self.high Require Import recovery_weakestpre adequacy.

Section program.
  Definition leftProg (x y : loc) : expr :=
    #x <-_NA #true ;;
    (* No flush or fence here. *)
    #y <-_AT #true.

  Definition rightProg (x y z : loc) : expr :=
    if: !_AT #y = #true
    then
      Flush #x ;;
      Fence ;;
      #z <-_NA #true
    else #().

  Definition prog (x y z : loc) : expr :=
    Fork (leftProg x y) ;; rightProg x y z.

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

  (* The bare points-to for [x] at value [true]. Unlike [durable_mp.v]'s
     [x_pack], this does *not* carry a [flush_lb]: the writing thread does not
     flush. *)
  Definition xm : dProp Σ :=
    ∃ σs, x ↦_{inv_x} (σs ++ [true]).

  #[global] Instance xm_buffer_free:
    BufferFree (xm).
  Proof.
    rewrite /IntoNoBuffer /xm.
    iIntros "[% xPts]".
    iModIntro.
    by iExists _.
  Qed.

  (* [x_pack] as in [durable_mp.v]: points-to together with a [flush_lb]. This is
     established by the *reader* (after it flushes and fences) and stored into
     [z]. *)
  Definition x_pack: dProp Σ :=
    xm ∗ flush_lb x inv_x true.

  #[global] Instance x_pack_buffer_free:
    BufferFree (x_pack).
  Proof.
    rewrite /IntoNoBuffer /x_pack /xm.
    iIntros "[[% xPts] #xFlush]".
    iModIntro.
    iSplit; last done.
    by iExists _.
  Qed.

  #[global] Instance x_pack_nextgen_flush:
    IntoNGFlush (x_pack) (x_pack).
  Proof.
    rewrite /IntoNGFlush /x_pack /xm.
    iIntros "[[% xPts] #xFlush]".
    iModIntro.
    iDestruct "xFlush" as "[xPers (% & % & xCrashed)]".
    assert (σ__pc = true) as -> by done.
    iDestruct (crashed_in_if_rec inv_x with "[$] [$]") as (???) "[xCrashed' xPts]".
    iDestruct (crashed_in_agree with "[$] [$]") as "->".
    rewrite /p_bumper list_fmap_id /=.
    iSplit; last by iApply persist_lb_to_flush_lb.
    iExists _. iApply "xPts".
  Qed.

  Opaque xm x_pack token_pack.

  (* [y] is an [option bool] location so that it can [bumper] to [None] after a
     crash: it transfers only a [store_lb] (flush-free) and a bare points-to
     [xm] (behind a token), neither of which survives a crash on their own. *)
  Definition inv_y : LocationProtocol (option bool) :=
    {| p_full (s : option bool) (v : val) :=
        match s with
        | None => True
        | Some false => ⌜ v = #false ⌝ ∗ token_pack γ__y
        | Some true => ⌜ v = #true ⌝ ∗ store_lb x inv_x true ∗ (xm ∨ token_pack γ__x)
        end%I;
       p_read (s : option bool) (v : val) :=
        match s with
        | None => True
        | Some false => ⌜ v = #false ⌝ ∗ token_pack γ__y
        | Some true => ⌜ v = #true ⌝ ∗ store_lb x inv_x true ∗ (xm ∨ token_pack γ__x)
        end%I;
       p_pers (s : option bool) (v : val) := True%I;
       p_bumper _ := None; |}.

  #[global] Instance inv_y_cond ℓ : ProtocolConditions ℓ inv_y.
  Proof.
    split.
    - intros ?? _. done.
    - intros [[|]|] v; apply _.
    - intros [[|]|] v; apply _.
    - intros [[|]|] v; apply _.
    - intros s v. rewrite /p_full /p_read /=.
      iSplit.
      + iIntros "$". iIntros "$".
      + iIntros "[$ _]".
    - iIntros "_" (σ_p v_p σ_f v_f) "%le Hpers Hfull".
      iSplit.
      + iModIntro. iModIntro. iIntros "_". by iSplit.
      + iIntros (σ_c v_c) "!> _ % %". iModIntro. iModIntro. iIntros "_". by iSplit.
    - iIntros (s v) "_". by iModIntro.
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

  Ltac solve_left_cc :=
    iSplit;
    first
      iApply (crash_condition_impl with "xPer tok zPer zPts").

  Lemma left_prog_spec s E1 :
    x ↦_{inv_x} [false] -∗
    y ↦_AT^{inv_y} [Some false] -∗
    (WPC leftProg x y @ s; E1
    {{ _, True }}
    {{ True }}).
  Proof.
    iIntros "xPts #yPts".
    rewrite /leftProg.
    wpc_bind (_ <-_NA _)%E.
    iApply wpc_atomic_no_mask. iSplit; first done.
    iApply (wp_store_na x _ _ _ _ true with "[$xPts]").
    { reflexivity. } { done. }
    { rewrite /inv_x. done. }
    iNext. iIntros "xPts".
    iSplit; first done.
    iModIntro.
    wpc_pures; first done.

    iDestruct (mapsto_na_store_lb with "xPts") as "#xStore".

    wpc_bind (_ <-_AT _)%E.
    iApply wpc_atomic_no_mask. iSplit; first done.
    iApply (wp_store_at _ inv_y [] (Some false) (Some true) with "[$yPts xPts]").
    { rewrite /p_full /=.
      iSplitL.
      { iSplitPure; first done.
        iFrame "xStore".
        iLeft.
        Transparent xm.
        iExists [false]. iApply "xPts".
        Opaque xm. }
      iSplitPure; first done.
      iIntros (v_i s_c v_c) "%le". simpl.
      destruct s_c as [[|]|]; [ | | done ].
      - iIntros "_". naive_solver.
      - iIntros "([_ O1] & _ & [_ O2])".
        iDestruct (token_pack_excl with "O1 O2") as %[]. }
    iIntros "!> yLb2".
    iSplit; done.
  Qed.

  Lemma prog_spec s:
    token_pack γ__z ∗
    token_pack γ__x ∗
    x ↦_{inv_x} [false] ∗
    y ↦_AT^{inv_y} [Some false] ∗
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
    - (* Show safety of the forked off (writing) thread. *)
      iDestruct (left_prog_spec with "xPts yPts") as "$".
    - solve_left_cc. iNext.
      wpc_pures; first iApply (crash_condition_impl with "xPer tok zPer zPts").
      rewrite /rightProg.
      wpc_bind (!_AT _)%E.
      iApply wpc_atomic_no_mask.
      solve_left_cc.
      iApply (wp_load_at_simple _ _
                (λ (s: option bool) v,
                   match s with
                   | Some true => (⌜ v = #true ⌝ ∗ store_lb x inv_x true ∗ xm)%I
                   | Some false => ⌜ v = #false ⌝%I
                   | None => False%I
                   end)
                inv_y with "[$yPts tok__x]").
      { iModIntro.
        iIntros (sL vL) "%le Hr".
        destruct sL as [[|]|]; simpl in le |- *.
        - iDestruct "Hr" as "(-> & #store & [xm | tokx])".
          + iSplitL "xm".
            * iSplitR; first done. iFrame "store xm".
            * iSplitR; first done. iFrame "store". iRight. iFrame "tok__x".
          + iDestruct (token_pack_excl with "tokx tok__x") as %[].
        - iDestruct "Hr" as "(-> & toky)".
          iSplitR "toky"; first done.
          iSplitR; first done. iFrame "toky".
        - destruct le. }
      iNext.
      iIntros (sL vL) "[yPts2 Q]".
      destruct sL as [[|]|].
      2: {
        (* We loaded [false] and this case is trivial. *)
        iDestruct "Q" as ">->".
        solve_left_cc.
        iModIntro.
        wpc_pures.
        { iApply (crash_condition_impl with "xPer tok zPer zPts"). }
        iModIntro.
        iRight. iFrame "zPts". }
      2: {
        (* Impossible: [None] is not reachable. *)
        iDestruct "Q" as ">[]". }
      (* We loaded [true]. *)
      iDestruct "Q" as "(>-> & >#store & xmF)".
      solve_left_cc.
      iModIntro.
      wpc_pures.
      { iApply (crash_condition_impl with "xPer tok zPer zPts"). }

      (* Flush *)
      wpc_bind (Flush _)%E.
      iApply wpc_atomic_no_mask. solve_left_cc.
      iApply (wp_flush_lb with "store").
      iNext.
      iIntros "(#xFlushF & _)".
      solve_left_cc.
      iModIntro.
      wpc_pures; first iApply (crash_condition_impl with "xPer tok zPer zPts").

      (* The fence: discharges both the pending [xm] and the pending [flush_lb]. *)
      wpc_bind (Fence)%E.
      iApply wpc_atomic_no_mask. solve_left_cc.
      iApply wp_fence. do 2 iModIntro.
      solve_left_cc.
      iModIntro.
      wpc_pures.
      { iApply (crash_condition_impl with "xPer tok zPer zPts"). }

      iApply wpc_atomic_no_mask. solve_left_cc.
      iApply (wp_store_na _ inv_z _ _ _ true with "[$zPts xmF xFlushF]"); eauto.
      { iSplitR; first done.
        iFrame "xFlushF".
        iLeft.
        Transparent x_pack.
        iFrame "xmF xFlushF".
        Opaque x_pack. }

      iIntros "!> zPts /=".
      solve_left_cc.
      iModIntro.
      iLeft. iFrame "zPts".
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
      iSplit.
      { iApply (crash_condition_impl with "xPer tok zPer zPts"). }
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
      + Transparent x_pack.
        iDestruct ("H") as "[xm xFlush]".
        Transparent xm.
        iDestruct "xm" as "[% xPts]".
        Opaque xm x_pack.
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
        { iApply (crash_condition_impl with "xPer tok zPer zPts"). }
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
    y ↦_AT^{inv_y} [Some false] ∗
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
     y ↦_AT^{inv_y} [Some false] ∗
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
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ, !tokenG Σ Ω}.
  Lemma closed_wpr_spec (s: stuckness) x y z:
    ⊢ |==> ∃ γ__x γ__y γ__z,
      (x ↦_{inv_x} [false] ∗
       persist_lb x inv_x false ∗
       y ↦_AT^{inv_y x γ__x γ__y} [Some false] ∗
       z ↦_{inv_z x γ__z} [false] ∗
       persist_lb z (inv_z x γ__z) false) ⊥ -∗
      validV ∅ -∗
      ((inv_x.(p_full) false #false ∗ inv_x.(p_pers) false #false) ∗
       ((inv_y x γ__x γ__y).(p_full) (Some false) #false ∗ (inv_y x γ__x γ__y).(p_pers) (Some false) #false) ∗
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
      iFrame "y_pack".
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

  Theorem optimised_durable_mp_safe Σ Ω `{!nvmBaseGpreS Σ Ω, !Perennial_preG Σ Ω} `{!tokenG Σ Ω}:
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
    iExists {[ y := adequacy_alloc.MkLocInfo Σ Ω Hbase Hhigh _ _ _ _ (inv_y x γ__x γ__y) _ (Some false) ]}.
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

Print Assumptions optimised_durable_mp_safe.
