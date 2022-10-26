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
     abstract_state_instances locations protocol if_rec.
From self.high.modalities Require Import fence no_buffer.

From self.examples Require Import spin_lock crash_lock.

Section program.

  Definition leftProg (x y : loc) lock : expr :=
    with_lock lock (
      #x <-_NA #true ;;
      #y <-_NA #true ;;
      Flush #x ;;
      Flush #y ;;
      Fence
    ).

  Definition rightProg (x y z : loc) lock : expr :=
    with_lock lock (
      if: !_NA #x = #true
      then
        #z <-_NA #true
      else #()
    ).

  Definition prog (x y z : loc) : expr :=
    let: "lock" := mk_lock #() in
    Fork (leftProg x y "lock") ;; rightProg y x z "lock".

  Definition recovery (x y z : loc) : expr :=
    if: !_NA #z = #true
    then
      assert: !_NA #x = #true ;;
      assert: !_NA #y = #true
    else #().

End program.

Section spec.
  Context `{nvmG Σ, lockG Σ}.
  Context `{!stagedG Σ}.

  Context (x y z : loc).

  Program Definition prot_bool : LocationProtocol bool :=
    {| p_inv (b : bool) v := ⌜ v = #b ⌝%I;
       p_bumper b := b; |}.

  Global Instance prot_bool_conditions : ProtocolConditions prot_bool.
  Proof. split; try apply _. iIntros. by iApply post_crash_flush_pure. Qed.

  Definition prot_z :=
    {| p_inv (b : bool) (v : val) :=
        if b
        then
          ⌜ v = #true ⌝ ∗ flush_lb x prot_bool true ∗ flush_lb y prot_bool true
        else ⌜ v = #false ⌝;
      p_bumper := id; |}%I.

  Global Instance prot_z_conditions : ProtocolConditions prot_z.
  Proof.
    split; try apply _.
    iIntros ([|] ?) "H !>"; simpl; last done.
    rewrite -2!persist_lb_to_flush_lb.
    iDestruct "H" as "($ & [$ _] & [$ _])".
  Qed.

  Definition lock_res : dProp Σ :=
    ∃ ss b,
      "#pLbX" ∷ persist_lb x prot_bool false ∗
      "#pLbY" ∷ persist_lb y prot_bool false ∗
      "#fLbX" ∷ flush_lb x prot_bool b ∗
      "#fLbY" ∷ flush_lb y prot_bool b ∗
      "xPts" ∷ x ↦_{prot_bool} (ss ++ [b]) ∗
      "yPts" ∷ y ↦_{prot_bool} (ss ++ [b]).

  Definition lock_condition : dProp Σ :=
    (* [x] and [y] *)
    (∃ (xss yss : list bool) (bx byy : bool) bx' by',
      "#pLbX" ∷ persist_lb x prot_bool bx' ∗
      "#pLbY" ∷ persist_lb y prot_bool by' ∗
      "xPts" ∷ x ↦_{prot_bool} (xss ++ [bx]) ∗
      "yPts" ∷ y ↦_{prot_bool} (yss ++ [byy])).

  Lemma lock_condition_impl bx' by' bx byy xss yss :
    persist_lb x prot_bool bx' -∗
    persist_lb y prot_bool by' -∗
    x ↦_{prot_bool} (xss ++ [bx]) -∗
    y ↦_{prot_bool} (yss ++ [byy]) -∗
    <PC> lock_condition.
  Proof.
    iIntros "flX flY xPts yPts".
    iCrashIntro.
    iDestruct "flX" as "[pLbX (% & ? & xCrashed)]".
    iDestruct "flY" as "[pLbY (% & ? & yCrashed)]".
    iDestruct (crashed_in_if_rec with "xCrashed xPts")
      as (??) "(? & crashedIn2 & xPts)".
    iDestruct (crashed_in_if_rec with "yCrashed yPts")
      as (??) "(? & crashedInY & yPts)".
    repeat iExists _.
    iFrameF "pLbX".
    iFrameF "pLbY".
    iFrame "xPts".
    iFrame "yPts".
  Qed.

  Ltac solve_lc :=
    try iModIntro (|={_}=> _)%I;
    iDestruct (lock_condition_impl with "pLbX pLbY xPts yPts") as "$".

  Definition crash_condition : dProp Σ :=
    (∃ (zss : list bool) (bz : bool) bz',
      "#zPerLb" ∷ persist_lb z prot_z bz' ∗
      "zPts" ∷ z ↦_{prot_z} (zss ++ [bz])).

  Lemma crash_condition_impl_alt zss bz b :
    persist_lb z prot_z b -∗
    z ↦_{prot_z} (zss ++ [bz]) -∗
    <PC> crash_condition.
  Proof.
    iIntros "zPerLb zPts".
    iCrashIntro.
    iDestruct "zPerLb" as "[zPerLb (% & ? & crashedIn)]".
    iDestruct (crashed_in_if_rec with "crashedIn zPts")
      as (??) "(? & crashedIn2 & zPts)".
    simpl.
    iExists _, _, _.
    iFrame "zPts".
    iApply (crashed_in_persist_lb with "crashedIn2").
  Qed.

  Lemma crash_condition_impl bz b :
    persist_lb z prot_z b -∗
    z ↦_{prot_z} [bz] -∗
    <PC> crash_condition.
  Proof. iApply (crash_condition_impl_alt [] bz b). Qed.

  Ltac solve_cc :=
    try iModIntro (|={_}=> _)%I;
    iDestruct (crash_condition_impl with "zPerLb zPts") as "$".

  Ltac solve_cc_alt :=
    try iModIntro (|={_}=> _)%I;
    iDestruct (crash_condition_impl_alt with "zPerLb zPts") as "$".

  Global Instance buffer_free_view_objective (P : dProp Σ) :
    ViewObjective P → BufferFree P.
  Proof.
    intros ?.
    rewrite /IntoNoBuffer.
    iModel.
    rewrite no_buffer_at.
    iApply view_objective_at.
  Qed.

  Lemma prog_spec :
    pre_borrow_d -∗
    persist_lb x prot_bool false -∗
    persist_lb y prot_bool false -∗
    persist_lb z prot_z false -∗
    x ↦_{prot_bool} [false] -∗
    y ↦_{prot_bool} [false] -∗
    z ↦_{prot_z} [false] -∗
    WPC prog x y z @ ⊤
      {{ v, True }}
      {{ (<PC> crash_condition) ∗ <PC> lock_condition }}.
  Proof.
    iIntros "pb #xPerLb #yPerLb #zPerLb xPts yPts zPts".
    rewrite /prog.

    eassert (
      (let: "lock" := mk_lock #() in
      Fork (leftProg x y "lock");; rightProg y x z "lock")%E
        =
          fill _ (mk_lock #())
          ) as ->.
    {
      reshape_expr (
        (let: "lock" := mk_lock #() in
        Fork (leftProg x y "lock");; rightProg y x z "lock")%E)
          ltac:(fun K e' => apply (@eq_refl _ (fill K e'))).
    }
    iApply (
      newlock_crash_spec (nroot .@ "lock") _ lock_res (<PC> lock_condition)%I
        _
                        (λ _, True)%I
                        (<PC> crash_condition)
      with "[xPts yPts] [] [-]").
    { iExists [], _. simpl.
      rewrite -2!persist_lb_to_flush_lb.
      iFrame "xPerLb yPerLb xPts yPts". }
    { iModIntro.
      iNamed 1.
      iApply (lock_condition_impl with "pLbX pLbY xPts yPts"). }
    iSplit; first solve_cc.
    iIntros (lk γ) "#isLock".
    wpc_pures; first solve_cc.

    wpc_bind (Fork _)%E.
    iApply (wpc_fork with "[]").
    - (* Show safety of the forked off thread. I.e., the _left_ thread. *)
      iNext.
      wpc_apply (with_lock_spec with "[$isLock]"); first done.
      iSplit; first done.
      setoid_rewrite (left_id (True%I) _ _).
      iNamed 1.
      (* write to [x] *)
      wpc_bind (_ <-_NA _)%E.
      iApply wpc_atomic_no_mask.
      iSplit.
      { solve_lc. }
      iApply (wp_store_na _ prot_bool _ _ b true with "[$xPts]"); eauto.
      { rewrite last_snoc. done. }
      { destruct b; done. }
      iNext. iIntros "xPts".
      iSplit.
      { solve_lc. }
      iModIntro.
      wpc_pures. { solve_lc. }

      (* write to [y] *)
      wpc_bind (_ <-_NA _)%E.
      iApply wpc_atomic_no_mask.
      iSplit. { solve_lc. }
      iApply (wp_store_na _ prot_bool _ _ b true with "[$yPts]"); eauto.
      { rewrite last_snoc. done. }
      { destruct b; done. }
      iNext. iIntros "yPts".
      iSplit. { solve_lc. }
      iModIntro.

      (* flushes *)
      wpc_pures. { solve_lc. }

      wpc_bind (Flush _)%E.
      iApply wpc_atomic_no_mask.
      iSplit. { solve_lc. }
      iApply (wp_flush_na with "xPts").
      iNext.
      iIntros "(xPts & #xLowerBound & ?)".
      iSplit. { solve_lc. }
      iModIntro.

      wpc_pures.
      { solve_lc. }

      wpc_bind (Flush _)%E.
      iApply wpc_atomic_no_mask.
      iSplit. { solve_lc. }
      iApply (wp_flush_na with "yPts").
      iNext.
      iIntros "(yPts & #yLowerBound & ?)".
      iSplit. { solve_lc. }
      iModIntro.

      wpc_pures.
      { solve_lc. }

      iApply wpc_atomic_no_mask. iSplit. { solve_lc.  }
      wp_apply wp_fence.
      iModIntro. iModIntro.
      iSplit.
      { solve_lc. }
      iModIntro. rewrite left_id.
      iExists _, true.
      iFrameF "pLbX". iFrameF "pLbY". iFrameF "xLowerBound".
      iFrameF "yLowerBound". iFrameF "xPts". iFrame "yPts".
    - (* verify the _right_ thread. *)
      iSplit; first solve_cc.
      iNext.
      wpc_pure1 _; first solve_cc.
      wpc_pure1 _; first solve_cc.
      wpc_apply (with_lock_spec with "[$isLock zPts]"); first done.
      iSplit; first solve_cc.
      iNamed 1.

      wpc_bind (!_NA _)%E.
      iApply wpc_atomic_no_mask.
      iSplit.
      { solve_lc. solve_cc. }
      iApply (wp_load_na with "[$yPts]").
      { apply last_snoc. }
      { iModIntro.
        iIntros (?). iIntros "#H". iFrame "H". rewrite right_id. iApply "H". }
      iNext. iIntros (?) "[yPts ->]".
      iSplit. { solve_lc. solve_cc. }
      iModIntro.
      destruct b.
      * wpc_pures. { solve_lc. solve_cc. }
        iApply wpc_atomic_no_mask.
        iSplit. { solve_lc. solve_cc. }
        iApply (wp_store_na _ prot_z _ _ _ true with "[$zPts]"); eauto.
        { simpl. iSplitPure; first done.
          iFrame "fLbX". done. }
        iNext. iIntros "zPts".
        iSplit.
        { solve_lc. solve_cc_alt. }
        iModIntro.
        solve_cc_alt.
        iExists _, true.
        iFrameF "xPerLb". iFrameF "yPerLb". iFrameF "fLbX". iFrameF "fLbY".
        iFrameF "xPts". iFrame "yPts".
      * wpc_pures.
        { solve_lc. solve_cc. }
        iModIntro.
        rewrite right_id.
        solve_cc.
        iExists _, false.
        iFrameF "xPerLb". iFrameF "yPerLb". iFrameF "fLbX". iFrameF "fLbY".
        iFrameF "xPts". iFrame "yPts".
  Qed.

  Instance if_else_persistent {PROP : bi} (b : bool) (P Q : PROP) :
    Persistent P →
    Persistent Q →
    Persistent (if b then P else Q).
  Proof. intros ??. destruct b; done. Qed.

  Lemma recovery_prog_spec s E :
    crash_condition ∗ lock_condition -∗
    WPC recovery x y z @ s; E
      {{ _, True }}
      {{ (<PC> crash_condition) ∗ <PC> lock_condition }}.
  Proof.
    iIntros "[A B]".
    iNamed "A".
    iNamed "B".
    rewrite /recovery.

    (* load [z] *)
    wpc_bind (!_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit. { solve_cc_alt. solve_lc. }

    iApply (wp_load_na with "[$zPts]").
    { apply last_snoc. }
    { iIntros "!>" (?) "#H". iFrame "H". rewrite right_id. iApply "H". }
    iNext. iIntros (?) "[zPts #H]".
    iSplit. { solve_cc_alt. solve_lc. }
    iModIntro.
    simpl.
    destruct bz.
    - iDestruct "H" as (->) "[flushX flushY]".
      rewrite /assert.
      wpc_pures. { solve_cc_alt. solve_lc. }

      iDestruct (mapsto_na_store_lb_incl with "[] xPts") as %incl.
      { iApply flush_lb_to_store_lb. iApply "flushX". }
      inversion incl.
      iDestruct (mapsto_na_store_lb_incl with "[] yPts") as %inclY.
      { iApply flush_lb_to_store_lb. iApply "flushY". }
      inversion inclY.

      wpc_bind (!_NA _)%E.
      iApply wpc_atomic_no_mask.
      iSplit. { solve_lc. solve_cc_alt. }
      iApply (wp_load_na with "[$xPts]").
      { apply last_snoc. }
      { iModIntro.
        iIntros (?). iIntros "#H". iFrame "H". rewrite right_id. iApply "H". }
      iNext. iIntros (?) "[xPts ->]".
      iSplit. { solve_lc. solve_cc_alt. }
      iModIntro.
      wpc_pures. { solve_cc_alt. solve_lc. }

      wpc_bind (!_NA _)%E.
      iApply wpc_atomic_no_mask.
      iSplit. { solve_lc. solve_cc_alt. }
      iApply (wp_load_na with "[$yPts]").
      { apply last_snoc. }
      { iModIntro.
        iIntros (?). iIntros "#H". iFrame "H". rewrite right_id. iApply "H". }
      iNext. iIntros (?) "[yPts ->]".
      iSplit. { solve_lc. solve_cc_alt. }
      iModIntro.
      wpc_pures. { solve_cc_alt. solve_lc. }
      iModIntro. done.
    - iDestruct "H" as %->.
      wpc_pures. { solve_cc_alt. solve_lc. }
      iModIntro. done.
  Qed.

End spec.
