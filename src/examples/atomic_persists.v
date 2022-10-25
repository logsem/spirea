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
      flush_lb x prot_bool b ∗
      flush_lb y prot_bool b ∗
      x ↦_{prot_bool} (ss ++ [b]) ∗
      y ↦_{prot_bool} (ss ++ [b]).

  Definition lock_condition : dProp Σ :=
    (* [x] and [y] *)
    (∃ (xss yss : list bool) (bx byy : bool),
      "#xPer" ∷ flush_lb x prot_bool bx ∗
      "#yPer" ∷ flush_lb y prot_bool byy ∗
      "xPts" ∷ x ↦_{prot_bool} (xss ++ [bx]) ∗
      "yPts" ∷ y ↦_{prot_bool} (yss ++ [byy])).

  Definition crash_condition : dProp Σ :=
    (∃ (zss : list bool) (bz : bool),
      "#zPer" ∷ persist_lb z prot_z bz ∗
      "zPts" ∷ z ↦_{prot_z} (zss ++ [bz])).

  Lemma crash_condition_impl :
    persist_lb z prot_z false -∗
    z ↦_{prot_z} [false] -∗
    <PC> crash_condition.
  Proof.
    iIntros "zPerLb zPts".
    iCrashIntro.
    iDestruct "zPerLb" as "[zPerLb (% & ? & crashedIn)]".
    iDestruct (crashed_in_if_rec with "crashedIn zPts")
      as (??) "(? & crashedIn2 & zPts)".
    simpl.
    iExists _, _.
    iFrame "zPts".
    iApply (crashed_in_persist_lb with "crashedIn2").
  Qed.

  Ltac solve_cc :=
    try iModIntro (|={_}=> _)%I;
    iDestruct (crash_condition_impl with "zPerLb zPts") as "$".

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

    iApply (
      newlock_crash_spec (nroot .@ "lock") _ lock_res (<PC> lock_condition)%I (
        (λ lk, let: "lock" := lk in
          Fork _;; _)%E)
                        (λ _, True)%I
                        (<PC> crash_condition)
      with "[xPts yPts] [] [-]").
    { iExists [], _. simpl.
      rewrite -2!persist_lb_to_flush_lb.
      iFrame "xPerLb yPerLb xPts yPts". }
    { iModIntro.
      rewrite /lock_res /lock_condition.
      iIntros "(% & % & xPts & yPts)".
      iCrashIntro. admit. }
    iSplit; first solve_cc.
    iIntros (lk γ) "#isLock".
    wpc_pures; first solve_cc.

    wpc_bind (Fork _)%E.
    iApply (wpc_fork with "[]").
    - (* Show safety of the forked off thread. *)
      iNext.
      wpc_apply (with_lock_spec with "[$isLock]"); first done.
      iSplit; first done.
      (* iIntros "[borrow locked]". *)
      (* wp_pures. *)
      (* rewrite wp_wpc. *)
      (* wpc_apply (use_crash_locked with "burrow"). *)
      (* { done. } *)
      (* iApply (wpc_crash_borrow_open with "borrow"). *)
      (* { done. } *)
      (* iSplit; first done. *)
      iIntros "(% & % & ? & ? & xPts & yPts)".
      (* write to [x] *)
      wpc_bind (_ <-_NA _)%E.
      iApply wpc_atomic_no_mask.
      iSplit.
      { admit. }
      iApply (wp_store_na _ prot_bool _ _ b true with "[$xPts]"); eauto.
      { rewrite last_snoc. done. }
      { destruct b; done. }
      iNext. iIntros "xPts".
      iSplit.
      { admit. }
      iModIntro.
      wpc_pures.
      { admit. }

      (* write to [y] *)
      wpc_bind (_ <-_NA _)%E.
      iApply wpc_atomic_no_mask.
      iSplit.
      { admit. }
      iApply (wp_store_na _ prot_bool _ _ b true with "[$yPts]"); eauto.
      { rewrite last_snoc. done. }
      { destruct b; done. }
      iNext. iIntros "yPts".
      iSplit. { admit. }
      iModIntro.

      (* flushes *)
      wpc_pures.
      { admit. }

      wpc_bind (Flush _)%E.
      iApply wpc_atomic_no_mask.
      iSplit. { admit. }
      iApply (wp_flush_na with "xPts").
      iNext.
      iIntros "(xPts & #xLowerBound & ?)".
      iSplit. { admit. }
      iModIntro.

      wpc_pures.
      { admit. }

      wpc_bind (Flush _)%E.
      iApply wpc_atomic_no_mask.
      iSplit. { admit. }
      iApply (wp_flush_na with "yPts").
      iNext.
      iIntros "(yPts & #yLowerBound & ?)".
      iSplit. { admit. }
      iModIntro.

      wpc_pures.
      { admit. }

      iApply wpc_atomic_no_mask.
      iSplit. { admit. }
      wp_apply wp_fence.
      iModIntro. iModIntro.
      iSplit.
      { admit. }
      { admit. }
    -
      iSplit; first solve_cc.
      iNext.
      wpc_pure1 _; first solve_cc.
      wpc_pure1 _; first solve_cc.
      wpc_apply (with_lock_spec with "[$isLock zPts]"); first done.
      iSplit; first solve_cc.
      iIntros "(% & % & #xLb & #yLb & xPts & yPts)".

      wpc_bind (!_NA _)%E.
      iApply wpc_atomic_no_mask.
      iSplit.
      { solve_cc. admit. }
      iApply (wp_load_na with "[$yPts]").
      { apply last_snoc. }
      { iModIntro.
        iIntros (?). iIntros "#H". iFrame "H". rewrite right_id. iApply "H". }
      iNext. iIntros (?) "[yPts ->]".
      iSplit. { solve_cc. admit. }
      iModIntro.
      destruct b.
      * wpc_pures. { solve_cc. admit. }
        iApply wpc_atomic_no_mask.
        iSplit. { solve_cc. admit. }
        iApply (wp_store_na _ prot_z _ _ _ true with "[$zPts]"); eauto.
        { simpl. iSplitPure; first done.
          iFrame "xLb". done. }
        iNext. iIntros "zPts".
        iSplit.
        { admit. }
        { admit. }
      * wpc_pures.
        { solve_cc. admit. }
        iModIntro.
        solve_cc.
        admit.
  Abort.

  Lemma recovery_prog_spec s E :
    crash_condition -∗
    WPC recovery x y z @ s; E
      {{ _, True }}
      {{ <PC> crash_condition }}.
  Proof.
  Abort.

End spec.
