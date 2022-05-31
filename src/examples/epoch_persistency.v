From stdpp Require Import numbers countable.

From iris.algebra Require Import excl agree csum gset.
From iris.proofmode Require Import tactics.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances crash_borrow.
From self.high Require Import proofmode wpc_proofmode.
From self.high Require Import dprop resources crash_weakestpre weakestpre
     weakestpre_na weakestpre_at recovery_weakestpre lifted_modalities modalities crash_borrow
     post_crash_modality protocol no_buffer abstract_state_instances locations protocol if_rec.
From self.high.modalities Require Import fence.

Section program.

  Definition left_prog (x : loc) : expr :=
    #x <-_AT #2.

  Definition right_prog (x y z : loc) : expr :=
    #x <-_AT #1 ;;
    let: "a" := !_AT #x in
    Flush #x ;;
    (if: "a" = #2
    then #y <-_NA #1
    else #()) ;;
    Fence ;;
    #z <-_NA #1.

  Definition prog (x y z : loc) : expr :=
    Fork (left_prog x) ;; right_prog x y z.

  Definition recovery x y z : expr :=
    if: (!_NA #y = #true) && (!_NA #z = #true)
    then assert: !_AT x = #2
    else #().

End program.

(* Definition x_state := option (bool + bool). *)
Inductive x_state := x_zero | x_one | x_two.

Instance x_state_eqdecision : EqDecision x_state.
Proof. Admitted.

Instance x_state_countable : Countable x_state.
Proof. Admitted.

Definition x_state_order (x1 x2 : x_state) : Prop :=
  match x1, x2 with
    x_zero, _ => True
  | _, x_zero => False
  | _, _ => True
  end.

Program Instance x_state_abstract_state :
  AbstractState x_state := { abs_state_relation := x_state_order }.
Next Obligation.
  split; repeat intros [| |]; done.
Qed.

Definition x_state_to_nat (x : x_state) : nat :=
  match x with
    x_zero => 0
  | x_one => 1
  | x_two => 2
  end.

(* One shot resource algebra that we use in this example. *)
Definition one_shotR := csumR (exclR unitO) (agreeR (leibnizO x_state)).
Definition Pending : one_shotR := Cinl (Excl ()).
Definition Shot (n : x_state) : one_shotR := Cinr (to_agree n).

Class one_shotG Σ := { one_shot_inG :> inG Σ one_shotR }.
Definition one_shotΣ : gFunctors := #[GFunctor one_shotR].
Global Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{nvmG Σ, nvmDeltaG, one_shotG Σ, inG Σ (gset_disjR nat) }.

  Context (x y z : loc) (γag : gname) (γtok : gname).

  Definition tok0 : dProp Σ := ⎡ own γtok (GSet {[ 0 ]}) ⎤.
  Definition tok1 : dProp Σ := ⎡ own γtok (GSet {[ 1 ]}) ⎤.
  Definition tok2 : dProp Σ := ⎡ own γtok (GSet {[ 2 ]}) ⎤.

  (* Protocol for [x]. *)

  Program Definition prot_x := {|
    pred s v _ := (
      ⌜ v = #(x_state_to_nat s) ⌝ ∗
      match s with
        x_zero => tok0
      | x_one => tok1
      | x_two => tok2
      end)%I
    ;
    bumper b := b;
  |}.
  Next Obligation.
    iIntros (? [| |] ?) "H"; simpl; iCrashFlush; done.
  Qed.
  Next Obligation. Admitted.

  (* Protocol for [y]. *)

  Program Definition prot_y :=
    {| pred (b : bool) (v : val) _ :=
        match b with
          false => ⌜ v = #0 ⌝
        | true =>
            ⌜ v = #1 ⌝ ∗
            ⎡ own γag (Shot x_two) ⎤
            (* (flush_lb x prot_x x_two -∗ x ↦_AT^{prot_x} [x_zero; x_one; x_two]) *)
        end%I;
      bumper b := b; |}.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

  (* Protocol for [z]. *)

  Program Definition prot_z :=
    {| pred (b : bool) (v : val) _ :=
        match b with
          false => ⌜ v = #0 ⌝
        | true =>
            ⌜ v = #1 ⌝ ∗
            ∃ n, ⎡ own γag (Shot n) ⎤ ∗
                 flush_lb x prot_x n ∗
                 ((⌜ n = x_one ⌝ ∗ x ↦_AT^{prot_x} [x_zero; x_one]) ∨
                  (⌜ n = x_two ⌝ ∗ x ↦_AT^{prot_x} [x_zero; x_one; x_two]))
        end%I;
      bumper b := b; |}.
  Next Obligation.
    iIntros (? [|] v); last first.
    { iIntros "H". iCrashFlush. done. }
    iIntros "(-> & (%s & shot & fLb & [[-> B]|[-> B]]))".
    - iDestruct (useful x prot_x _ x_one with "[fLb]") as "bbB".
      {
        iFrame "fLb".
      iCrashFlush.
      iSplitPure; first done.
      iDestruct "fLb" as "[pLb (%sC & %le & #xCr)]".
      iDestruct (crashed_in_if_rec with "xCr B") as (?) "(xCr' & disj)".
      iDestruct (crashed_in_agree with "xCr xCr'") as %<-.
      iDestruct "disj" as "[H|H]"; last first.
      { iDestruct "H" as (? ([= <-] & le2 & neq)) "H".
        destruct sC; done. }
      iDestruct "H" as (? ? ? ?) "H".
      iExists x_one.
      iFrame "shot".
      rewrite -persist_lb_to_flush_lb.
      iFrame "pLb".
      iLeft.
      iSplitPure; first done.
      admit.
    - admit.
  Admitted.
  Next Obligation. Admitted.

  Definition crash_condition {hD : nvmDeltaG} : dProp Σ :=
    ∃ xss yss zss,
      (* x *)
      persist_lb x prot_x x_zero ∗
      x ↦_AT^{prot_x} xss ∗
      (* y *)
      persist_lb y prot_y false ∗
      y ↦_{prot_y} yss ∗
      (* z *)
      persist_lb z prot_z false ∗
      z ↦_{prot_z} zss.

  (* Definition left_crash_condition {hD : nvmDeltaG} : dProp Σ := *)
  (*   ∃ xss xs, *)
  (*     x ↦_AT^{prot_x} (xss ++ [xs]) ∗ *)
  (*     persist_lb x prot_x xs. *)

  Lemma left_prog_spec :
    tok2 -∗
    persist_lb x prot_x x_zero -∗
    x ↦_AT^{prot_x} [x_zero] -∗
    WPC left_prog x @ ⊤
      {{ v, x ↦_AT^{prot_x} [x_zero; x_two] }}
      {{ <PC> _, True }}.
  Proof.
    iIntros "tok #perLb xPts".
    rewrite /left_prog.
    iApply wpc_atomic_no_mask.
    iSplit. { iCrash. done. }
    iApply (wp_store_at _ [] _ x_two with "[$xPts $tok]").
    { iSplitPure; first done.
      iSplitPure; first done.
      (* iDestruct (persist_lb_to_store_lb _ _ x_two with "perLb") as "$". *)
      iIntros (v_i s_l v_l le).
      (* [s_l] can either be [x_zero] or [one_r]. *)
      destruct s_l; simpl.
      - iIntros "((-> & tok1) & (? & tok2) & (-> & tok3))".
        iDestruct (own_valid_2 with "tok1 tok3") as %hi%gset_disj_valid_op.
        set_solver.
      - iIntros "?". done.
      - iIntros "((-> & tok1) & (? & tok2) & (-> & tok3))".
        done. }
    iIntros "!> pts".
    iSplit. { iModIntro. iCrash. done. }
    iModIntro. iApply "pts".
  Qed.

  Lemma prove_crash_condition xss yss zss :
    (* x *)
    persist_lb x prot_x x_zero -∗
    x ↦_AT^{prot_x} xss -∗
    (* y *)
    persist_lb y prot_y false -∗
    y ↦_{prot_y} yss -∗
    (* z *)
    persist_lb z prot_z false -∗
    z ↦_{prot_z} zss -∗
    <PC> _, crash_condition.
  Proof.
    iIntros "xPLb xPts yPLb yPts zPLb zPts".
    iCrash.
    iDestruct "xPLb" as "[xPLb (%xsC & % & #xCrash)]".
    iDestruct "yPLb" as "[yPLb (%ysC & % & #yCrash)]".
    iDestruct "zPLb" as "[zPLb (%zsC & % & #zCrash)]".
    iDestruct (crashed_in_if_rec with "xCrash xPts") as (xsC') "[xCrash' disj]".
    iDestruct (crashed_in_agree with "xCrash xCrash'") as %<-.
    iDestruct "disj" as "[L|R]"; last first.
  Admitted.
    (* { iDestruct "R" as (? ([= eq] & le & neq)) "_". *)
    (*   exfalso. *)
    (*   destruct xsC; done. } *)
    (* iDestruct "L" as (xss xs pre le) "xPts". *)
    (* rewrite /crash_condition. *)
    (* iExists ((λ b : x_state, b) <$> xss), xs. iExistsN. *)
    (* iSplitL "xPts". { *)
    (* iFrame "xPts". *)
  (* Qed. *)

  Ltac solve_cc :=
    iApply (prove_crash_condition with "xPLb xPts yPLb yPts zPLb zPts").

  Lemma right_prog_spec :
    tok1 -∗
    ⎡ pre_borrow ⎤ -∗
    ⎡ own γag Pending ⎤ -∗
    (* x *)
    persist_lb x prot_x x_zero -∗
    x ↦_AT^{prot_x} [x_zero] -∗
    (* y *)
    persist_lb y prot_y false -∗
    y ↦_{prot_y} [false] -∗
    (* z *)
    persist_lb z prot_z false -∗
    z ↦_{prot_z} [false] -∗
    WPC right_prog x y z @ ⊤
      {{ v, True }}
      {{ <PC> _, crash_condition }}.
  Proof.
    iIntros "tok1 pre shot xPLb xPts yPLb yPts zPLb zPts".
    rewrite /right_prog.
    wpc_bind (_ <-_AT _)%E.
    wpc_atomic; first solve_cc.
    iApply (wp_store_at _ [] _ x_one with "[$xPts tok1]").
    { iSplitL "tok1". { simpl. iFrame "tok1". done. }
      iSplitPure; first done.
      iIntros (? sC ??).
      destruct sC; simpl.
      - iIntros "((-> & tok1) & (? & tok2) & (-> & tok3))".
        iDestruct (own_valid_2 with "tok1 tok3") as %hi%gset_disj_valid_op.
        set_solver.
      - iIntros "?". done.
      - iIntros "((-> & tok1) & (? & tok2) & (-> & tok3))".
        done. }
    iNext.
    iIntros "xPts".
    iSplit; iModIntro; first solve_cc.
    wpc_pures; first solve_cc.
    wpc_bind (!_AT _)%E.
    wpc_atomic; first solve_cc.
    iApply (wp_load_at _ _ _
             (λ v, ⌜ v = #1 ⌝)%I
             (λ s v, ⌜ s = x_two ∧ v = #2 ⌝)%I with "[xPts]").
    { iFrame "xPts".
      iSplit.
      - iIntros (??).
        (* iExists (λ s, ⌜ s = x_two ⌝)%I. *)
        admit.
      - iIntros (vs vL sL).
        iExists ⌜ sL = x_two ⌝%I.
        iIntros (sLe).
        iSplitL.
        { iIntros "L".
          iDestruct (big_sepL2_cons_inv_l with "L") as (???) "[[-> tok0] L]".
          iDestruct (big_sepL2_cons_inv_l with "L") as (bin go cat) "[[-> tok1] L]".
          iDestruct (big_sepL2_cons_inv_l with "L") as (ho hi hip) "[[eq tok2] L]".
          iDestruct (big_sepL2_nil_inv_l with "L") as %->.
          simpl.
          simplify_eq.
          assert (vL = ho) as <-. { admit. }
          destruct sL; first done; last done.
          iDestruct (own_valid_2 with "tok1 tok2") as %hi%gset_disj_valid_op.
          set_solver. }
        iIntros (->).
        iModIntro.
        simpl.
        iIntros "(-> & $)".
        done. }
    iIntros "!>" (?) "H".
    rewrite post_fence_flush_free.
    iAssert (∃ xss xs,
              x ↦_AT^{ prot_x} (xss ++ [xs]) ∗
              ((⌜ vL = #1 ∧ xss = [x_zero] ∧ xs = x_one ⌝) ∨
              (⌜ vL = #2 ∧ xss = [x_zero; x_one] ∧ xs = x_two ⌝)))%I
      with "[H]" as (xss xs) "[xPts disj]".
      { iDestruct "H" as "[(%sL & xPts & eq)|(xPts & ->)]".
        - iExists _, _.
          rewrite post_fence_flush_free.
          iDestruct "eq" as %(-> & ->).
          iFrame "xPts".
          iRight.
          done.
        - iExists _, _.
          iFrame "xPts".
          iLeft.
          done. }
    iSplit; first (iModIntro; solve_cc).

    (* Let us now do the irrevesible irrevocable forever-done action that is
     * firing the one-shot ghost state. *)
    iMod (own_update with "shot") as "shot".
    { apply (cmra_update_exclusive (Shot xs)). done. }
    iDestruct "shot" as "#shot".

    iModIntro.
    wpc_pures; first solve_cc.

    wpc_bind (Flush _)%E.
    iApply wpc_atomic_no_mask.
    iSplit; first solve_cc.
    iApply (wp_flush_at with "xPts").
    iIntros "!> (xPts & #fLb & _)".
    iSplit; iModIntro; first solve_cc.
    wpc_pures; first solve_cc.
    (* This is that spot where we hit a fork in the road. To take the if branch
     * or not to take the if branch. That is the question. *)
    iDestruct "disj" as "[(-> & -> & ->) | (-> & -> & ->)]".
    - rewrite bool_decide_false //.
      wpc_pures; first solve_cc.
      (* fence *)
      wpc_bind Fence.
      iApply wpc_atomic_no_mask.
      iSplit; first solve_cc.
      iApply wp_fence. do 2 iModIntro.
      iSplit; iModIntro; first solve_cc.
      wpc_pures; first solve_cc.
      (* write to [z] *)
      iApply wpc_atomic_no_mask.
      iSplit; first solve_cc.
      iDestruct "xPts" as "#xPts".
      iApply (wp_store_na _ _ _ _ _ true with "[$zPts]"); eauto.
      { simpl.
        iSplitPure; first done.
        iExists x_one.
        iFrame "shot fLb".
        iLeft.
        iSplitPure; first done.
        iFrame "xPts". }
      iIntros "!> zPts".
      iSplit; iModIntro; first solve_cc.
      done.
    - rewrite bool_decide_true //.
      wpc_pures; first solve_cc.

      wpc_bind (_ <-_NA _)%E.
      (* Write to y *)
      iApply wpc_atomic_no_mask.
      iSplit; first solve_cc.
      iApply (wp_store_na _ _ _ _ _ true with "[$yPts]");
        first done;
        first done.
      { simpl. iFrame "shot". done. }
      iIntros "!> yPts".
      iSplit; iModIntro; first solve_cc.

      wpc_pures; first solve_cc.

      wpc_bind Fence.
      iApply wpc_atomic_no_mask.
      iSplit; first solve_cc.
      iApply wp_fence. do 2 iModIntro.
      iSplit; iModIntro; first solve_cc.

      wpc_pures; first solve_cc.
      (* write to [z] *)
      iApply wpc_atomic_no_mask.
      iSplit; first solve_cc.
      iDestruct "xPts" as "#xPts".
      iApply (wp_store_na _ _ _ _ _ true with "[$zPts]"); eauto.
      { simpl.
        iSplitPure; first done.
        iExists x_two.
        iFrame "shot fLb".
        iRight.
        iSplitPure; first done.
        iFrame "xPts". }
      iIntros "!> zPts".
      iSplit; iModIntro; first solve_cc.
      done.
  Admitted.

  Lemma prog_spec :
    tok1 -∗ tok2 -∗
    ⎡ pre_borrow ⎤ -∗
    (* x *)
    persist_lb x prot_x None -∗
    (* y *)
    persist_lb y prot_y false -∗
    y ↦_{prot_y} [false] -∗
    (* z *)
    persist_lb z prot_z false -∗
    z ↦_{prot_z} [false] -∗
    WPC prog x y z @ ⊤
      {{ v, True }}
      {{ <PC> _, crash_condition }}.
  Proof. Admitted.

End proof.
