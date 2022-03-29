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
     post_crash_modality protocol no_buffer abstract_state_instances locations protocol.
From self.high.modalities Require Import fence.

Section program.

  Definition leftProg (x : loc) : expr :=
    #x <-_AT #2.

  Definition rightProg (x y z : loc) : expr :=
    #x <-_AT #1 ;;
    let: "a" := !_AT #x in
    Flush #x ;;
    if: "a" = #2
    then #y <-_NA #1
    else #() ;;
    Fence ;;
    #z <-_NA #1.

  Definition prog (x y z : loc) : expr :=
    Fork (leftProg x) ;; rightProg x y z.

  Definition recovery x y z : expr :=
    if: (!_NA #y = #true) && (!_NA #z = #true)
    then assert: !_AT x = #2
    else #().

End program.

Definition x_state := option (bool + bool).

(* One shot resource algebra that we use in this example. *)
Definition one_shotR := csumR (exclR unitO) (agreeR (leibnizO x_state)).
Definition Pending : one_shotR := Cinl (Excl ()).
Definition Shot (n : x_state) : one_shotR := Cinr (to_agree n).

Class one_shotG Σ := { one_shot_inG :> inG Σ one_shotR }.
Definition one_shotΣ : gFunctors := #[GFunctor one_shotR].
Global Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{nvmFixedG Σ, nvmDeltaG Σ, one_shotG Σ, inG Σ (gset_disjR nat) }.

  Context (x y z : loc) (γag : gname) (γtok : gname).

  (* Protocol for [x]. *)

  Definition zero : x_state := None.
  Definition one_l : x_state := Some (inl false).
  Definition one_r : x_state := Some (inr false).
  Definition two_l : x_state := Some (inl true).
  Definition two_r : x_state := Some (inr true).

  Definition x_state_to_nat (s : x_state) : nat :=
    match s with
      None => 0
    | Some (inl false) => 1
    | Some (inr false) => 1
    | Some (inl true) => 2
    | Some (inr true) => 2
    end%I.

  Definition tok0 : dProp Σ := ⎡ own γtok (GSet {[ 0 ]}) ⎤.
  Definition tok1 : dProp Σ := ⎡ own γtok (GSet {[ 1 ]}) ⎤.
  Definition tok2 : dProp Σ := ⎡ own γtok (GSet {[ 2 ]}) ⎤.
  Definition tokFin1 : dProp Σ := ⎡ own γtok (GSet {[ 3 ]}) ⎤.
  Definition tokFin2 : dProp Σ := ⎡ own γtok (GSet {[ 4 ]}) ⎤.

  Program Definition prot_x := {|
    pred s v _ := (
      ⌜ v = #(x_state_to_nat s) ⌝ ∗
      (* (⌜ s = zero ⌝ ∨ *)
      (*   ⌜ s = two_l ⌝ ∗ tok2 ∗ (tokFin1 ∨ tokFin2) ∨ *)
      (*   ⌜ s = one_l ⌝ ∗ tok1 ∗ tokFin1 ∨ *)
      (*   ⌜ s = one_r ⌝ ∗ tok1 ∗ (tokFin1 ∨ tokFin2) ∨ *)
      (*   ⌜ s = two_r ⌝ ∗ tok2 ∗ tokFin2))%I *)
      match s with
        None => tok0
      | Some (inl true) => tok2 ∗ (tokFin1 ∨ tokFin2)
      | Some (inl false) => tok1 ∗ tokFin1
      | Some (inr false) => tok1 ∗ (tokFin1 ∨ tokFin2)
      | Some (inr true) => tok2 ∗ tokFin2
      end)%I
    ;
    bumper b := b;
  |}.
  Next Obligation. iIntros (? [[[|]|[|]]|] ?) "H"; simpl; iCrashFlush; done. Qed.

  (* Protocol for [y]. *)

  Program Definition prot_y :=
    {| pred (b : bool) (v : val) _ :=
        match b with
          false => ⌜ v = #0 ⌝
        | true => ⌜ v = #1 ⌝ ∗ ⎡ own γag (Shot two_r) ⎤
        end%I;
      bumper b := b; |}.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

  (* Protocol for [z]. *)

  Program Definition prot_z :=
    {| pred (b : bool) (v : val) _ :=
        match b with
          false => ⌜ v = #0 ⌝
        | true => ⌜ v = #1 ⌝ ∗ ∃ n, ⎡ own γag (Shot n) ⎤ ∗ flush_lb x prot_x n
        end%I;
      bumper b := b; |}.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

  Definition crash_condition {hD : nvmDeltaG Σ} : dProp Σ :=
    ∃ (yb bz : bool),
      ⎡ is_at_loc x ⎤ ∗
      persist_lb x prot_x None ∗
      (* y *)
      persist_lb y prot_y false ∗
      y ↦_{prot_y} [yb] ∗
      (* z *)
      persist_lb z prot_z false ∗
      z ↦_{prot_z} [bz].

  Definition left_crash_condition {hD : nvmDeltaG Σ} : dProp Σ :=
    ⎡ is_at_loc x ⎤ ∗ persist_lb x prot_x None.

 (*  Lemma left_prog_spec : *)
 (*    tok2 -∗ tokFin1 -∗ ⎡ is_at_loc x ⎤ -∗ persist_lb x prot_x None -∗ *)
 (*    WPC leftProg x @ ⊤ *)
 (*      {{ v, store_lb x prot_x two_l ∨ store_lb x prot_x two_r }} *)
 (*      {{ <PC> _, True }}. *)
 (*  Proof. *)
 (*    iIntros "tok tokFin #atLoc #perLb". *)
 (*    rewrite /leftProg. *)
 (*    iApply wpc_atomic_no_mask. *)
 (*    iSplit. { iCrash. done. } *)
 (*    iApply ( *)
 (*        wp_store_at_strong _ (λ s, ⌜ s = two_l ∨ s = two_r ⌝)%I with "[$atLoc tok tokFin]"). *)
 (*    { iDestruct (persist_lb_to_store_lb with "perLb") as "$". *)
 (*      iIntros (s_l v_l le). *)
 (*      (* [s_l] can either be [zero] or [one_r]. *) *)
 (*      destruct (decide (s_l = zero)) as [->|neq]. *)
 (*      - iExists two_l. *)
 (*        iSplit. { *)
 (*          iIntros (? [[[|]|[|]]|] ??) "H1 [-> H2]"; simpl. *)
 (*          * admit. *)
 (*          * admit. *)
 (*          * admit. *)
 (*          * admit. *)
 (*          * admit. } *)
 (* (* simplify_eq. *) *)
 (*          (* iSplit; first done. *) *)
 (*          (* admit. } *) *)
 (*        iSplitL "". { iModIntro. iIntros "$". rewrite left_id. iAccu. } *)
 (*        iIntros "_". *)
 (*        iSplit; last (iLeft; done). *)
 (*        iSplitPure; first done. *)
 (*        iRight. iLeft. iFrame. done. *)
 (*      - iExists two_r. *)
 (*        iSplitL "". { admit. } *)
 (*        simpl. iSplitPure; first done. *)
 (*        iRight. iRight. iRight. iRight. iFrame. done. *)
 (*      } *)
 (*  Qed. *)

  Lemma right_prog_spec :
    tokFin1 -∗ tok2 -∗
    ⎡ pre_borrow ⎤ -∗
    (* x *)
    ⎡ is_at_loc x ⎤ -∗
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

  Lemma prog_spec :
    tok1 -∗ tok2 -∗
    tokFin1 -∗ tokFin2 -∗
    ⎡ pre_borrow ⎤ -∗
    (* x *)
    ⎡ is_at_loc x ⎤ -∗
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
