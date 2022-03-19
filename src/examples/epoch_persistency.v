From stdpp Require Import numbers countable.

From iris.algebra Require Import excl agree csum.
From iris.proofmode Require Import tactics.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances.
From self.high Require Import proofmode wpc_proofmode.
From self.high Require Import dprop resources crash_weakestpre weakestpre
     weakestpre_na recovery_weakestpre lifted_modalities modalities
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

(* One shot resource algebra that we use in this example. *)
Definition one_shotR := csumR (exclR unitO) (agreeR ZO).
Definition Pending : one_shotR := Cinl (Excl ()).
Definition Shot (n : Z) : one_shotR := Cinr (to_agree n).

Class one_shotG Σ := { one_shot_inG :> inG Σ one_shotR }.
Definition one_shotΣ : gFunctors := #[GFunctor one_shotR].
Global Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
Proof. solve_inG. Qed.

Section proof.
  Context `{nvmFixedG Σ, nvmDeltaG Σ, one_shotG Σ }.

  Context (x y z : loc).

  (* Protocol for [x]. *)

  Program Definition prot_x :=
    {| pred (n : Z) (v : val) _ := ⌜ v = #x ⌝%I;
      bumper b := b; |}.
  Next Obligation. iIntros (???) "H". iCrashFlush. done. Qed.

  (* Protocol for [y]. *)

  Program Definition prot_y (γ : gname) :=
    {| pred (b : bool) (v : val) _ :=
        match b with
          false => ⌜ v = #0 ⌝
        | true => ⌜ v = #1 ⌝ ∗ ⎡ own γ (Shot 2) ⎤
        end%I;
      bumper b := b; |}.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

  (* Protocol for [z]. *)

  Program Definition prot_z (γ : gname) :=
    {| pred (b : bool) (v : val) _ :=
        match b with
          false => ⌜ v = #0 ⌝
        | true => ⌜ v = #1 ⌝ ∗ ∃ n, ⎡ own γ (Shot n) ⎤ ∗ flush_lb x prot_x n
        end%I;
      bumper b := b; |}.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

End proof.
