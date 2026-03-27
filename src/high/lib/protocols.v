From iris.proofmode Require Import reduction monpred ltac_tactics.

From self.base Require Import primitive_laws.
From self.high Require Import generational_resources abstract_state_instances protocol.

Set Default Proof Using "Type*".

Section constant_prot.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ}.

  Definition constant_prot (v1 : val) : LocationProtocol unit :=
    {|
      p_full := λ _ v2, ⌜ v1 = v2 ⌝%I;
      p_read := λ _ v2, ⌜ v1 = v2 ⌝%I;
      p_pers := λ _ v2, ⌜ v1 = v2 ⌝%I;
      p_bumper := id |}.

  #[global] Instance constant_prot_cond (v1 : val) :
    ProtocolConditions (constant_prot v1).
  Proof.
    split; try apply _.
    - iIntros (? ?). rewrite /p_full /p_read /=.
      iSplit.
      + by iIntros.
      + iIntros "[% %]".
        iPureIntro.
        naive_solver.
    - rewrite /p_full /p_read /=.
      iIntros (? ? ? ? _ _ ?).
      iSplit.
      + do 2 iModIntro.
        done.
      + iIntros (? ?) "!> % _ _".
        do 2 iModIntro.
        done.
    - rewrite /p_read /=.
      iIntros (? ?) "%".
      by iModIntro.
  Qed.

  (* a protocol that behaves similarly to the constant protocol,
   * but instead of having different protocols we use discrete abstract state. *)
  Definition discrete_prot: LocationProtocol (discreteState val) :=
    {|
      p_full σ v := ⌜ v = get_discrete σ ⌝%I;
      p_read σ v := ⌜ v = get_discrete σ ⌝%I;
      p_pers σ v := ⌜ v = get_discrete σ ⌝%I;
      p_bumper := id;
    |}.

  #[global] Instance discrete_prot_cond:
    ProtocolConditions discrete_prot.
  Proof.
    split; try apply _; rewrite /discrete_prot /=.
    - iIntros.
      iSplit; first naive_solver.
      iIntros "[$ _]".
    - iIntros.
      iSplit; first by do 2 iModIntro.
      iIntros (??) "!> %%%".
      by do 2 iModIntro.
    - iIntros.
      by iModIntro.
  Qed.
End constant_prot.
