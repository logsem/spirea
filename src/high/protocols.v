
From iris.proofmode Require Import reduction monpred tactics.

From self.high Require Import dprop dprop_liftings resources modalities post_crash_modality.
From self.lang Require Import lang.
From self.high Require Import abstract_state_instances protocol.

Section constant_prot.
  Context `{nvmG Σ}.

  Program Definition constant_prot (v1 : val) : LocationProtocol unit :=
    {| p_inv := λ _ v2, ⌜ v1 = v2 ⌝%I;
       p_bumper := id |}.

  Global Instance constant_prot_cond (v1 : val) :
    ProtocolConditions (constant_prot v1).
  Proof.
    split; [apply _ | apply _| ].
    iIntros. by iApply post_crash_flush_pure.
  Qed.

End constant_prot.
