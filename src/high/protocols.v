
From iris.proofmode Require Import reduction monpred tactics.

From self.high Require Import dprop dprop_liftings resources modalities post_crash_modality.
From self.lang Require Import lang.
From self.high Require Import abstract_state_instances protocol.

Section constant_prot.
  Context `{nvmG Σ}.

  Program Definition constant_prot (v1 : val) : LocationProtocol unit :=
    {| pred := λ _ v2, ⌜ v1 = v2 ⌝%I;
       bumper := id |}.
  Next Obligation. iIntros. by iApply post_crash_flush_pure. Qed.

End constant_prot.
