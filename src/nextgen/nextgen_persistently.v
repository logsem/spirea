From self Require Import basic_nextgen_modality.
(* From self.nextgen Require Import gen_trans. *)

Import uPred.

Section bnextgen_rules.
  Context {M : ucmra}.

  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q).
  Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.

  Implicit Types (P Q : uPred M).

  Local Arguments uPred_holds {_} !_ _ _ /.

  Notation "□ P" := (uPred_persistently P) : bi_scope.

  #[global]
  Instance core_gentrans : GenTrans (core (A := M)).
  Proof.
    split.
    - apply _.
    - apply cmra_core_validN.
    - intros ???. apply cmra_core_monoN.
    Qed.

  Definition ng_persistently P : uPred M := ⚡={core}=> P.

  Lemma ng_persistently_equiv P :
    □ P ⊣⊢ ng_persistently P.
  Proof.
    unfold ng_persistently.
    uPred.unseal.
    rewrite !basic_nextgen_modality.uPred_bnextgen_unseal.
    done.
  Qed.

End bnextgen_rules.
