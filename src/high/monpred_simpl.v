From iris Require Import bi.monpred.
From iris.bi Require Import bi.

From self.high Require Import dprop.

Section bi_monpred_extra.
  Context {I : biIndex} {PROP : bi}.
  Local Notation monPred := (monPred I PROP).
  Local Notation monPredI := (monPredI I PROP).
  Local Notation monPred_at := (@monPred_at I PROP).
  Local Notation BiIndexBottom := (@BiIndexBottom I).
  Implicit Types i : I.
  Implicit Types P Q : monPred.

  Lemma monPred_at_if i (P Q : monPred) (b : bool) :
    (if b then P else Q) i ⊣⊢ if b then P i else Q i.
  Proof. by destruct  b. Qed.

End bi_monpred_extra.

Hint Rewrite (@monPred_at_forall thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_exist thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_and thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_or thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_wand thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_later thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_sep thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_objectively thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_pure thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_embed thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_if thread_view_bi_index) : monpred_simpl.
Ltac monPred_simpl := autorewrite with monpred_simpl.
