From iris Require Import bi.monpred.

From self.high Require Import dprop.

Hint Rewrite (@monPred_at_forall thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_exist thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_and thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_or thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_wand thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_later thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_sep thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_objectively thread_view_bi_index) : monpred_simpl.
Hint Rewrite (@monPred_at_pure thread_view_bi_index) : monpred_simpl.
Ltac monPred_simpl := autorewrite with monpred_simpl.
