From iris.algebra Require Import csum excl auth.

From self Require Import gen_trans.

Definition fmap_pair A {B C} (f : B → C) (p : A * B) : (A * C) :=
  (p.1, f p.2).

#[global]
Instance fmap_pair_ne {A B C : ofe} (f : B → C) `{NonExpansive f} :
  NonExpansive (@fmap_pair A _ _ f).
Proof. solve_proper. Qed.

Definition gen_trans_auth {A : ucmra} (t : A → A) (a : auth A) : auth A :=
  View
    (fmap_pair dfrac (agree_map t) <$> a.(view_auth_proj))
    (t a.(view_frag_proj)).

Section gen_trans.
  Context {A : ucmra}.
  Implicit Types (t : A → A).

  #[global]
  Instance gen_trans_auth_ne `{NonExpansive t} : NonExpansive (gen_trans_auth t).
  Proof. unfold gen_trans_auth. solve_proper. Qed.

  #[global]
  Instance gen_trans_auth_gentrans `{!GenTrans t} : GenTrans (gen_trans_auth t).
  Proof.
    unfold gen_trans_auth.
    split.
    - apply _.
    - rewrite view.view_validN_eq /= /auth_view_rel_raw.
      intros ? [[[??]|]?]; simpl.
      * intros [? (a' & eq & ? & ?)].
        split; first done.
        exists (t a').
        rewrite eq.
        rewrite agree_map_to_agree.
        split; first done.
        split.
        + apply: generation_monoN. done.
        + apply generation_valid. done.
      * intros (a' & ? & ?).
        exists (t a').
        split.
        + apply: generation_monoN. done.
        + apply generation_valid. done.
    - rewrite view.view_pcore_eq.
      intros [[[??]|]?]; simpl;
        rewrite generation_core; last done.
      unfold core.
      f_equiv.
      f_equiv; last done.
      rewrite /fmap_pair /= 2!pair_pcore /=.
      destruct (pcore d) eqn:eq; rewrite eq; done.
    - intros [[[??]|]?]; simpl;
        intros [[[??]|]?]; simpl; rewrite !generation_op; try done.
      rewrite view.view_op_eq. simpl.
      rewrite -Some_op.
      rewrite /fmap_pair /=.
      rewrite -pair_op.
      rewrite cmra_morphism_op.
      solve_proper.
  Qed.

End gen_trans.