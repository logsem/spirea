(* This file defines additional [CmraMorphisms] and instances in addition to
 * those included in Iris. *)

From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

(* For this we require [CmraTotal A] and [CoreId b]. We could add weaker
 * requirements, but these are convenient as t.c. search can solver them. *)
Global Instance cmra_morphism_const {A B : cmra} `{CmraTotal A} (b : B) `{!CoreId b} :
  b ⋅ b ≡ b →
  ✓ b →
  CmraMorphism (A := A) (const b).
Proof.
  intros Hidemp Hval.
  split; first apply _.
  - intros ???. apply cmra_valid_validN. done.
  - intros. rewrite cmra_pcore_core core_id. done.
  - done.
Qed.

#[global]
Instance cmra_morphism_const_agree {A B : ofe} (b : B) :
  CmraMorphism (A := agree A) (const (to_agree b)).
Proof. apply cmra_morphism_const; [apply _|apply agree_idemp|done]. Qed.

(* A [CmraMorphism] over [auth]. *)

Definition fmap_pair A {B C} (f : B → C) (p : A * B) : (A * C) :=
  (p.1, f p.2).

#[global]
Instance fmap_pair_ne {A B C : ofe} (f : B → C) `{NonExpansive f} :
  NonExpansive (@fmap_pair A _ _ f).
Proof. solve_proper. Qed.

Definition fmap_auth {A : ucmra} (t : A → A) (a : auth A) : auth A :=
  View
    (fmap_pair dfrac (agree_map t) <$> a.(view_auth_proj))
    (t a.(view_frag_proj)).

Section fmap_auth.
  Context {A : ucmra}.
  Implicit Types (t : A → A).

  #[global]
  Instance fmap_auth_ne `{NonExpansive t} : NonExpansive (fmap_auth t).
  Proof. unfold fmap_auth. solve_proper. Qed.

  #[global]
  Instance fmap_auth_gentrans `{!CmraMorphism t} : CmraMorphism (fmap_auth t).
  Proof.
    unfold fmap_auth.
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
        + apply: cmra_morphism_monotoneN. done.
        + apply: cmra_morphism_validN. done.
      * intros (a' & ? & ?).
        exists (t a').
        split.
        + apply: cmra_morphism_monotoneN. done.
        + apply: cmra_morphism_validN. done.
    - rewrite view.view_pcore_eq.
      intros [[[??]|]?]; simpl;
        rewrite cmra_morphism_core; last done.
      unfold core.
      f_equiv.
      f_equiv; last done.
      rewrite /fmap_pair /= 2!pair_pcore /=.
      destruct (pcore d) eqn:eq; rewrite eq; done.
    - intros [[[??]|]?]; simpl;
        intros [[[??]|]?]; simpl; rewrite !cmra_morphism_op; try done.
      rewrite view.view_op_eq. simpl.
      rewrite -Some_op.
      rewrite /fmap_pair /=.
      rewrite -pair_op.
      rewrite cmra_morphism_op.
      solve_proper.
  Qed.

  Lemma fmap_auth_frag a t :
    fmap_auth t (◯ a) = ◯ (t a).
  Proof. done. Qed.

End fmap_auth.

#[global]
Instance core_cmra_morphism `{CmraTotal A} : @CmraMorphism A _ core.
Proof.
  split.
  - apply _.
  - apply cmra_core_validN.
  - intros a.
    rewrite !cmra_pcore_core.
    done.
  - intros ??.
Abort.

#[global]
Instance pcore_cmra_morphism {A : cmra} : @CmraMorphism A _ pcore.
Proof.
  split.
  - apply _.
  - intros n a Hv. destruct (pcore a) as [a'|] eqn:eq; last done.
    apply Some_validN.
    eapply cmra_pcore_validN; done.
  - intros a.
    destruct (pcore a) as [a'|] eqn:eq; simpl.
Abort.
