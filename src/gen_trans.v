From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

(* The properties that a generational transformation (GT), i.e., the function
that transforms the ghost state into a new generation, needs to satisfy. Note
that this class is used both for the "global" GT that applies to the single
unital camera and to individual GTs for a specific camera. *)
Class GenTrans {M : cmra} (f : M → M) := {
    generation_ne :> NonExpansive f;
    (* The function should be monotone with respect to the inclusion order of
    the monoid. *)
    (* generation_mono : ∀ x y, x ≼ y → f x ≼ f y; *)
    (* Validity is preserved. *)
    generation_valid : ∀ n (a : M), ✓{n} a → ✓{n} (f a);
    (* The generation comutes with the core. *)
    (* generation_core_some : ∀ (a : M) pa, *)
    (*   pcore a = Some pa → Some (f pa) ≡ pcore (f a); *)
    generation_pcore x : f <$> pcore x ≡ pcore (f x);
    generation_op : ∀ (a b : M),
      (* ✓{n} (a ⋅ b) → *)
      f (a ⋅ b) ≡ f a ⋅ f b
  }.

Global Instance gen_trans_proper {A : cmra} (f : A → A) :
  GenTrans f → Proper ((≡) ==> (≡)) f.
Proof. intros ?. apply: ne_proper. Qed.

Lemma gen_trans_monotone {A : cmra} (f : A → A) `{!GenTrans f} x y :
  x ≼ y → f x ≼ f y.
Proof. intros [z ->]. exists (f z). rewrite generation_op. done. Qed.

Global Arguments generation_op {_} _ {_} _ _.

Global Instance gen_trans_cmra_morphism {A : cmra} (f : A → A) :
  GenTrans f → CmraMorphism f.
Proof.
  split.
  - apply generation_ne.
  - apply generation_valid.
  - apply generation_pcore.
  - Abort.

Lemma generation_monoN {M : ucmra} (f : M → M) `{!GenTrans f} n x y :
  x ≼{n} y → f x ≼{n} f y.
Proof.
  intros [z ->].
  apply cmra_included_includedN, gen_trans_monotone, cmra_included_l.
  apply _.
Qed.

Global Instance gen_trans_prod_map {A B : cmra} (f : A → A) (g : B → B) :
  GenTrans f → GenTrans g → GenTrans (prod_map f g).
Proof.
  split; first apply _.
  - intros ? [??] [??]. split; simpl; apply generation_valid; done.
  - intros x. etrans; last apply (reflexivity (mbind _ _)).
    etrans; first apply (reflexivity (_ <$> mbind _ _)). simpl.
    assert (Hf := generation_pcore (x.1)).
    destruct (pcore (f (x.1))), (pcore (x.1)); inversion_clear Hf=>//=.
    assert (Hg := generation_pcore (x.2)).
    destruct (pcore (g (x.2))), (pcore (x.2)); inversion_clear Hg=>//=.
    by setoid_subst.
  - intros [??] [??]. simpl in *.
    do 2 rewrite (generation_op _) //.
Qed.

Global Instance gen_trans_fmap {A : cmra} (f : A → A) :
  GenTrans f → GenTrans (fmap f : optionR A → optionR A).
Proof.
  split; first apply _.
  - intros ? [?|]; last done. simpl.
    rewrite 2!Some_validN.
    apply generation_valid.
  - move=> [a|] //. apply Some_proper, generation_pcore.
  - move=> [a|] [b|] //=.
    rewrite (generation_op f) //.
Qed.
