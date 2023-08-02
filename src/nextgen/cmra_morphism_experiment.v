From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.
From iris.algebra Require Import csum excl auth dfrac.

(*
  What is the correct definition of a morphism between cameras?

  The definition in Iris requires `f <$> pcore x ≡ pcore (f x)`. With this the
  projections `fst` and `snd` fail to be morphisms:

  ```
  snd <$> pcore (Excl (), DfracDiscarded) ≡ pcore (snd (Excl (), DfracDiscarded))
  ```

  iff.

  ```
  None ≡ DfracDiscarded
  ```
 *)

(* The projection [snd] is not a [CmraMorphism]. *)
Lemma snd_not_cmra_morphism :
  ¬ (∀ (A B : cmra), CmraMorphism (@snd A B)).
Proof.
  intros ?.
  specialize (cmra_morphism_pcore snd (Excl (), DfracDiscarded)).
  simpl.
  naive_solver.
Qed.

(*
  With `pcore a = Some pa → Some (f pa) ≡ pcore (f a)` the projections are
  morphisms but then `fmap f : option A → option B` where `f : A → B` is a morphisms is not
  a morphism. Taking `a = Some (Excl (), DfracDiscarded)` and `pa = None`:


  pcore (Some (Excl (), DfracDiscarded)) = Some None →
    Some (fmap snd None) ≡ pcore (fmap snd (Some (Excl (), DfracDiscarded))
  ```

  implies

  ```
  Some None ≡ Some (Some DfracDiscarded)
  ```
 *)

Definition test {M : cmra} (a : M) (f : M → M) : Prop :=
  default True (pa ← pcore a; mret (Some (f pa) ≡ pcore (f a))).

(* The properties that a generational transformation (GT), i.e., the function
that transforms the ghost state into a new generation, needs to satisfy. Note
that this class is used both for the "global" GT that applies to the single
unital camera and to individual GTs for a specific camera. *)
Class CmraMorphismAlt {M M2 : cmra} (f : M → M2) := {
    cmra_morphism_alt_ne :> NonExpansive f;
    cmra_morphism_alt_valid : ∀ n (a : M), ✓{n} a → ✓{n} (f a);
    cmra_morphism_alt_pcore : ∀ (a : M) pa,
      pcore a = Some pa →
      Some (f pa) ≡ pcore (f a); (* CHANGED: is [f <$> pcore x ≡ pcore (f x)] in Iris *)
    cmra_morphism_alt_op : ∀ (a b : M), f (a ⋅ b) ≡ f a ⋅ f b
  }.

Global Instance gen_trans_proper {A : cmra} (f : A → A) :
  CmraMorphismAlt f → Proper ((≡) ==> (≡)) f.
Proof. intros ?. apply: ne_proper. Qed.

Global Arguments cmra_morphism_alt_op {_ _} _ {_} _ _.

(* The projection [snd] _is_ a [CmraMorphismAlt]. *)
Global Instance gen_trans_snd {A B : cmra} : CmraMorphismAlt (@snd A B).
Proof.
  split; first apply _.
  - intros ? [??] [??]. done.
  - intros [??] [??]. intros [? eq]%prod_pcore_Some. rewrite eq. done.
  - intros [??] [??]. done.
Qed.

(* The [pcore] condition in [CmraMorphismAlt] does not hold for [fmap f :
 * option A → option B] for some [f : A → B] *)
Lemma fmap_option_pcore :
  ¬ (∀ (A B : cmra) (f : A → B),
      CmraMorphismAlt f →
      ∀ (a : option A) pa,
        pcore a = Some pa →
        Some (fmap f pa) ≡ pcore (fmap f a)).
Proof.
  intros Ha.
  specialize (
    Ha
      (prodR (exclR unitO) dfracR) _ snd _
      (Some (Excl (), DfracDiscarded)) None eq_refl
  ).
  (* simpl in Ha. *)
  (* unfold pcore, cmra_pcore in Ha. simpl in Ha. *)
  (* unfold option_pcore_instance in Ha. simpl in Ha. *)
  simplify_eq.
Qed.

(* The proof of the instance fails so we admit it. *)
Global Instance gen_trans_fmap {A B : cmra} (f : A → B) :
  CmraMorphismAlt f → CmraMorphismAlt (fmap f : optionR A → optionR B).
Proof.
  split; first apply _.
  - intros ? [?|]; last done. simpl. rewrite 2!Some_validN. apply cmra_morphism_alt_valid.
  - move=> [a|] [a'|] //.
    * simpl in *.
      intros [= eq].
      apply (cmra_morphism_alt_pcore) in eq.
      rewrite eq.
      done.
    * intros [= eq].
      apply Some_proper.
      simpl.
      admit.
  - move=> [a|] [b|] //=.
    rewrite (cmra_morphism_alt_op f) //.
Admitted.

(* With the admitted instance we have a contradiction. *)
Lemma oops : False.
Proof.
  apply fmap_option_pcore. intros ????. apply cmra_morphism_alt_pcore.
Qed.
