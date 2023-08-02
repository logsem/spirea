From iris.algebra Require Import csum excl.

From self Require Import cmra_morphism_extra.

(******************************************************************************)
(* Generational single-shot stream.

   The generational single-shot stream makes it possible to own a "permanent"
   exclusive token that is preserved across generations. For each generation the
   "permanent" token also "produces" a per-generation token that is only valid
   for the current generation.  *)

Definition one_shot A := csum (excl unit) (agree A).
Definition one_shotR (A : Type) := csumR (exclR unitO) (agreeR (leibnizO A)).

Definition GTS A : Type := excl' () * option (one_shot A).
Definition GTSR A : cmra :=
  prodR (optionR (exclR unitO)) (optionR (one_shotR A)).

(** The per-generation token. *)
Definition GTS_tok_gen {A} : GTS A := (None, Some $ Cinl $ Excl ()).
(** The per-generation token has been used to make decision. *)
Definition GTS_tok_gen_shot {A} f : GTS A := (None, Some $ Cinr $ to_agree f).
(** The permanent cross-generation token. *)
Definition GTS_tok_perm {A} : GTS A := (Excl' (), None).
(** Both tokens. *)
Definition GTS_tok_both {A} : GTS A := (Excl' (), Some $ Cinl $ Excl ()).

Definition GTS_floor {A} (a : GTS A) : GTS A :=
  (* The cross-generation permanent token is preserved and also produces the
  per-generation token. *)
  match a with
    (Excl' (), _) => (Excl' (), Some $ Cinl $ Excl ())
  | (None, _) => (None, None)
  | (ExclBot', _) => (ExclBot', Some $ Cinl $ ExclBot)
  end.

Global Instance GTS_floor_generation A : CmraMorphism (GTS_floor (A := A) : GTSR A → GTSR A).
Proof.
  split.
  - intros n [??] [??]. simpl.
    rewrite -discrete_iff.
    intros [eq%leibniz_equiv ?].
    simpl in eq.
    rewrite eq.
    solve_proper.
  - intros ? [[[[]|]|] [[[[]|]|?|]|]]; cbv; naive_solver.
  - intros [[[[]|]|] [[[[]|]|?|]|]]; done.
  - do 2 intros [[[[]|]|] [[[[]|]|?|]|]]; try done.
Qed.

Lemma GTS_tok_gen_shot_agree {M} {A} (t1 t2 : A) :
  ✓ ((GTS_tok_gen_shot t1 : GTSR A) ⋅ (GTS_tok_gen_shot t2 : GTSR A))
    ⊣⊢@{uPredI M} ⌜ t1 = t2 ⌝.
Proof.
  rewrite /GTS_tok_gen_shot.
  rewrite !prod_validI. simpl.
  rewrite -Some_op.
  rewrite -Cinr_op.
  rewrite option_validI. simpl.
  rewrite option_validI. simpl.
  rewrite csum_validI.
  rewrite left_id.
  rewrite to_agree_op_validI.
  rewrite -leibniz_equiv_iff.
  apply (anti_symm _); naive_solver.
Qed.

Lemma GTS_tok_gen_shot_idemp {A} (a : A) :
  (GTS_tok_gen_shot a : GTSR A) ⋅ GTS_tok_gen_shot a ≡ GTS_tok_gen_shot a.
Proof.
  rewrite -pair_op -Some_op -Cinr_op. rewrite agree_idemp. done.
Qed.

Section gts.

  Lemma GTS_floor_perm {A : Type} :
    GTS_floor (GTS_tok_perm) =@{GTSR A} GTS_tok_perm ⋅ GTS_tok_gen.
  Proof. reflexivity. Qed.

  Lemma GTS_floor_gen {A} : GTS_floor (GTS_tok_gen) =@{GTSR A} (None, None).
  Proof. reflexivity. Qed.

End gts.
