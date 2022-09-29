From iris.algebra Require Import agree excl.
From iris.proofmode Require Import classes.
From iris.base_logic.lib Require Export iprop own.
From iris.prelude Require Import options.
Import uPred.

Class Generation {M : ucmra} (f : M → M) := {
    generation_ne :> NonExpansive f;
    generation_mono : ∀ x y, x ≼ y → f x ≼ f y;
    generation_valid : ∀ n (a : M), ✓{n} a → ✓{n} (f a);
    generation_op : ∀ n (a b : M), ✓{n} (a ⋅ b) → f (a ⋅ b) = f a ⋅ f b
}.

Lemma generation_monoN {M : ucmra} (f : M → M) `{!Generation f} n x y :
  x ≼{n} y → f x ≼{n} f y.
Proof.
  intros [z ->].
  apply cmra_included_includedN, generation_mono, cmra_included_l.
Qed.

(** When working in the model, it is convenient to be able to treat [uPred] as
[nat → M → Prop]. But we only want to locally break the [uPred] abstraction
this way. *)
Local Coercion uPred_holds : uPred >-> Funclass.

Local Program Definition uPred_bgupd_def {M : ucmra}
  (f : M → M) `{!Generation f} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n (f x) |}.
Next Obligation. naive_solver eauto using uPred_mono, generation_monoN. Qed.

Local Definition uPred_bgupd_aux : seal (@uPred_bgupd_def).
Proof. by eexists. Qed.

Definition uPred_bgupd {M : ucmra} f `{g : !Generation f} := uPred_bgupd_aux.(unseal) M f g.

Local Definition uPred_bgupd_unseal :
  @uPred_bgupd = @uPred_bgupd_def := uPred_bgupd_aux.(seal_eq).

Notation "⚡={ f }=> P" := (uPred_bgupd f P)
  (at level 99, f at level 50, P at level 200, format "⚡={ f }=>  P") : bi_scope.

Section rules.

  Context {M : ucmra}.

  Implicit Types (f : M → M).

  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  (* Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope. *)

  Local Arguments uPred_holds {_} !_ _ _ /.
  (* Local Hint Immediate uPred_in_entails : core. *)

  Ltac unseal := try uPred.unseal; rewrite !uPred_bgupd_unseal !/uPred_holds /=.

  Lemma bgupd_ownM f `{!Generation f} (a : M) :
    uPred_ownM a ⊢ ⚡={f}=> uPred_ownM (f a).
  Proof.
    unseal. split. simpl.
    intros n x Hv ?.
    apply generation_monoN; done.
  Qed.

  Lemma bgupd_sep f `{!Generation f} P Q :
    (⚡={f}=> P) ∗ (⚡={f}=> Q) ⊢ ⚡={f}=> (P ∗ Q) .
  Proof.
    unseal. split. simpl.
    intros ? ? ?.
    intros (a & b & eq & Hp & Hq).
    exists (f a), (f b).
    rewrite -(generation_op n a b).
    - rewrite eq. done.
    - rewrite -eq. done.
  Qed.

  Lemma bgupd_intro_plain f `{!Generation f} P :
    ■ P ⊢ ⚡={f}=> ■ P.
  Proof. unseal. split. done. Qed.

  Lemma bgupd_plainly f `{!Generation f} P :
    (⚡={f}=> ■ P) ⊢ P.
  Proof.
    unseal. split. simpl. intros ????. simpl.
    eauto using uPred_mono, ucmra_unit_leastN.
  Qed.

  Lemma bgupd_mono f `{!Generation f} P Q :
    (P ⊢ Q) → (⚡={f}=> P) ⊢ ⚡={f}=> Q.
  Proof.
    intros [Hi].
    unseal. split. simpl.
    intros ???.
    apply Hi.
    apply generation_valid.
    done.
  Qed.

End rules.

(******************************)
(* Generational token stream. *)

Definition GTS : Type := excl' () * excl' ().
Definition GTSR : cmra :=
  prodR (optionR (exclR unitO)) (optionR (exclR unitO)).

Definition GTS_floor (a : GTS) : GTS :=
  match a with
  | (_, ExclBot') => (ExclBot', ExclBot')
  | (ExclBot', _) => (ExclBot', ExclBot')
  | (None, None) => (None, None)
  (* The per-generation token is lost. *)
  | (None, Excl' ()) => (None, None)
  (* The cross-generation permanent token is preserved and also produces the
  per-generation token. *)
  | (Excl' (), _) => (Excl' (), Excl' ())
  end.

Definition GTS_tok_gen : GTS := (None, Excl' ()).
Definition GTS_tok_perm : GTS := (Excl' (), None).
Definition GTS_tok_both : GTS := (Excl' (), Excl' ()).

Lemma excl_bot_top {A : ofe} (a : excl A) : a ≼ ExclBot.
Proof. eexists ExclBot. done. Qed.

Lemma excl'_bot_top {A : ofe} (a : excl' A) : a ≼ ExclBot'.
Proof. eexists ExclBot'. destruct a; done. Qed.

Lemma excl'_bot_top_top {A : ofe} (a : excl' A) : ExclBot' ≼ a → a ≡ ExclBot'.
Proof. intros [[|] E]; apply E. Qed.

Instance GTS_floor_generation : Generation GTS_floor.
Proof.
  split.
  - intros ???.
    rewrite -discrete_iff.
    naive_solver.
  - do 2 intros [[[[]|]|] [[[]|]|]]; simpl; try done;
      rewrite 2!prod_included; simpl; try naive_solver;
      try (rewrite !option_included; naive_solver).
    * intros. split; apply excl'_bot_top.
    * intros [? ?%excl'_bot_top_top].
      inversion H0.
      inversion H3.
  - intros ? [[[[]|]|] [[[]|]|]]; cbv; try naive_solver.
  - intros ?.
    do 2 intros [[[[]|]|] [[[]|]|]]; simpl; cbv; try done; try naive_solver.
Qed.

Record GenerationalCmra := {
    gencmra_cmra :> cmra;
    gencmra_gen :> cmra → Prop;
}.

Definition generational_cmra A : Type := option (agree (A → A)) * GTS * option A.

Definition generational_cmraR (A : cmra) :=
  prodR (prodR (optionR (agreeR (leibnizO (A → A)))) GTSR) (optionR A).

(* Ownership over generational ghost state. *)

Local Definition own_gen_def `{!inG Σ (generational_cmraR A)}
    (γ : gname) (a : A) : iProp Σ :=
  own γ (None, (None, None), Some a).
Local Definition own_gen_aux : seal (@own_gen_def). Proof. by eexists. Qed.
Definition own_gen := own_gen_aux.(unseal).
Global Arguments own_gen {Σ A _} γ a.
Local Definition own_gen_eq : @own_gen = @own_gen_def := own_gen_aux.(seal_eq).
Local Instance: Params (@own_gen) 4 := {}.

Definition own_tok `{!inG Σ (generational_cmraR A)} γ : iProp Σ :=
  own γ ((None, GTS_tok_both, None) : generational_cmraR A).

Definition own_pick `{!inG Σ (generational_cmraR A)} γ (f : A → A) : iProp Σ :=
  own γ ((Some (to_agree f), (None, None), None) : generational_cmraR A).

Definition gupd {Σ : gFunctors} P : iProp Σ :=
  (∃ (m : iResUR),
    ∀ fG (_ : Generation fG), ⚡={fG}=> P).

Lemma own_generational_update_tok `{!inG Σ (generational_cmraR A)} γ a f :
  .

Lemma own_generational_update_tok `{!inG Σ (generational_cmraR A)} γ a f :
  own_tok γ ∗ own_gen γ a ⊢ own_tok γ ∗ own_gen γ (f a) ∗ own_pick γ f.
