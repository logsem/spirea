From iris.algebra Require Import functions gmap agree excl.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own.
From iris.prelude Require Import options.
Import uPred.

(* The properties that the "generation", i.e., the function that transforms the
ghost state, needs to satisfy. Note that this is the "global" generation that
applies to the single unital camera. *)
Class Generation {M : ucmra} (f : M → M) := {
    generation_ne :> NonExpansive f;
    (* The function should be monotone with respect to the inclusion order of
    the monoid. *)
    generation_mono : ∀ x y, x ≼ y → f x ≼ f y;
    (* Validity is preserved. *)
    generation_valid : ∀ n (a : M), ✓{n} a → ✓{n} (f a);
    (* The generation comutes with the core. *)
    generation_core : ∀ (a : M), f (core a) = core (f a);
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

Class IntoBgupd `{M : ucmra} f `{!Generation f} (P : uPred M) (Q : uPred M) :=
  into_bgupd : P ⊢ ⚡={ f }=> Q.
Global Arguments IntoBgupd  {_} _%I _ _%I.
Global Arguments into_bgupd {_} _%I _%I {_}.
Global Hint Mode IntoBgupd + + + ! - : typeclass_instances.

Section bgupd_rules.

  Context {M : ucmra}.

  Context (f : M → M) `{!Generation f}.

  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  (* Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope. *)

  Local Arguments uPred_holds {_} !_ _ _ /.
  (* Local Hint Immediate uPred_in_entails : core. *)

  Ltac unseal := try uPred.unseal; rewrite !uPred_bgupd_unseal !/uPred_holds /=.

  Global Instance bgupd_ne : NonExpansive (uPred_bgupd f).
  Proof.
    unseal. intros ? P Q Heq.
    split.
    intros ????. simpl.
    split; intros ?; apply Heq; eauto using Heq, generation_valid.
  Qed.

  Lemma bgupd_ownM (a : M) :
    uPred_ownM a ⊢ ⚡={f}=> uPred_ownM (f a).
  Proof.
    unseal. split. simpl.
    intros n x Hv ?.
    apply generation_monoN; done.
  Qed.

  Lemma bgupd_and P Q :
    (⚡={f}=> P) ∧ (⚡={f}=> Q) ⊣⊢ ⚡={f}=> (P ∧ Q).
  Proof. unseal. split. simpl. done. Qed.

  Lemma bgupd_sep_2 P Q :
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

  Lemma bgupd_intro_plain P :
    ■ P ⊢ ⚡={f}=> ■ P.
  Proof. unseal. split. done. Qed.

  Lemma bgupd_plainly P :
    (⚡={f}=> ■ P) ⊢ P.
  Proof.
    unseal. split. simpl. intros ????. simpl.
    eauto using uPred_mono, ucmra_unit_leastN.
  Qed.

  Lemma bgupd_mono P Q :
    (P ⊢ Q) → (⚡={f}=> P) ⊢ ⚡={f}=> Q.
  Proof.
    intros [Hi].
    unseal. split. simpl.
    intros ???.
    apply Hi.
    apply generation_valid.
    done.
  Qed.

  Lemma bgupd_emp_2 : emp ⊢ ⚡={f}=> emp.
  Proof. unseal. done. Qed.

  Lemma bgupd_intuitinistically_2 P :
    <pers> (⚡={f}=> P) ⊢ ⚡={f}=> (<pers> P).
  Proof.
    unseal. split. simpl. intros ???.
    rewrite generation_core. done.
  Qed.

  Global Instance bgupd_mono' :
    Proper ((⊢) ==> (⊢)) (uPred_bgupd f).
  Proof. intros P Q. apply bgupd_mono. Qed.

  Global Instance bgupd_proper :
    Proper ((≡) ==> (≡)) (uPred_bgupd f) := ne_proper _.

  Lemma modality_bgupd_mixin :
    modality_mixin (@uPred_bgupd M f _)
      (MIEnvTransform (IntoBgupd f _)) (MIEnvTransform (IntoBgupd f _)).
  Proof.
    split; simpl; split_and?.
    - intros ?? Hi.
      rewrite Hi.
      rewrite 2!intuitionistically_into_persistently.
      apply bgupd_intuitinistically_2.
    - intros. rewrite bgupd_and. done.
    - done.
    - apply bgupd_emp_2.
    - apply bgupd_mono.
    - apply bgupd_sep_2.
  Qed.
  Definition modality_bgupd :=
    Modality _ modality_bgupd_mixin.

  Global Instance from_modal_objectively P :
    FromModal True modality_bgupd (⚡={f}=> P) (⚡={f}=> P) P | 1.
  Proof. by rewrite /FromModal. Qed.

End bgupd_rules.

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
  - intros [[[[]|]|] [[[]|]|]]; simpl; cbv; try done; try naive_solver.
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

Definition own_gen `{!inG Σ (generational_cmraR A)}
    (γ : gname) (a : A) : iProp Σ :=
  own γ (None, (None, None), Some a).

(* Local Definition own_gen_def `{!inG Σ (generational_cmraR A)} *)
(*     (γ : gname) (a : A) : iProp Σ := *)
(*   own γ (None, (None, None), Some a). *)
(* Local Definition own_gen_aux : seal (@own_gen_def). Proof. by eexists. Qed. *)
(* Definition own_gen := own_gen_aux.(unseal). *)
(* Global Arguments own_gen {Σ A _} γ a. *)
(* Local Definition own_gen_eq : @own_gen = @own_gen_def := own_gen_aux.(seal_eq). *)
(* Local Instance: Params (@own_gen) 4 := {}. *)

Definition own_tok `{!inG Σ (generational_cmraR A)} γ : iProp Σ :=
  own γ ((None, GTS_tok_both, None) : generational_cmraR A).

Lemma own_tok_split `{!inG Σ (generational_cmraR A)} γ :
  own_tok γ ⊣⊢
  own γ (None, GTS_tok_perm, None) ∗
  own γ (None, GTS_tok_gen, None).
Proof. rewrite -own_op. done. Qed.

Definition own_pick `{!inG Σ (generational_cmraR A)} γ (f : A → A) : iProp Σ :=
  own γ ((Some (to_agree f), (None, None), None) : generational_cmraR A).

(* The generation function for the encoding of each ownership over generational
camera. *)
Definition gen_generation {A : cmra} (f : A → A)
    (e : generational_cmra A) : generational_cmra A :=
  match e with
  | (_, tok, ma) => (Some (to_agree f), GTS_floor tok, f <$> ma)
  end.

Definition resp {Σ} (fG : iResUR Σ → _) `{!Generation fG}
    (fs : ∀ i, gmap gname
                ((rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ)) →
                 (rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ)))) :=
  ∀ (m : iResUR Σ) i γ a f,
    fs i !! γ = Some f →
    m i !! γ = Some a →
    (fG m) i !! γ = Some (f a).

Definition R Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ)).

Record foo Σ i := {
  foo_cmra : cmra;
  foo_eq : R Σ i = generational_cmraR foo_cmra;
  (* foo_map : gmap gname (foo_cmra → foo_cmra); *)
}.

Definition gupd {Σ} P : iProp Σ :=
  ∃ (f : ∀ i, gmap gname (R Σ i → R Σ i))
    (m : iResUR Σ),
    (* ⌜ ∀ i γ A a, R Σ i = generational_cmraR A ∧ f i !! γ = Some a ⌝ ∗ *)
    uPred_ownM m ∗
    ⌜ (∀ i (γ : gname) (a : rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ)),
        (m i) !! γ = Some a  →
        ∃ (A : _)
          (eq : rFunctor_apply (gFunctors_lookup Σ i) (iPropO Σ) = generational_cmraR A),
            cmra_transport eq ((rFunctor_map _ (iProp_unfold, iProp_fold)) a) = (None, GTS_tok_gen, None)) ⌝ ∗
    ∀ (fG : iResUR Σ → _) (_ : Generation fG), ⌜ resp fG f ⌝ → ⚡={fG}=> P.

Notation "⚡==> P" := (gupd P)
  (at level 99, P at level 200, format "⚡==>  P") : bi_scope.

  (* look : discrete_fun_singleton (inG_id i) *)
  (*          {[γ := own.inG_unfold (cmra_transport inG_prf a)]} i' !! γ' =  *)
  (*        Some b *)

Lemma iRes_singlon_lookup_inG_id `{i : !inG Σ A} (a : A) (γ γ' : gname)
    (b : rFunctor_apply (gFunctors_lookup Σ (inG_id i)) (iPrePropO Σ)) :
  (own.iRes_singleton γ a) (inG_id i) !! γ' = Some b →
  γ = γ' ∧ b = own.inG_unfold (cmra_transport inG_prf a).
Proof.
  rewrite /own.iRes_singleton.
  rewrite discrete_fun_lookup_singleton.
  rewrite lookup_singleton_Some.
  intros [??]. split; congruence.
Qed.

(* Lemma iRes_singleton_id_eq `{i : !inG Σ A} (a : A) i' (γ γ' : gname) *)
(*     (b : rFunctor_apply (gFunctors_lookup Σ i') (iPrePropO Σ)) *)
(*     (* (eq : inG_id i = i') : *) *)
(*     (* (eq : inG_id i = i') : *) *)
(*   (own.iRes_singleton γ a) i' !! γ' = Some b → *)
(*   (own.iRes_singleton γ a) (inG_id i) !! γ' = Some (cmra_transport eq b). *)
(*   (* (match eq in (_ = rr) return Prop  with *) *)
(*   (* | eq_refl => (own.iRes_singleton γ a) (inG_id i) !! γ' = Some b *) *)
(*   (* end) *) *)
(*   . *)

Lemma iRes_singleton_id_eq `{i : !inG Σ A} (a : A) i' (γ γ' : gname)
    (b : rFunctor_apply (gFunctors_lookup Σ i') (iPrePropO Σ)) :
  inG_id i = i' →
  (own.iRes_singleton γ a) i' !! γ' = Some b →
  ∃ (eq : rFunctor_apply (gFunctors_lookup Σ i') (iPrePropO Σ) =
          rFunctor_apply (gFunctors_lookup Σ (inG_id i)) (iPrePropO Σ)),
    (* (own.iRes_singleton γ a) (inG_id i) !! γ' = Some (cmra_transport eq b). *)
    (own.iRes_singleton γ a) (inG_id i) !! γ' = Some (cmra_transport eq b).
Proof.
  intros eq look.
  assert (
    rFunctor_apply (gFunctors_lookup Σ i') (iPrePropO Σ) (* type of [B] *)
    =
    rFunctor_apply (gFunctors_lookup Σ (inG_id i)) (iPrePropO Σ)
  ) as eq2 by congruence.
  exists eq2.
  destruct eq.
  rewrite look.
  f_equiv.
  (* eq_dep *)
  (* eq_dep1 *)
  (* rewrite eq eq2 in look. *)

  (*
  rewrite /discrete_fun_singleton in look.
  rewrite /discrete_fun_insert in look.
  pose proof (cmra_transport eq2 b).
  rewrite eq2 in look.

  Set Printing Implicit.
  pose proof
    (eq_rect i'
       (λ id,
         discrete_fun_singleton (inG_id i)
           {[γ := own.inG_unfold (cmra_transport inG_prf a)]} id !! γ' =
           Some (b))
           (* Some (b : rFunctor_apply (gFunctors_lookup Σ id) (iPrePropO Σ))) *)
           (* Some (cmra_transport eq2 b)) *)
       look
       _
       eq).
  simpl in H.

  rewrite e in look.
  rewrite discrete_fun_lookup_singleton.
  discrete_fun_lookup_singleton_ne.
*)
Admitted.

Lemma iRes_singleton_lookup `{i : !inG Σ A} γ γ' (a : A) i'
    (b : rFunctor_apply (gFunctors_lookup Σ i') (iPrePropO Σ)) :
  (own.iRes_singleton γ a) i' !! γ' = Some b →
  ∃ (eq : rFunctor_apply (gFunctors_lookup Σ i') (iPrePropO Σ) =
          rFunctor_apply (gFunctors_lookup Σ (inG_id i)) (iPrePropO Σ)),
    inG_id i = i' ∧
    γ = γ' ∧
    cmra_transport eq b = own.inG_unfold (cmra_transport inG_prf a)
  .
Proof.
  rewrite /own.iRes_singleton.
  destruct (decide (inG_id i = i')) as [eq|]; last first.
  { rewrite discrete_fun_lookup_singleton_ne //. }
  intros look.
  apply iRes_singleton_id_eq in look; try done.
  destruct look as [eq2 look].
  exists eq2.
  split; first done.
  apply iRes_singlon_lookup_inG_id in look as [-> ?].
  done.
Qed.

(** * Properties about generational ghost ownership. *)
Section own_properties.

  Context `{i : !inG Σ (generational_cmraR A)}.

  Implicit Types a : A.

  Lemma own_gen_alloc a : ✓ a → ⊢ |==> ∃ γ, own_gen γ a ∗ own_tok γ.
  Proof.
    intros Hv.
    iApply bupd_mono; last first.
    { iApply (own_alloc (None, GTS_tok_both, Some a)). done. }
    iIntros "[%γ H]".
    iExists (γ).
    rewrite -own_op.
    iApply "H".
  Qed.

  Lemma own_generational_update_tok γ a f :
    own_tok γ ∗ own_gen γ a ⊢ ⚡==> own_tok γ ∗ own_gen γ (f a) ∗ own_pick γ f.
  Proof.
    iIntros "[tok gen]".
    iDestruct (own_tok_split with "tok") as "[tok1 tok2]".
    rewrite /gupd.
    pose proof (@inG_prf _ _ i) as eq.
    simpl in eq.
    rewrite /inG_apply in eq.

    iExists (
      λ j, if decide (j = inG_id i) then {[ γ := gen_generation f ]} else ∅
    ).

    iExists (own.iRes_singleton γ (None, GTS_tok_gen, None)).
    (* iExists ( *)
    (*   discrete_fun_singleton (inG_id i : fin (gFunctors_len Σ)) *)
    (*     {[ γ := (None, GTS_tok_gen, None) ]} *)
    (* ). *)
    iEval (rewrite own.own_eq) in "tok2".
    iFrame "tok2".

    iSplit.
    - iPureIntro. intros i' γ' b.
      intros look.
      apply iRes_singleton_lookup in look as (eq' & iEq & gEq & ho).

      exists A.
      symmetry in eq.
      rewrite iEq in eq.
      eexists eq.
  Admitted.
  (*     rewrite -iEq. *)

  (*     rewrite ho. *)
  (*     Unshelve. *)
  (*     3: { *)
  (*       app *)
  (*       simpl. *)
  (*       rewrite (inG_prf (A := generational_cmraR A)). *)
  (*       rewrite /inG_apply. *)
  (*       done. *)


  (*   (* TODO *) *)
  (* Admitted. *)

End own_properties.
