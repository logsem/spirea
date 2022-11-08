From iris.algebra Require Import functions gmap agree excl.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own.
From iris.prelude Require Import options.

From self Require Import extra.
Import uPred.

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
(* Lemma gen_trans_monotoneN *)

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

(** When working in the model, it is convenient to be able to treat [uPred] as
[nat → M → Prop]. But we only want to locally break the [uPred] abstraction
this way. *)
Local Coercion uPred_holds : uPred >-> Funclass.

Local Program Definition uPred_bgupd_def {M : ucmra}
  (f : M → M) `{!GenTrans f} (P : uPred M) : uPred M :=
  {| uPred_holds n x := P n (f x) |}.
Next Obligation. naive_solver eauto using uPred_mono, generation_monoN. Qed.

Local Definition uPred_bgupd_aux : seal (@uPred_bgupd_def).
Proof. by eexists. Qed.

Definition uPred_bgupd {M : ucmra} f `{g : !GenTrans f} := uPred_bgupd_aux.(unseal) M f g.

Local Definition uPred_bgupd_unseal :
  @uPred_bgupd = @uPred_bgupd_def := uPred_bgupd_aux.(seal_eq).

Notation "⚡={ f }=> P" := (uPred_bgupd f P)
  (at level 99, f at level 50, P at level 200, format "⚡={ f }=>  P") : bi_scope.

Class IntoBgupd `{M : ucmra} f `{!GenTrans f} (P : uPred M) (Q : uPred M) :=
  into_bgupd : P ⊢ ⚡={ f }=> Q.
Global Arguments IntoBgupd  {_} _%I {_} _%I _%I.
Global Arguments into_bgupd {_} _%I _%I {_}.
Global Hint Mode IntoBgupd + + + ! - : typeclass_instances.

Section bgupd_rules.
  Context {M : ucmra} (f : M → M) `{!GenTrans f}.

  Notation "P ⊢ Q" := (@uPred_entails M P%I Q%I) : stdpp_scope.
  Notation "⊢ Q" := (bi_entails (PROP:=uPredI M) True Q).
  Notation "(⊢)" := (@uPred_entails M) (only parsing) : stdpp_scope.

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
    rewrite -(generation_op _ a b).
    rewrite eq. done.
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
    pose proof (generation_pcore x) as eq.
    rewrite 2!cmra_pcore_core in eq.
    apply Some_equiv_inj in eq.
    rewrite eq.
    done.
  Qed.

  Global Instance bgupd_mono' :
    Proper ((⊢) ==> (⊢)) (uPred_bgupd f).
  Proof. intros P Q. apply bgupd_mono. Qed.

  Global Instance bgupd_proper :
    Proper ((≡) ==> (≡)) (uPred_bgupd f) := ne_proper _.

  Lemma modality_bgupd_mixin :
    modality_mixin (@uPred_bgupd M f _)
      (MIEnvTransform (IntoBgupd f)) (MIEnvTransform (IntoBgupd f)).
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

  Lemma bgupd_later P :
    ▷ (⚡={f}=> P) ⊣⊢ ⚡={f}=> (▷ P).
  Proof. unseal. done. Qed.

  Lemma bgupd_exist {A} Ψ :
    (⚡={f}=> (∃ a : A, Ψ a)) ⊣⊢ (∃ a : A, ⚡={f}=> Ψ a).
  Proof. unseal. done. Qed.

  Lemma bgupd_forall {A} Ψ :
    (⚡={f}=> (∀ a : A, Ψ a)) ⊣⊢ (∀ a : A, ⚡={f}=> Ψ a).
  Proof. unseal. done. Qed.

  Lemma bgupd_plain P `{!Plain P} :
    (⚡={f}=> P) ⊢ P.
  Proof. rewrite {1}(plain P). apply bgupd_plainly. Qed.

End bgupd_rules.

Lemma bgupd_plain_soundness {M : ucmra} f `{!GenTrans f} (P : uPred M) `{!Plain P} :
  (⊢ ⚡={f}=> P) → ⊢ P.
Proof.
  eapply bi_emp_valid_mono. etrans; last exact: bgupd_plainly.
  apply bgupd_mono'. apply: plain.
Qed.

Section into_bgupd.
  Context {M : ucmra} (f : M → M) `{!GenTrans f}.

  Global Instance into_bgupd_ownM a :
    IntoBgupd f (uPred_ownM a) (uPred_ownM (f a)) := bgupd_ownM f a.

  Global Instance into_bgupd_later P P' :
    IntoBgupd f P P' → IntoBgupd f (▷ P) (▷ P').
  Proof. rewrite /IntoBgupd. rewrite -bgupd_later. intros ->. done. Qed.

  Global Instance into_bgupd_forall {A} (Ψ Ψ' : A → _) :
    (∀ x, IntoBgupd f (Ψ x) (Ψ' x)) → IntoBgupd f (∀ x, Ψ x) (∀ x, Ψ' x).
  Proof.
    rewrite /IntoBgupd bgupd_forall.
    iIntros (H) "Hi". iIntros (?).
    iApply H.
    iApply "Hi".
  Qed.

  Global Instance into_bgupd_exist {A} (Ψ Ψ' : A → _) :
    (∀ x : A, IntoBgupd f (Ψ x) (Ψ' x)) → IntoBgupd f (∃ x : A, Ψ x) (∃ x : A, Ψ' x).
  Proof.
    rewrite /IntoBgupd bgupd_exist.
    iIntros (H). iIntros "(%x & Hi)". iExists x.
    iApply H.
    iApply "Hi".
  Qed.

End into_bgupd.

(******************************************************************************)
(* Generational token stream.

   The generational token stream makes it possible to own a "permanent"
   exclusive token that is preserved across generations. For each generation the
   "permanent" token also "produces" a per-generation token that is only valid
   for the current generation.  *)

Definition GTS : Type := excl' () * excl' ().
Definition GTSR : cmra :=
  prodR (optionR (exclR unitO)) (optionR (exclR unitO)).

(** The per-generation token. *)
Definition GTS_tok_gen : GTS := (None, Excl' ()).
(** The permanent cross-generation token. *)
Definition GTS_tok_perm : GTS := (Excl' (), None).
(** Both tokens. *)
Definition GTS_tok_both : GTS := (Excl' (), Excl' ()).

Definition GTS_floor (a : GTS) : GTS :=
  (* The cross-generation permanent token is preserved and also produces the
  per-generation token. *)
  match a with (a, _) => (a, a) end.

Global Instance GTS_floor_generation : GenTrans GTS_floor.
Proof.
  split.
  - intros ???.
    rewrite -discrete_iff.
    naive_solver.
  - intros ? [[[[]|]|] [[[]|]|]]; cbv; try naive_solver.
  - intros [[[[]|]|] [[[]|]|]]; done.
  - do 2 intros [[[[]|]|] [[[]|]|]]; try done.
Qed.

Section gts.

  Lemma GTS_floor_perm : GTS_floor (GTS_tok_perm) = GTS_tok_perm ⋅ GTS_tok_gen.
  Proof. reflexivity. Qed.

  Lemma GTS_floor_gen : GTS_floor (GTS_tok_gen) = (None, None).
  Proof. reflexivity. Qed.

End gts.

Definition generational_cmra A : Type :=
  option (agree (A → A)) * GTS * option A.

Definition generational_cmraR (A : cmra) :=
  prodR (prodR (optionR (agreeR (leibnizO (A → A)))) GTSR) (optionR A).

(* Ownership over generational ghost state. *)

Definition gen_own `{!inG Σ (generational_cmraR A)}
    (γ : gname) (a : A) : iProp Σ :=
  own γ (None, (None, None), Some a).

(* Local Definition own_gen_def `{!inG Σ (generational_cmraR A)} *)
(*     (γ : gname) (a : A) : iProp Σ := *)
(*   own γ (None, (None, None), Some a). *)
(* Local Definition own_gen_aux : seal (@own_gen_def). Proof. by eexists. Qed. *)
(* Definition gen_own := own_gen_aux.(unseal). *)
(* Global Arguments gen_own {Σ A _} γ a. *)
(* Local Definition own_gen_eq : @gen_own = @own_gen_def := own_gen_aux.(seal_eq). *)
(* Local Instance: Params (@gen_own 4 := {}. *)

Definition gen_token `{!inG Σ (generational_cmraR A)} γ : iProp Σ :=
  own γ ((None, GTS_tok_both, None) : generational_cmraR A).

Lemma gen_token_split `{!inG Σ (generational_cmraR A)} γ :
  gen_token γ ⊣⊢
  own γ (None, GTS_tok_perm, None) ∗
  own γ (None, GTS_tok_gen, None).
Proof. rewrite -own_op. done. Qed.

Definition gen_pick `{!inG Σ (generational_cmraR A)} γ (f : A → A) : iProp Σ :=
  own γ ((Some (to_agree f), (None, None), None) : generational_cmraR A).

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

Definition gen_generation_first {A : cmra} (f : A → A) :
  prodR (optionR (agreeR (leibnizO (A → A)))) GTSR →
  prodR (optionR (agreeR (leibnizO (A → A)))) GTSR
  := prod_map
       (const (Some (to_agree f)) : optionR (agreeR (leibnizO (A → A))) → optionR (agreeR (leibnizO (A → A))))
       (GTS_floor : GTSR → GTSR).

(* The generational transformation function for the encoding of each ownership
over a generational camera. *)
Definition gen_generation {A : cmra}
    (f : A → A) : generational_cmraR A → generational_cmraR A :=
  prod_map (gen_generation_first f) (fmap f : optionR A → optionR A).
  (* match e with *)
  (* | (_, tok, ma) => (Some (to_agree f), GTS_floor tok, f <$> ma) *)
  (* end. *)

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

Global Instance gen_trans_const {A : ofe} (a : A) :
  GenTrans (const (Some (to_agree a))).
Proof.
  split; first apply _.
  - done.
  - intros. simpl. rewrite (core_id). done.
  - intros ??. simpl.
    rewrite -Some_op.
    rewrite agree_idemp.
    done.
Qed.

Global Instance gen_generation_gen_trans {A : cmra} (f : A → A)
  `{!Proper (equiv ==> equiv) f} :
  GenTrans f → GenTrans (gen_generation f).
Proof. apply _. Qed.

Global Instance gen_generation_proper {A : cmra} (f : A → A) :
  Proper ((≡) ==> (≡)) f →
  Proper ((≡) ==> (≡)) (gen_generation f).
Proof.
  intros ? [[??]?] [[??]?] [[??]?]. simpl in *.
  rewrite /gen_generation /gen_generation_first.
  solve_proper.
Qed.

(* The functor in [Σ] at index [i] applied to [iProp]. *)
Notation R Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPropO Σ)).
(* The functor in [Σ] at index [i] applied to [iPreProp]. *)
Notation Rpre Σ i := (rFunctor_apply (gFunctors_lookup Σ i) (iPrePropO Σ)).

Local Definition map_unfold {Σ} {i : gid Σ} : R Σ i -n> Rpre Σ i :=
  rFunctor_map _ (iProp_fold, iProp_unfold).
Local Definition map_fold {Σ} {i : gid Σ} : Rpre Σ i -n> R Σ i :=
  rFunctor_map _ (iProp_unfold, iProp_fold).

Definition cmra_map_transport {A B : cmra} (Heq : A = B) (f : A → A) : (B → B) :=
  eq_rect A (λ T, T → T) f _ Heq.

Lemma cmra_map_transport_cmra_transport {A B : cmra} (f : A → A) a (Heq : A = B) :
  (cmra_map_transport Heq f) (cmra_transport Heq a) =
  (cmra_transport Heq (f a)).
Proof. destruct Heq. simpl. reflexivity. Qed.

Global Instance cmra_map_transport_proper {A B : cmra} (f : A → A) (Heq : A = B) :
  (Proper ((≡) ==> (≡)) f) →
  (Proper ((≡) ==> (≡)) (cmra_map_transport Heq f)).
Proof. naive_solver. Qed.

(* Data for generational transformation for a camera. *)
(* A predicate over functions. *)
Record gen_trans (A : cmra) := {
  (* The condition that defines the set set op allowed transformations. *)
  gt_condition : (A → A) → Prop;
  (* A witness that at least one function satisfies the conditions. *)
  gt_inhabited : A → A;
  (* The witness satisfied the conditions. *)
  gt_inhabited_condition : gt_condition (gt_inhabited);
  gt_inhabited_gen_trans : GenTrans (gt_inhabited);
}.

Arguments gt_condition {_} _.
Arguments gt_inhabited {_}.
Arguments gt_inhabited_condition {_}.

Existing Instance gt_inhabited_gen_trans.

Program Definition lift {A} (g : gen_trans A) :
  gen_trans (generational_cmraR A) := {|
    gt_condition t := ∃ t_i,
      t = gen_generation t_i ∧ g.(gt_condition) t_i;
    gt_inhabited := gen_generation g.(gt_inhabited)
  |}.
Next Obligation.
  intros ??. simpl.
  eexists _. split; first done.
  apply g.(gt_inhabited_condition).
Qed.

Class gTransforms {Σ : gFunctors} := {
  g_trans : ∀ (i : gid Σ), option (gen_trans (R Σ i))
}.

#[export] Hint Mode gTransforms +.

Definition gen_transport {A B : cmra} (eq : A = B) (g : gen_trans A) : gen_trans B :=
  eq_rect A gen_trans g B eq.

(* The global functor [Σ] contains the camera [A] and the global generational
transformation [Ω] respects [g]. *)
Class genInG (Σ : gFunctors) (Ω : gTransforms) (A : cmra) (g : gen_trans A)
    := GenInG {
  genInG_inG : inG Σ (generational_cmraR A);
  genInG_gen_trans :
    Ω.(g_trans) (inG_id genInG_inG) =
      Some (gen_transport (@inG_prf _ _ genInG_inG) (lift g))
}.

Existing Instance genInG_inG.

(** [Picks] contains transformation functions for a subset of ghost names. It is
the entries that we have picked generational transformation for. *)
Definition Picks Σ : Type := ∀ i, gmap gname (R Σ i → R Σ i).

(** Every pick in [picks] is a valid generational transformation. *)
Definition picks_gen_trans {Σ} (picks : Picks Σ) :=
  ∀ i γ t, picks i !! γ = Some t → GenTrans t.

(* Every pick in [picks] satisfies the conditions for that cmra in [Ω]. *)
Definition picks_satisfy_cond {Σ} (Ω : gTransforms) (picks : Picks Σ) :=
  ∀ i γ t, picks i !! γ = Some t →
    ∃ gt, Ω.(g_trans) i = Some gt ∧ gt.(gt_condition) t.

Lemma picks_valid_empty {Σ} Ω :
  picks_satisfy_cond Ω (λ i : fin (gFunctors_len Σ), ∅).
Proof. intros ???. rewrite lookup_empty. inversion 1. Qed.

(* The functor [fG] respects the conditions in [Ω] and the entries in
[picks]. *)
Definition fG_resp {Σ} (fG : iResUR Σ → iResUR Σ) Ω(picks : Picks Σ) :=
  ∀ (m : iResUR Σ) i γ a gt,
    m i !! γ = Some a → (* For every element in the old element. *)
    Ω i = Some gt → (* Where we have transformation conditions. *)
    ∃ t, (* There exists a transformation. *)
      Proper ((≡) ==> (≡)) t ∧
      (fG m) i !! γ = Some (map_unfold (t (map_fold a))) ∧
      gt.(gt_condition) t ∧
      (∀ t', picks i !! γ = Some t' → t = t').

Definition m_contains_tokens_for_picks {Σ} (picks : Picks Σ) (m : iResUR Σ) :=
  ∀ i,
    dom (picks i) ≡ dom (m i) ∧
    (∀ (γ : gname) (a : Rpre Σ i),
      m i !! γ = Some a  →
      ∃ (A : _) (eq : generational_cmraR A = R Σ i),
        (map_fold a) ≡
        (cmra_transport eq (None, GTS_tok_gen, None))).

Definition gupd {Σ : gFunctors} {Ω : gTransforms} P : iProp Σ :=
  ∃ (picks : Picks Σ) (m : iResUR Σ),
    ⌜ picks_satisfy_cond Ω picks ⌝ ∗
    ⌜ picks_gen_trans picks ⌝ ∗
    uPred_ownM m ∗ ⌜ m_contains_tokens_for_picks picks m ⌝ ∗
    ∀ (fG : iResUR Σ → _) (_ : GenTrans fG),
      ⌜ fG_resp fG Ω.(g_trans) picks ⌝ →
      ⚡={fG}=> P.

Notation "⚡==> P" := (gupd P)
  (at level 99, P at level 200, format "⚡==>  P") : bi_scope.

Lemma uPred_own_resp `{i : !genInG Σ Ω A tr} fG `{!GenTrans fG} picks
  (f : generational_cmraR A → _) γ a `{!Proper ((≡) ==> (≡)) f} :
  fG_resp (Σ := Σ) fG Ω.(g_trans) picks →
  picks (inG_id _) !! γ = Some (cmra_map_transport inG_prf f) →
  uPred_ownM (fG (own.iRes_singleton γ a))
  ⊢ uPred_ownM ((own.iRes_singleton γ (f a))).
Proof.
  iIntros (Hresp Hlook).
  rewrite /own.iRes_singleton.
  rewrite /fG_resp in Hresp.
  eassert (_) as HI.
  { eapply (
      Hresp (discrete_fun_singleton (inG_id _)
              {[γ := own.inG_unfold (cmra_transport inG_prf a)]})
          (inG_id genInG_inG)
          γ
          (own.inG_unfold (cmra_transport inG_prf a))
          (gen_transport inG_prf (lift tr))
      ).
    - rewrite discrete_fun_lookup_singleton.
      rewrite lookup_singleton.
      done.
    - apply genInG_gen_trans. }
  destruct HI as (t & proper & fGLook & ? & lookEq).
  apply lookEq in Hlook as ->.
  f_equiv. simpl.
  apply discrete_fun_included_spec.
  intros idx'.
  destruct (decide ((inG_id genInG_inG) = idx')) as [<-|neq]; last first.
  { rewrite discrete_fun_lookup_singleton_ne; try done.
    apply ucmra_unit_least. }
  rewrite discrete_fun_lookup_singleton.
  apply singleton_included_l.
  exists (own.inG_unfold (cmra_transport inG_prf (f a))).
  split; last done.
  rewrite fGLook.
  f_equiv.
  f_equiv.
  rewrite own.inG_fold_unfold.
  rewrite cmra_map_transport_cmra_transport.
  done.
Qed.

Lemma cmra_transport_map_transport {A B} (eq : A = B) t a :
  cmra_transport eq (cmra_map_transport (eq_sym eq) t a) =
  t (cmra_transport eq a).
Proof. destruct eq. simpl. done. Qed.

Lemma gt_conditions_transport {A B} (eq : generational_cmraR A = B) tr t :
  gt_condition (gen_transport eq (lift tr)) t =
  gt_condition (lift tr) (cmra_map_transport (eq_sym eq) t).
Proof. destruct eq. done. Qed.

Lemma uPred_own_resp_omega `{i : !genInG Σ Ω A tr} fG `{!GenTrans fG} picks γ
    (a : generational_cmraR A) :
  fG_resp (Σ := Σ) fG Ω.(g_trans) picks →
  uPred_ownM (fG (own.iRes_singleton γ a))
  ⊢ ∃ (t : generational_cmraR A → generational_cmraR A),
      ⌜ gt_condition (lift tr) t ⌝ ∗
      uPred_ownM ((own.iRes_singleton γ (t a))).
Proof.
  iIntros (Hresp).
  rewrite /own.iRes_singleton.
  rewrite /fG_resp in Hresp.
  eassert (_) as HI.
  { eapply (
      Hresp (discrete_fun_singleton (inG_id _)
              {[γ := own.inG_unfold (cmra_transport inG_prf a)]})
          (inG_id genInG_inG)
          γ
          (own.inG_unfold (cmra_transport inG_prf a))
          (gen_transport inG_prf (lift tr))
      ).
    - rewrite discrete_fun_lookup_singleton.
      rewrite lookup_singleton.
      done.
    - apply genInG_gen_trans. }
  destruct HI as (t & proper & fGLook & ? & lookEq).
  set (eq_sym (@inG_prf _ _ (genInG_inG))) as eq.
  iIntros "HR".
  iExists (cmra_map_transport eq t).
  iSplit.
  { iPureIntro.
    rewrite -gt_conditions_transport.
    assumption. }
  iStopProof.
  f_equiv.
  simpl.
  apply discrete_fun_included_spec.
  intros idx'.

  destruct (decide ((inG_id genInG_inG) = idx')) as [<-|neq]; last first.
  { rewrite discrete_fun_lookup_singleton_ne; try done.
    apply ucmra_unit_least. }
  rewrite discrete_fun_lookup_singleton.
  apply singleton_included_l.
  eexists _.
  split; last done.
  rewrite fGLook.
  f_equiv.
  f_equiv.
  rewrite cmra_transport_map_transport.
  rewrite /map_fold -/own.inG_fold.
  rewrite own.inG_fold_unfold.
  done.
Qed.

Lemma iRes_singleton_lookup_inG_id `{i : !inG Σ A} (a : A) (γ γ' : gname)
    (b : Rpre Σ (inG_id i)) :
  (own.iRes_singleton γ a) (inG_id i) !! γ' = Some b →
  γ = γ' ∧ b = own.inG_unfold (cmra_transport inG_prf a).
Proof.
  rewrite /own.iRes_singleton.
  rewrite discrete_fun_lookup_singleton.
  rewrite lookup_singleton_Some.
  intros [??]. split; congruence.
Qed.

Lemma iRes_singleton_lookup `{i : !inG Σ A} γ γ' (a : A) i'
    (b : Rpre Σ i') :
  (own.iRes_singleton γ a) i' !! γ' = Some b →
  ∃ (eq : i' = inG_id i),
    γ = γ' ∧
      own.inG_unfold (cmra_transport inG_prf a) =
        match eq in (_ = r) return rFunctor_apply (gFunctors_lookup Σ r) (iPrePropO Σ) with
        | eq_refl => b
        end.
Proof.
  rewrite /own.iRes_singleton.
  destruct (decide (inG_id i = i')) as [eq|]; last first.
  { rewrite discrete_fun_lookup_singleton_ne //. }
  intros look.
  destruct eq.
  apply iRes_singleton_lookup_inG_id in look as [-> ->].
  exists eq_refl.
  done.
Qed.

Lemma iRes_singleton_lookup_alt `{i : !inG Σ A} γ γ' (a : A) i' (b : Rpre Σ i') :
  (own.iRes_singleton γ a) i' !! γ' = Some b →
  ∃ (eq : inG_id i = i'),
    γ = γ' ∧
      match eq in (_ = r) return Rpre Σ r with
      | eq_refl => own.inG_unfold (cmra_transport inG_prf a)
      end = b.
Proof.
  rewrite /own.iRes_singleton.
  destruct (decide (inG_id i = i')) as [eq|]; last first.
  { rewrite discrete_fun_lookup_singleton_ne //. }
  intros look.
  destruct eq.
  apply iRes_singleton_lookup_inG_id in look as [-> ->].
  exists eq_refl.
  done.
Qed.

(** A map of picks that for the resource at [idx] and the ghost name [γ] picks
the generational transformation [t]. *)
Definition pick_singleton {Σ} idx (γ : gname)
    (t : R Σ idx → R Σ idx) : Picks Σ :=
  λ j, match decide (idx = j) with
         left Heq =>
           (eq_rect _ (λ i, gmap gname (R Σ i → _)) {[ γ := t ]} _ Heq)
       | right _ => ∅
       end.

Section pick_singleton_lemmas.
  Context {Σ : gFunctors} (idx : gid Σ).

  Implicit Types (f : R Σ idx → R Σ idx).

  Definition pick_singleton_lookup γ (f : R Σ idx → R Σ idx) :
    pick_singleton idx γ f idx !! γ = Some f.
  Proof.
    rewrite /pick_singleton.
    case (decide (idx = idx)); last by congruence.
    intros eq'.
    assert (eq' = eq_refl) as ->.
    { rewrite (proof_irrel eq' eq_refl). done. }
    simpl.
    apply lookup_singleton.
  Qed.

  Definition pick_singleton_dom_index_eq γ f :
    dom (pick_singleton idx γ f idx) = {[ γ ]}.
  Proof.
    rewrite /pick_singleton.
    case (decide (idx = idx)); last congruence.
    intros [].
    simpl.
    apply dom_singleton_L.
  Qed.

  Definition pick_singleton_dom_index_neq γ f idx' :
    idx ≠ idx' →
    dom (pick_singleton idx γ f idx') = ∅.
  Proof.
    intros neq.
    rewrite /pick_singleton.
    case (decide (idx = idx')); first congruence.
    intros ?.
    apply dom_empty_L.
  Qed.

  Definition gen_f_singleton_lookup_Some idx' γ γ' f (f' : R Σ idx' → R Σ idx'):
    (pick_singleton idx γ f) idx' !! γ' = Some f' →
    ∃ (eq : idx' = idx),
      γ = γ' ∧
      f = match eq in (_ = r) return (R Σ r → R Σ r) with eq_refl => f' end.
  Proof.
    rewrite /pick_singleton.
    case (decide (idx = idx')); last first.
    { intros ?. rewrite lookup_empty. inversion 1. }
    intros ->.
    simpl.
    intros [-> ->]%lookup_singleton_Some.
    exists eq_refl.
    done.
  Qed.

  Lemma picks_singleton_gen_trans γ f :
    GenTrans f → picks_gen_trans (pick_singleton idx γ f).
  Proof.
    intros fGT idx' γ' f' (-> & -> & ->)%gen_f_singleton_lookup_Some. done.
  Qed.

  Lemma picks_gen_trans_empty :
    picks_gen_trans ((λ i : fin (gFunctors_len Σ), ∅)).
  Proof. intros ??? [=]. Qed.

End pick_singleton_lemmas.

Lemma pick_singleton_iRes_singleton_dom `{i : !inG Σ A}
    γ (a : A) i' (t : R Σ (inG_id i) → R Σ _) :
  dom (pick_singleton (inG_id _) γ t i') ≡ dom (own.iRes_singleton γ a i').
Proof.
  rewrite /pick_singleton.
  rewrite /own.iRes_singleton.
  destruct (decide (i' = inG_id i)) as [->|].
  - rewrite discrete_fun_lookup_singleton.
    rewrite dom_singleton.
    rewrite pick_singleton_dom_index_eq //.
  - rewrite pick_singleton_dom_index_neq //.
    rewrite discrete_fun_lookup_singleton_ne //.
Qed.

(* Build a global generational transformation based on the picks in [f] and the
constraints made by [Ω]. *)
Definition build_trans {Σ} (Ω : @gTransforms Σ) (picks : Picks Σ) :
    (iResUR Σ → iResUR Σ) :=
  λ (m : iResUR Σ) (i : gid Σ),
    map_imap (λ γ a,
      (* 1/ Lookup in the partial map of picks. *)
      (* 2/ Lookup in omega and pick the inhabited witness. *)
      (* 3/ Else, return none. *)
      match picks i !! γ with
      | Some fl => Some $ map_unfold $ fl $ map_fold a
      | None =>
          match Ω.(g_trans) i with
          | None => None
          | Some gt =>
              Some $ map_unfold $ gt.(gt_inhabited) $ map_fold a
          end
      end
    ) (m i).

Section build_trans.
  Context {Σ : gFunctors}.
  Implicit Types (picks : Picks Σ).

  Lemma core_Some_pcore {A : cmra} (a : A) : core (Some a) = pcore a.
  Proof. done. Qed.

  Lemma build_trans_generation Ω picks :
    picks_gen_trans picks → GenTrans (build_trans Ω picks).
  Proof.
    (* NOTE: this proof is _very_ brute-forcey. One could try and shorten it. *)
    intros picksGT.
    rewrite /build_trans.
    split.
    - rewrite /Proper.
      intros ??? eq i γ.
      rewrite 2!map_lookup_imap.
      specialize (eq i γ).
      destruct eq as [a b eq|]; simpl; last done.
      destruct (picks i !! γ) eqn:look.
      * apply picksGT in look. solve_proper.
      * solve_proper.
    - intros ?? Hval.
      intros i γ.
      rewrite !map_lookup_imap. simpl.
      specialize (Hval i γ).
      destruct (a i !! γ) eqn:eq; rewrite eq /=; last done.
      rewrite eq in Hval.
      destruct (picks i !! γ) as [pick|] eqn:eq2.
      * apply Some_validN.
        apply: cmra_morphism_validN.
        apply Some_validN.
        specialize (picksGT i γ pick eq2) as ?.
        apply generation_valid.
        apply: cmra_morphism_validN.
        apply Hval.
      * destruct (g_trans i); last done.
        apply Some_validN.
        apply: cmra_morphism_validN.
        apply generation_valid.
        apply: cmra_morphism_validN.
        apply Hval.
    - move=> m /=.
      rewrite cmra_pcore_core.
      simpl.
      f_equiv.
      intros i γ.
      rewrite lookup_core.
      rewrite 2!map_lookup_imap.
      rewrite lookup_core.
      destruct (m i !! γ) as [a|] eqn:look; rewrite look; simpl; last done.
      simpl.
      rewrite core_Some_pcore.
      destruct (picks i !! γ) as [pick|] eqn:pickLook; simpl.
      * rewrite core_Some_pcore.
        rewrite -cmra_morphism_pcore.
        specialize (picksGT i γ pick pickLook) as ?.
        rewrite -generation_pcore.
        rewrite -cmra_morphism_pcore.
        destruct (pcore a); done.
      * destruct (g_trans i).
        + rewrite core_Some_pcore.
          rewrite -cmra_morphism_pcore.
          rewrite -generation_pcore.
          rewrite -cmra_morphism_pcore.
          destruct (pcore a); done.
        + destruct (pcore a); done.
    - intros m1 m2.
      intros i γ.
      rewrite 2!discrete_fun_lookup_op.
      rewrite !map_lookup_imap.
      rewrite 2!lookup_op.
      rewrite !map_lookup_imap.
      destruct (picks i !! γ) as [pick|] eqn:pickLook.
      * specialize (picksGT i γ pick pickLook) as ?.
        destruct (m1 i !! γ) eqn:eq1; destruct (m2 i !! γ) eqn:eq2;
          rewrite eq1 eq2; simpl; try done.
        rewrite -Some_op.
        rewrite -cmra_morphism_op.
        rewrite -generation_op.
        rewrite -cmra_morphism_op.
        done.
      * destruct (g_trans i);
          destruct (m1 i !! γ) eqn:eq1;
          destruct (m2 i !! γ) eqn:eq2;
            rewrite eq1 eq2; simpl; try done.
        rewrite -Some_op.
        rewrite -cmra_morphism_op.
        rewrite -generation_op.
        rewrite -cmra_morphism_op.
        done.
  Qed.

  Lemma build_trans_resp Ω picks :
    picks_gen_trans picks →
    picks_satisfy_cond Ω picks →
    fG_resp (build_trans Ω picks) Ω.(g_trans) picks.
  Proof.
    rewrite /fG_resp /build_trans.
    intros picksGT sat ???????.
    destruct (picks i !! γ) as [pick|] eqn:eq.
    - exists pick.
      specialize (sat i γ pick eq) as (gt' & ? & ?).
      specialize (picksGT i γ pick eq) as ?.
      assert (gt = gt') as <- by congruence.
      rewrite map_lookup_imap. rewrite H. simpl.
      split; first apply _.
      rewrite eq.
      split; first done.
      split; first done.
      move=> ? [= ->] //.
    - exists (gt_inhabited gt).
      split; first apply _.
      rewrite map_lookup_imap. rewrite H. simpl.
      rewrite eq H0.
      split; first done.
      split; first apply gt_inhabited_condition.
      intros ? [=].
  Qed.

End build_trans.

Global Instance gen_trans_cmra_map_transport {A B : cmra} (eq : A = B)
    (f : A → A) :
  GenTrans f → GenTrans (cmra_map_transport eq f).
Proof. destruct eq. done. Qed.

Lemma m_contains_tokens_for_picks_singleton `{i : inG Σ (generational_cmraR A)}
    γ t :
  m_contains_tokens_for_picks
    (pick_singleton (inG_id _) γ (cmra_map_transport inG_prf (gen_generation t)))
    (own.iRes_singleton γ (None, GTS_tok_gen, None)).
Proof.
  intros i'.
  split.
  { apply pick_singleton_iRes_singleton_dom. }
  (* We how show that the resource contains the tokens as it should. *)
  intros γ' b.
  intros look.
  apply iRes_singleton_lookup_alt in look as (iEq & -> & bEq).
  exists A.
  assert (rFunctor_apply (gFunctors_lookup Σ i') (iPrePropO Σ) =
            rFunctor_apply (gFunctors_lookup Σ (inG_id i)) (iPrePropO Σ)).
  { rewrite iEq. done. }
  destruct iEq.
  pose proof (@inG_prf _ _ i) as eq'.
  rewrite /inG_apply in eq'.
  eexists (@inG_prf _ _ i).
  rewrite <- bEq.
  rewrite -/(@own.inG_fold _ _ i).
  apply own.inG_fold_unfold.
Qed.

(* (** * Properties about generational ghost ownership. *) *)
Section own_properties.

  Context `{i : !genInG Σ Ω A transA}.

  Implicit Types a : A.

  (* Allocating new ghost state results in both generational ownership over the
  allocated element and owneship ovevr the token. *)
  Lemma own_gen_alloc a : ✓ a → ⊢ |==> ∃ γ, gen_own γ a ∗ gen_token γ.
  Proof.
    intros Hv.
    iApply bupd_mono; last first.
    { iApply (own_alloc (None, GTS_tok_both, Some a)). done. }
    iIntros "[%γ H]".
    iExists (γ).
    rewrite -own_op.
    iApply "H".
  Qed.

  Lemma gt_condition_transport f :
    gt_condition (lift transA) (gen_generation f) →
    gt_condition (gen_transport inG_prf (lift transA))
      (cmra_map_transport inG_prf (gen_generation f)).
  Proof. destruct inG_prf. simpl. done. Qed.

  Lemma own_generational_update_tok γ a t `{!GenTrans t} :
    transA.(gt_condition) t →
    gen_token γ ∗ gen_own γ a ⊢ ⚡==>
      gen_token γ ∗ gen_own γ (t a) ∗ gen_pick γ t.
  Proof.
    iIntros (cond) "[tok gen]".
    iDestruct (gen_token_split with "tok") as "[tok1 tok2]".
    rewrite /gupd.
    (* For both the picks and the resource we pick singleton maps corresponding
    to the one ghost name we care about. *)
    iExists (pick_singleton (inG_id _) γ (cmra_map_transport inG_prf (gen_generation t))).
    iExists (own.iRes_singleton γ (None, GTS_tok_gen, None)).

    (* We first have to show that the picks are valid in relation to [Ω]. *)
    iSplit.
    { iPureIntro. intros i' γ' b.
      intros (-> & -> & <-)%gen_f_singleton_lookup_Some.
      eexists _.
      rewrite genInG_gen_trans.
      split; first done.
      apply gt_condition_transport. simpl.
      eexists t. split; first done. apply cond. }

    (* We use the per-generation token. *)
    iEval (rewrite own.own_eq) in "tok2".
    iFrame "tok2".

    iSplit.
    { iPureIntro. apply: picks_singleton_gen_trans. }
    (* We must now show that the domain of the picks and the resource that we
    own are equal. *)
    iSplit.
    { iPureIntro. apply m_contains_tokens_for_picks_singleton. }
    iIntros (?? fG_resp).
    rewrite /gen_own.
    iEval (rewrite own.own_eq) in "gen".
    iEval (rewrite own.own_eq) in "tok1".
    rewrite /own.own_def.
    iModIntro.
    iDestruct (uPred_own_resp _ _ (gen_generation t) with "gen") as "gen".
    { done. }
    { apply pick_singleton_lookup. }
    iDestruct (uPred_own_resp _ _ (gen_generation t) with "tok1") as "tok1".
    { done. }
    { apply pick_singleton_lookup. }
    iEval (rewrite comm).
    iEval (rewrite -assoc).
    simpl.
    iSplitL "gen".
    { iApply own_mono; last first.
      { rewrite own.own_eq. rewrite /own.own_def. iApply "gen". }
      exists (Some (to_agree t), (None, None), None).
      done. }
    rewrite /gen_pick.
    rewrite /gen_token.
    rewrite -own_op.
    iApply own_mono; last first.
    { rewrite own.own_eq. rewrite /own.own_def. iApply "tok1". }
    reflexivity.
  Qed.

  Lemma own_generational_update γ a :
    gen_own γ a ⊢
      ⚡==> ∃ t, ⌜ transA.(gt_condition) t ⌝ ∗ gen_own γ (t a) ∗ gen_pick γ t.
  Proof.
    iIntros "own".
    rewrite /gupd.
    (* We don't (and can't) pick anything so we give the empty map of picks. *)
    iExists (λ i, ∅), ε.
    rewrite ownM_unit'.
    rewrite left_id.
    iSplit.
    { iPureIntro. apply picks_valid_empty. }
    iSplit. { iPureIntro. apply picks_gen_trans_empty. }
    iSplit.
    { iPureIntro. intros ?.
      rewrite discrete_fun_lookup_empty. rewrite 2!dom_empty.
      done. }
    iIntros (fG ? resp).

    rewrite /gen_own.
    iEval (rewrite own.own_eq) in "own".
    rewrite /own.own_def.
    iModIntro.
    iDestruct (uPred_own_resp_omega _ _ with "own") as (to) "(%cond & own)".
    { done. }
    simpl in cond.
    destruct cond as (t & -> & cond).
    iExists t.
    iSplit; first done.
    simpl.
    rewrite /gen_pick.
    rewrite -own_op.
    rewrite own.own_eq.
    iFrame "own".
  Qed.

  Lemma gupd_plain_soundness P `{!Plain P} :
    (⊢ ⚡==> P) → ⊢ P.
  Proof.
    rewrite /gupd.
    intros HP.
    iDestruct HP as (picks m val picksGT) "(m & % & HP)".
    clear HP.
    set (fG := (build_trans Ω picks)).
    pose proof (build_trans_generation Ω _ picksGT).
    rewrite <- (bgupd_plain fG P).
    iApply ("HP" $!  _ with "[%]").
    apply build_trans_resp; done.
  Qed.

End own_properties.
