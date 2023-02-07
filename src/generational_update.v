From iris.algebra Require Import functions gmap agree excl csum.
From iris.proofmode Require Import classes tactics.
From iris.base_logic.lib Require Export iprop own invariants.
From iris.prelude Require Import options.

From self Require Import extra basic_nextgen_modality gen_trans gen_single_shot.
Import uPred.

Definition generational_cmra A : Type :=
  option (agree (A → A)) * GTS (A → A) * option A.

Definition generational_cmraR (A : cmra) :=
  prodR (prodR (optionR (agreeR (leibnizO (A → A)))) (GTSR (A → A))) (optionR A).

(* Ownership over generational ghost state. *)

Definition gen_own `{!inG Σ (generational_cmraR A)}
    (γ : gname) (a : A) : iProp Σ :=
  own γ (None, (None, None), Some a).

Definition gen_token `{!inG Σ (generational_cmraR A)} γ : iProp Σ :=
  own γ ((None, GTS_tok_both, None) : generational_cmraR A).

Definition own_shot `{!inG Σ (generational_cmraR A)} γ t : iProp Σ :=
  own γ ((None, GTS_tok_gen_shot t, None) : generational_cmraR A).

Definition gen_token_used `{!inG Σ (generational_cmraR A)} γ : iProp Σ :=
  own γ ((None, GTS_tok_perm, None) : generational_cmraR A).

Lemma gen_token_split `{!inG Σ (generational_cmraR A)} γ :
  gen_token γ ⊣⊢
  own γ (None, GTS_tok_perm, None) ∗
  own γ (None, GTS_tok_gen, None).
Proof. rewrite -own_op. done. Qed.

Definition gen_picked_in `{!inG Σ (generational_cmraR A)} γ (f : A → A) : iProp Σ :=
  own γ ((Some (to_agree f), (None, None), None) : generational_cmraR A).

Lemma gen_picked_in_agree `{!inG Σ (generational_cmraR A)} γ (f f' : A → A) :
  gen_picked_in γ f -∗ gen_picked_in γ f' -∗ ⌜ f = f' ⌝.
Proof.
  iIntros "A B".
  iDestruct (own_valid_2 with "A B") as "val".
  rewrite -3!pair_op.
  rewrite 2!prod_validI.
  iDestruct "val" as ([val _]) "_".
  iPureIntro.
  rewrite Some_valid in val.
  apply (to_agree_op_inv_L (A := leibnizO (A → A))) in val.
  done.
Qed.

Definition gen_generation_first {A : cmra} (f : A → A) :
  prodR (optionR (agreeR (leibnizO (A → A)))) (GTSR (A → A)) →
  prodR (optionR (agreeR (leibnizO (A → A)))) (GTSR (A → A))
  := prod_map
       (const (Some (to_agree f)) : optionR (agreeR (leibnizO (A → A))) → optionR (agreeR (leibnizO (A → A))))
       (GTS_floor : (GTSR (A → A)) → (GTSR (A → A))).

(* The generational transformation function for the encoding of each ownership
over a generational camera. *)
Definition gen_generation {A : cmra}
    (f : A → A) : generational_cmraR A → generational_cmraR A :=
  prod_map (gen_generation_first f) (fmap f : optionR A → optionR A).

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

Lemma map_unfold_inG_unfold {Σ A} {i : inG Σ A} :
  map_unfold ≡ own.inG_unfold (i := i).
Proof. done. Qed.

Lemma map_fold_unfold {Σ} {i : gid Σ} (a : R Σ i) :
  map_fold (map_unfold a) ≡ a.
Proof.
  rewrite /map_fold /map_unfold -rFunctor_map_compose -{2}[a]rFunctor_map_id.
  apply (ne_proper (rFunctor_map _)); split=> ?; apply iProp_fold_unfold.
Qed.

Lemma map_unfold_op {Σ} {i : gid Σ} (a b : R Σ i)  :
  map_unfold a ⋅ map_unfold b ≡ map_unfold (a ⋅ b).
Proof. rewrite cmra_morphism_op. done. Qed.

Lemma map_unfold_validN {Σ} {i : gid Σ} n (x : R Σ i) :
  ✓{n} (map_unfold x) ↔ ✓{n} x.
Proof.
  split; [|apply (cmra_morphism_validN _)].
  move=> /(cmra_morphism_validN map_fold). by rewrite map_fold_unfold.
Qed.

Lemma map_unfold_validI {Σ} {i : gid Σ} (a : R Σ i) :
  ✓ map_unfold a ⊢@{iPropI Σ} ✓ a.
Proof. apply valid_entails=> n. apply map_unfold_validN. Qed.

(** Transport an endo map on a camera along an equality in the camera. *)
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

(** Essentially an inhabited set of valid generational transitions for the
camera [A]. We represent the set as a predicate over GTs and inhabitness as a
witness that satisfies the predicate. *)
Record valid_gen_trans (A : cmra) := {
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

Program Definition lift {A} (g : valid_gen_trans A) :
  valid_gen_trans (generational_cmraR A) := {|
    gt_condition t := ∃ t_i,
      t = gen_generation t_i ∧ g.(gt_condition) t_i;
    gt_inhabited := gen_generation g.(gt_inhabited)
  |}.
Next Obligation.
  intros ??. simpl.
  eexists _. split; first done.
  apply g.(gt_inhabited_condition).
Qed.

(** For every entry in [Ω] we store this record of information. The key data is
[gti_valid] which is the set of valid transformation for the camera at index
[i]. The equality [gti_look] is the "canonical" equality we will use to show
that the resource [R Σ i] has the proper form. Using this equality is necesarry
as we otherwise end with different equalities of this form that we then do not
know to be equal. *)
Record gen_trans_info (Σ : gFunctors) (i : gid Σ) := {
  gti_car : cmra;
  gti_look : generational_cmraR gti_car = R Σ i ;
  gti_valid : valid_gen_trans (R Σ i);
}.

Arguments gti_car {_} {_}.
Arguments gti_look {_} {_}.
Arguments gti_valid {_} {_}.

(** A copy of [option] to work arround universe inconsistencies that arrise if
we use [option]. *)
Inductive option2 (A : Type) : Type :=
  | Some2 : A -> option2 A
  | None2 : option2 A.

Arguments Some2 {A} a.
Arguments None2 {A}.

(** [gTransforms] contains a partial map from the type of cameras into a "set"
of valid transformation function for that camera. *)
Class gTransforms {Σ : gFunctors} := {
  g_valid_gt :> ∀ (i : gid Σ), option2 (gen_trans_info Σ i)
}.

Global Arguments g_valid_gt {_} _.

#[export] Hint Mode gTransforms +.

Definition gen_transport {A B : cmra}
    (eq : A = B) (g : valid_gen_trans A) : valid_gen_trans B :=
  eq_rect A valid_gen_trans g B eq.

Program Definition gen_cmra_eq {A B C : cmra}
  (eq : A = B)
  (eq2 : generational_cmraR B = C) : generational_cmraR A = C.
Proof.
  rewrite -eq2.
  rewrite eq.
  reflexivity.
Defined.

(* The global functor [Σ] contains the camera [A] and the global generational
transformation [Ω] respects [g]. *)
Class genInG (Σ : gFunctors) (Ω : @gTransforms Σ) (A : cmra) (g : valid_gen_trans A)
    := GenInG {
  genInG_id : gid Σ;
  genInG_apply := rFunctor_apply (gFunctors_lookup Σ genInG_id);
  genInG_gti : gen_trans_info Σ (genInG_id);
  genInG_gen_trans : Ω.(g_valid_gt) (genInG_id) = Some2 genInG_gti;
  genInG_gti_typ : A = genInG_gti.(gti_car);
  genInG_gen_trans2 :
    genInG_gti.(gti_valid) =
      (gen_transport (gen_cmra_eq genInG_gti_typ genInG_gti.(gti_look)) (lift g));
}.

Global Arguments genInG_id {_} {_} {_} {_} _.

Global Program Instance genInG_inG `{i : !genInG Σ Ω A g} :
    inG Σ (generational_cmraR A) :=
  {|
    inG_id := genInG_id i;
    inG_prf := gen_cmra_eq genInG_gti_typ genInG_gti.(gti_look);
  |}.

(** [Picks] contains transformation functions for a subset of ghost names. It is
the entries that we have picked generational transformation for. *)
Definition Picks Σ : Type := ∀ i, gmap gname (R Σ i → R Σ i).

(** Every pick in [picks] is a valid generational transformation and satisfies
the conditions for that cmra in [Ω]. *)
Definition picks_valid {Σ} (Ω : gTransforms) (picks : Picks Σ) :=
  ∀ i γ t, picks i !! γ = Some t →
    GenTrans t ∧
    ∃ gti, Ω.(g_valid_gt) i = Some2 gti ∧ gti.(gti_valid).(gt_condition) t.

(* The functor [fG] respects the conditions in [Ω] and the entries in
[picks]. *)
Definition fG_resp {Σ} (fG : iResUR Σ → iResUR Σ) (Ω : gTransforms) (picks : Picks Σ) :=
  ∀ (m : iResUR Σ) i γ a gti,
    m i !! γ = Some a → (* For every element in the old element. *)
    Ω.(g_valid_gt) i = Some2 gti → (* Where we have transformation conditions. *)
    ∃ t, (* There exists a transformation. *)
      Proper ((≡) ==> (≡)) t ∧
      (fG m) i !! γ = Some (map_unfold (t (map_fold a))) ∧
      gti.(gti_valid).(gt_condition) t ∧
      (∀ t', picks i !! γ = Some t' → t = t').

Definition m_contains_tokens_for_picks {Σ} Ω (picks : Picks Σ) (m : iResUR Σ) :=
  ∀ i,
    dom (picks i) ≡ dom (m i) ∧
    (∀ (γ : gname) (a : Rpre Σ i),
      m i !! γ = Some a  →
      ∃ gti (t : gti.(gti_car) → gti.(gti_car)),
        Ω.(g_valid_gt) i = Some2 gti ∧
        picks i !! γ = Some (cmra_map_transport gti.(gti_look) (gen_generation t)) ∧
        a ≡ map_unfold (cmra_transport (gti.(gti_look)) (None, GTS_tok_gen_shot t, None))).

Definition nextgen {Σ : gFunctors} {Ω : gTransforms} P : iProp Σ :=
  ∃ (picks : Picks Σ) (m : iResUR Σ),
    ⌜ picks_valid Ω picks ⌝ ∗
    uPred_ownM m ∗ ⌜ m_contains_tokens_for_picks Ω picks m ⌝ ∗
    ∀ (fG : iResUR Σ → _) (_ : GenTrans fG) (_ : fG_resp fG Ω picks ),
      ⚡={fG}=> P.

(* Definition nextgen_alt {Σ : gFunctors} {Ω : gTransforms} P : iProp Σ := *)
(*   ∀ (fG : iResUR Σ → _) (_ : GenTrans fG), *)
(*     ⌜ fG_resp fG Ω picks ⌝ -∗ *)
(*     uPred_ownM m -∗ *)
(*     ⚡={fG}=> P. *)

Notation "⚡==> P" := (nextgen P)
  (at level 99, P at level 200, format "⚡==>  P") : bi_scope.

Class IntoNextgen {Σ} {Ω : gTransforms} (P : iProp Σ) (Q : iProp Σ) :=
  into_nextgen : P ⊢ ⚡==> Q.
Global Arguments IntoNextgen  {_} {_} _%I _%I.
Global Arguments into_nextgen {_} {_} _%I _%I.
Global Hint Mode IntoNextgen + + ! - : typeclass_instances.

Lemma uPred_own_resp `{i : !genInG Σ Ω A tr} fG `{!GenTrans fG} picks
  (f : generational_cmraR A → _) γ a `{!Proper ((≡) ==> (≡)) f} :
  fG_resp (Σ := Σ) fG Ω picks →
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
          (genInG_id i)
          γ
          (own.inG_unfold (i := genInG_inG) (cmra_transport inG_prf a))
          _
      ).
    - rewrite discrete_fun_lookup_singleton.
      rewrite lookup_singleton.
      done.
    - apply genInG_gen_trans. }
  destruct HI as (t & proper & fGLook & valid & lookEq).
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
  rewrite (own.inG_fold_unfold (i := (@genInG_inG Σ Ω A tr i))).
  rewrite cmra_map_transport_cmra_transport.
  done.
Qed.

Lemma cmra_transport_map_transport {A B} (eq : A = B) t a :
  cmra_transport eq (cmra_map_transport (eq_sym eq) t a) =
  t (cmra_transport eq a).
Proof. destruct eq. simpl. done. Qed.

Lemma cmra_transport_pcore {A B : cmra} (eq : A = B) (a : A) :
  (cmra_transport eq) <$> (pcore a) = pcore (cmra_transport eq a).
Proof. destruct eq. simpl. destruct (pcore a); done. Qed.

Lemma gt_conditions_transport {A B} (eq : generational_cmraR A = B) tr t :
  gt_condition (gen_transport eq (lift tr)) t =
  gt_condition (lift tr) (cmra_map_transport (eq_sym eq) t).
Proof. destruct eq. done. Qed.

Lemma uPred_own_resp_omega `{i : !genInG Σ Ω A tr} fG `{!GenTrans fG} picks γ
    (a : generational_cmraR A) :
  fG_resp (Σ := Σ) fG Ω picks →
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
      Hresp (discrete_fun_singleton (genInG_id i)
              {[γ := own.inG_unfold (cmra_transport inG_prf a)]})
          (inG_id genInG_inG)
          γ
          (own.inG_unfold (cmra_transport inG_prf a))
          _
      ).
    - rewrite discrete_fun_lookup_singleton.
      rewrite lookup_singleton.
      done.
    - simpl.
      apply genInG_gen_trans. }
  destruct HI as (t & proper & fGLook & valid & lookEq).
  set (eq_sym (@inG_prf _ _ (genInG_inG))) as eq.
  iIntros "HR".
  iExists (cmra_map_transport eq t).
  iSplit.
  { iPureIntro.
    rewrite -gt_conditions_transport.
    rewrite -genInG_gen_trans2.
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

  Definition gen_f_singleton_lookup_Some idx' γ γ' f (f' : R Σ idx' → _) :
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

  Lemma picks_valid_empty Ω :
    picks_valid Ω (λ i : gid Σ, ∅).
  Proof. intros ???. rewrite lookup_empty. inversion 1. Qed.

End pick_singleton_lemmas.

Global Instance gen_trans_cmra_map_transport {A B : cmra} (eq : A = B)
    (f : A → A) :
  GenTrans f → GenTrans (cmra_map_transport eq f).
Proof. destruct eq. done. Qed.

Lemma gt_condition_transport {A B} (transA : valid_gen_trans A)
    (f : A → A)
    (eq : generational_cmraR A = B) :
  gt_condition (lift transA) (gen_generation f) →
  gt_condition (gen_transport eq (lift transA))
    (cmra_map_transport eq (gen_generation f)).
Proof. destruct eq. simpl. done. Qed.

Lemma picks_valid_singleton `{i : !genInG Σ Ω A gens} f γ :
  GenTrans f →
  gt_condition gens f →
  picks_valid Ω
    (pick_singleton (genInG_id i) γ
       (cmra_map_transport inG_prf (gen_generation f))).
Proof.
  intros ?? idx' γ' f'.
  intros (-> & -> & <-)%gen_f_singleton_lookup_Some.
  split; first apply _.
  eexists _.
  rewrite genInG_gen_trans.
  split; first done.
  rewrite genInG_gen_trans2.
  apply gt_condition_transport. simpl.
  eexists f. split; first done. assumption.
Qed.

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
          match Ω.(g_valid_gt) i with
          | None2 => None
          | Some2 gt =>
              Some $ map_unfold $ gt.(gti_valid).(gt_inhabited) $ map_fold a
          end
      end
    ) (m i).

Section picks_lemmas.
  Context {Σ : gFunctors}.
  Implicit Types (picks : Picks Σ).

  Lemma core_Some_pcore {A : cmra} (a : A) : core (Some a) = pcore a.
  Proof. done. Qed.

  Lemma build_trans_generation Ω picks :
    picks_valid Ω picks → GenTrans (build_trans Ω picks).
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
      * apply picksGT in look as [gt ?]. solve_proper.
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
        specialize (picksGT i γ pick eq2) as [??].
        apply generation_valid.
        apply: cmra_morphism_validN.
        apply Hval.
      * destruct (g_valid_gt Ω i); last done.
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
        specialize (picksGT i γ pick pickLook) as [??].
        rewrite -generation_pcore.
        rewrite -cmra_morphism_pcore.
        destruct (pcore a); done.
      * destruct (g_valid_gt Ω i).
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
      * specialize (picksGT i γ pick pickLook) as [??].
        destruct (m1 i !! γ) eqn:eq1; destruct (m2 i !! γ) eqn:eq2;
          rewrite eq1 eq2; simpl; try done.
        rewrite -Some_op.
        rewrite -cmra_morphism_op.
        rewrite -generation_op.
        rewrite -cmra_morphism_op.
        done.
      * destruct (g_valid_gt Ω i);
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
    picks_valid Ω picks →
    fG_resp (build_trans Ω picks) Ω picks.
  Proof.
    rewrite /fG_resp /build_trans.
    intros picksGT ??????.
    destruct (picks i !! γ) as [pick|] eqn:eq.
    - exists pick.
      (* specialize (sat i γ pick eq) as (gt' & ? & ?). *)
      specialize (picksGT i γ pick eq) as [l (gt' & ? & ?)].
      assert (gti = gt') as <- by congruence.
      rewrite map_lookup_imap. rewrite H. simpl.
      split; first apply _.
      rewrite eq.
      split; first done.
      split; first done.
      move=> ? [= ->] //.
    - intros ?.
      exists (gt_inhabited gti.(gti_valid)).
      split; first apply _.
      rewrite map_lookup_imap. rewrite H. simpl.
      rewrite eq H0.
      split; first done.
      split; first apply gt_inhabited_condition.
      intros ? [=].
  Qed.

  Definition merge_picks (picks1 picks2 : Picks Σ) :=
    λ i, (picks1 i) ∪ (picks2 i).

  Definition map_agree_overlap `{FinMap K M} {A} (m1 m2 : M A) :=
    ∀ (k : K) (i j : A), m1 !! k = Some i → m2 !! k = Some j → i = j.

  Lemma m_contains_tokens_for_picks_empty Ω :
    m_contains_tokens_for_picks Ω (λ i : gid Σ, ∅) ε.
  Proof. done. Qed.

  Lemma tokens_for_picks_agree_overlap Ω picks1 picks2 m1 m2 :
    m_contains_tokens_for_picks Ω picks1 m1 →
    m_contains_tokens_for_picks Ω picks2 m2 →
    uPred_ownM m1 -∗
    uPred_ownM m2 -∗
    ⌜ ∀ i, map_agree_overlap (picks1 i) (picks2 i) ⌝.
  Proof.
    iIntros (t1 t2) "m1 m2". iIntros (i).
    iIntros (γ a1 a2 look1 look2).
    specialize (t1 i) as (domEq1 & m1look).
    assert (is_Some (m1 i !! γ)) as [? m1Look].
    { rewrite -elem_of_dom -domEq1 elem_of_dom. done. }
    edestruct m1look as (gti1 & t1 & ? & picks1Look & ?); first done.
    specialize (t2 i) as (domEq2 & m2look).
    assert (is_Some (m2 i !! γ)) as [? m2Look].
    { rewrite -elem_of_dom -domEq2 elem_of_dom. done. }
    edestruct m2look as (gti2 & t2 & ? & picks2Look & ?); first done.
    clear m1look m2look.
    assert (gti1 = gti2) as -> by congruence.
    iCombine "m1 m2" as "m".
    iDestruct (ownM_valid with "m") as "#Hv".
    rewrite discrete_fun_validI.
    setoid_rewrite gmap_validI.
    iSpecialize ("Hv" $! i γ).
    rewrite lookup_op.
    rewrite m1Look m2Look.
    rewrite option_validI /=.
    rewrite H0 H2.
    simplify_eq.
    rewrite map_unfold_op.
    clear.
    iClear "m".
    rewrite map_unfold_validI.
    destruct (gti_look gti2); simpl.
    rewrite 2!prod_validI.
    iDestruct "Hv" as "((_ & %Hv) & _)".
    simpl in Hv.
    destruct Hv as [? Hv].
    simpl in *.
    rewrite Some_valid in Hv.
    rewrite Cinr_valid in Hv.
    rewrite to_agree_op_valid in Hv.
    rewrite Hv.
    done.
  Qed.

  Lemma cmra_transport_validI {A B : cmra} (eq : A =@{cmra} B) (a : A) :
    ✓ cmra_transport eq a ⊢@{iPropI Σ} ✓ a.
  Proof. destruct eq. done. Qed.

  Lemma tokens_for_picks_agree_overlap' Ω picks1 picks2 m1 m2 :
    m_contains_tokens_for_picks Ω picks1 m1 →
    m_contains_tokens_for_picks Ω picks2 m2 →
    uPred_ownM m1 -∗
    uPred_ownM m2 -∗
    ⌜ ∀ i γ a b, (m1 i) !! γ = Some a → (m2 i) !! γ = Some b → a ≡ b ⌝.
  Proof.
    iIntros (t1 t2) "m1 m2". iIntros (i).
    iIntros (γ a1 a2 m1Look m2Look).
    specialize (t1 i) as (domEq1 & m1look).
    edestruct m1look as (gti1 & t1 & ? & picks1Look & ?); first done.
    specialize (t2 i) as (domEq2 & m2look).
    edestruct m2look as (gti2 & t2 & ? & picks2Look & ?); first done.
    clear m1look m2look.
    assert (gti1 = gti2) as -> by congruence.
    iCombine "m1 m2" as "m".
    iDestruct (ownM_valid with "m") as "#Hv".
    rewrite discrete_fun_validI.
    setoid_rewrite gmap_validI.
    iSpecialize ("Hv" $! i γ).
    rewrite lookup_op.
    rewrite m1Look m2Look.
    rewrite option_validI /=.
    rewrite H0 H2.
    simplify_eq.
    rewrite map_unfold_op.
    rewrite map_unfold_validI.
    rewrite -cmra_transport_op.
    rewrite cmra_transport_validI.
    rewrite -pair_op.
    rewrite -pair_op.
    rewrite prod_validI.
    rewrite prod_validI.
    iDestruct "Hv" as "((_ & Hv) & _)". simpl.
    rewrite GTS_tok_gen_shot_foo.
    iDestruct "Hv" as %->.
    done.
  Qed.

  Lemma cmra_map_transport_inj {A B : cmra} (eq : A = B) a b :
    cmra_map_transport eq a = cmra_map_transport eq b → a = b.
  Proof. destruct eq. done. Qed.

  Lemma m_contains_tokens_for_picks_merge Ω picks1 picks2 (m1 m2 : iResUR Σ) :
    (∀ i, map_agree_overlap (picks1 i) (picks2 i)) →
    (∀ i γ a b, (m1 i) !! γ = Some a → (m2 i) !! γ = Some b → a ≡ b) →
    m_contains_tokens_for_picks Ω picks1 m1 →
    m_contains_tokens_for_picks Ω picks2 m2 →
    m_contains_tokens_for_picks Ω (merge_picks picks1 picks2) (m1 ⋅ m2).
  Proof.
    intros overlap1 overlap2 tok1 tok2.
    intros i.
    rewrite /merge_picks.
    rewrite dom_op.
    specialize (tok1 i) as (domEq1 & tok1).
    specialize (tok2 i) as (domEq2 & tok2).
    split.
    { rewrite -domEq1 -domEq2. rewrite dom_union. done. }
    intros γ a.

    rewrite discrete_fun_lookup_op.
    rewrite lookup_op.
    case (m1 i !! γ) eqn:look1; rewrite look1;
      case (m2 i !! γ) eqn:look2; rewrite look2.
    - specialize (overlap2 i _ _ _ look1 look2) as elemEq.
      apply tok1 in look1 as (gti1 & t1 & val1 & picksLook1 & a1).
      apply tok2 in look2 as (gti2 & t2 & val2 & picksLook2 & a2).
      intros [= opEq].
      exists gti1, t1.
      split; first done.
      split. { erewrite lookup_union_Some_l; done. }
      rewrite -opEq.
      rewrite -elemEq.
      rewrite a1.
      assert (gti1 = gti2) as -> by congruence.
      rewrite map_unfold_op.
      f_equiv.
      rewrite -cmra_transport_op.
      f_equiv.
      rewrite -pair_op.
      split; first split; [done| |done].
      simpl.
      specialize (overlap1 i _ _ _ picksLook1 picksLook2) as hi.
      apply cmra_map_transport_inj in hi.
      rewrite /GTS_tok_gen_shot.
      rewrite -!pair_op.
      split; first done. simpl.
      rewrite -Some_op.
      f_equiv.
      rewrite -Cinr_op.
      f_equiv.
      apply agree_idemp.
    - intros [= ->].
      apply tok1 in look1 as (gti1 & t1 & val1 & picksLook1 & a1).
      exists gti1, t1.
      split; first done.
      split. { erewrite lookup_union_Some_l; done. }
      apply a1.
    - intros [= ->].
      apply tok2 in look2 as (gti2 & t2 & val2 & picksLook2 & a2).
      exists gti2, t2.
      split; first done.
      split; last done.
      erewrite lookup_union_r; try done.
      apply not_elem_of_dom.
      rewrite domEq1.
      rewrite not_elem_of_dom.
      done.
    - intros [=].
  Qed.

  Lemma picks_valid_merge {Ω} (picks1 picks2 : Picks Σ) :
    picks_valid Ω picks1 →
    picks_valid Ω picks2 →
    picks_valid Ω (merge_picks picks1 picks2).
  Proof.
    intros p1 p2.
    intros i' γ t.
    rewrite /merge_picks.
    intros [look | [? look]]%lookup_union_Some_raw.
    - apply p1 in look as (? & gt & ? & ?). naive_solver.
    - apply p2 in look as (? & gt & ? & ?). naive_solver.
  Qed.

End picks_lemmas.

Lemma transportation_equality_1 {A B C : cmra} (t : A → A)
    (eq2 : generational_cmraR C = B) (eq3 : A = C) :
  cmra_map_transport (gen_cmra_eq eq3 eq2) (gen_generation t) =
  cmra_map_transport eq2 (gen_generation (cmra_map_transport eq3 t)).
Proof. destruct eq2. simpl. destruct eq3. simpl. done. Qed.

Lemma transportation_equality_2 Σ Ω `{i : !genInG Σ Ω A aa} t :
  cmra_transport (gen_cmra_eq genInG_gti_typ (gti_look genInG_gti))
    (None, GTS_tok_gen_shot t, None)
  ≡ cmra_transport (gti_look genInG_gti)
      (None, GTS_tok_gen_shot (cmra_map_transport genInG_gti_typ t), None).
Proof.
  destruct (gti_look genInG_gti).
  simpl.
  destruct genInG_gti_typ.
  done.
Qed.

Lemma m_contains_tokens_for_picks_singleton {Σ} Ω `{i : !genInG Σ Ω A aa}
    γ (t : A → A) :
  m_contains_tokens_for_picks Ω
    (pick_singleton (inG_id _) γ (
      cmra_map_transport inG_prf (gen_generation t)
    ))
    (own.iRes_singleton γ ((None, GTS_tok_gen_shot t, None) : generational_cmraR A)).
Proof.
  intros i'.
  split.
  { apply pick_singleton_iRes_singleton_dom. }
  (* We how show that the resource contains the tokens as it should. *)
  intros γ' b.
  intros look.
  apply iRes_singleton_lookup_alt in look as (iEq & -> & bEq).
  destruct iEq.
  exists genInG_gti.
  exists (cmra_map_transport (genInG_gti_typ) t).
  split. { simpl. apply genInG_gen_trans. }
  split.
  { rewrite pick_singleton_lookup.
    f_equiv.
    rewrite /inG_prf /=.
    apply transportation_equality_1. }
  rewrite <- bEq.
  rewrite /map_fold.
  f_equiv.
  rewrite /inG_prf /=.
  simpl.
  specialize (transportation_equality_2 Σ _ t).
  done.
Qed.

(* (** * Properties about generational ghost ownership. *) *)
Section own_properties.

  Context `{i : !genInG Σ Ω A transA}.

  Implicit Types a : A.

  Definition gen_picked_out γ t : iProp Σ :=
    ⌜ GenTrans t ∧ transA.(gt_condition) t ⌝ ∧ own_shot γ t.

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

  Lemma gen_token_pick_next γ t `{!GenTrans t} :
    transA.(gt_condition) t →
    gen_token γ ⊢ |==> gen_token_used γ ∗ gen_picked_out γ t.
  Proof.
    intros cond.
    rewrite gen_token_split.
    iIntros "[$ B]".
    rewrite /gen_picked_out.
    rewrite bi.pure_True; last done.
    rewrite left_id.
    iApply (own_update with "B").
    apply prod_update; last done.
    apply prod_update; first done.
    apply prod_update; first done.
    apply option_update.
    apply cmra_update_exclusive. done.
  Qed.

  Lemma gen_token_used_nextgen γ :
    gen_token_used γ ⊢ ⚡==> gen_token γ.
  Proof.
    iIntros "tok".
    rewrite /gen_token_used.
    iEval (rewrite own.own_eq) in "tok".
    iExists (λ i, ∅), ε.
    rewrite ownM_unit'.
    rewrite left_id.
    iSplit. { iPureIntro. apply picks_valid_empty. }
    iSplit. { iPureIntro. apply m_contains_tokens_for_picks_empty. }
    iIntros (fG ? resp).
    iModIntro.
    iDestruct (uPred_own_resp_omega _ _ with "tok") as (to) "(%cond & tok)";
      first done.
    destruct cond as (t & -> & cond).
    rewrite /gen_token.
    rewrite /gen_generation /gen_generation_first.
    iApply own_mono; last first.
    { rewrite own.own_eq. iApply "tok". }
    eexists (Some (to_agree t), (None, None), None).
    (* We split and simpl as it speeds up the reflexivity. *)
    split; simpl; reflexivity.
  Qed.

  Lemma gen_picked_next_nextgen γ t :
    gen_picked_out γ t ⊢ ⚡==> gen_picked_in γ t.
  Proof.
    iIntros "((% & %cond) & #tok)".
    iExists (pick_singleton (inG_id _) γ (cmra_map_transport inG_prf (gen_generation t))).
    iExists (own.iRes_singleton γ
               ((None, GTS_tok_gen_shot t, None) : generational_cmraR A)).
    (* We first have to show that the picks are valid in relation to [Ω]. *)
    iSplit.
    { iPureIntro. apply: picks_valid_singleton. done. }
    (* We use the per-generation token. *)
    rewrite /own_shot.
    iEval (rewrite own.own_eq) in "tok".
    iFrame "tok".
    iSplit.
    { iPureIntro. apply m_contains_tokens_for_picks_singleton. }
    iIntros (fG ? resp).
    rewrite /gen_own.
    rewrite /own.own_def.
    iModIntro.
    iDestruct (uPred_own_resp _ _ (gen_generation t) with "tok") as "tok'".
    { done. }
    { apply pick_singleton_lookup. }
    iClear "tok".
    simpl.
    rewrite /gen_picked_in.
    rewrite /gen_token.
    simpl.
    iApply (own_mono (i := (@genInG_inG Σ Ω A transA i)) γ _ (Some (to_agree t), (None, None), None)); last first.
    { rewrite own.own_eq. rewrite /own.own_def. iApply "tok'". }
    reflexivity.
  Qed.

  Lemma own_generational_update γ a :
    gen_own γ a ⊢
      ⚡==> ∃ t, ⌜ transA.(gt_condition) t ⌝ ∗
                 gen_own γ (t a) ∗ gen_picked_in γ t.
  Proof.
    iIntros "own".
    rewrite /nextgen.
    (* We don't (and can't) pick anything so we give the empty map of picks. *)
    iExists (λ i, ∅), ε.
    rewrite ownM_unit'.
    rewrite left_id.
    iSplit. { iPureIntro. apply picks_valid_empty. }
    iSplit.
    { iPureIntro. apply m_contains_tokens_for_picks_empty. }
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
    rewrite /gen_picked_in.
    rewrite -own_op.
    rewrite own.own_eq.
    iFrame "own".
  Qed.

  Lemma fG_resp_merge_l fG picks1 picks2 :
    fG_resp fG Ω (merge_picks picks1 picks2) →
    fG_resp fG Ω picks1.
  Proof.
    intros resp.
    intros m i' γ ? ? look1 val.
    edestruct resp as (t & ? & ? & ? & TT); [done|done| ].
    exists t.
    split; first done.
    split; first done.
    split; first done.
    intros t' look.
    apply TT.
    rewrite /merge_picks.
    apply lookup_union_Some_l.
    done.
  Qed.

  Lemma lookup_union_r_overlap `{FinMap K M} {B} (picks1 picks2 : M B) γ t :
    map_agree_overlap (picks1) (picks2) →
    picks2 !! γ = Some t →
    (picks1 ∪ picks2) !! γ = Some t.
  Proof.
    intros lap look.
    destruct (picks1 !! γ) eqn:eq.
    - apply lookup_union_Some_l.
      rewrite eq.
      f_equiv.
      eapply lap; done.
    - rewrite -look. apply lookup_union_r. done.
  Qed.

  Lemma fG_resp_merge_r fG picks1 picks2 :
    (∀ i, map_agree_overlap (picks1 i) (picks2 i)) →
    fG_resp fG Ω (merge_picks picks1 picks2) →
    fG_resp fG Ω picks2.
  Proof.
    intros overlap resp.
    intros m i' γ ? ? look1 val.
    edestruct resp as (t & ? & ? & ? & TT); [done|done| ].
    exists t.
    split; first done.
    split; first done.
    split; first done.
    intros t' look.
    apply TT.
    rewrite /merge_picks.
    apply lookup_union_r_overlap; last done.
    apply overlap.
  Qed.

  Lemma tokens_persistent picks m :
    m_contains_tokens_for_picks Ω picks m →
    Persistent (uPred_ownM m).
  Proof.
    intros tok.
    apply ownM_persistent.
    rewrite core_id_total.
    intros i' γ.
    destruct (tok i') as (domEq & mLook).
    rewrite discrete_fun_lookup_core.
    rewrite lookup_core.
    destruct (m i' !! γ) eqn:look; rewrite look; last done.
    rewrite core_Some_pcore.
    simpl.
    apply mLook in look as (? & ? & ? & ? & ->).
    rewrite -cmra_morphism_pcore.
    rewrite -cmra_transport_pcore.
    done.
  Qed.

  Lemma nextgen_and_2 P Q :
    (⚡==> P) ∧ (⚡==> Q) ⊢ ⚡==> (P ∧ Q).
  Proof.
    rewrite /nextgen.
    iIntros "H".
    rewrite and_exist_r.
    setoid_rewrite and_exist_r.
    iDestruct "H" as (picks1 m1) "H".
    rewrite and_exist_l.
    setoid_rewrite and_exist_l.
    iDestruct "H" as (picks2 m2) "H".
    iExists (merge_picks picks1 picks2), (m1 ⋅ m2).
    setoid_rewrite <- bnextgen_and.
    iAssert (⌜ picks_valid Ω picks1 ⌝)%I as %val1.
    { iDestruct "H" as "[($ & ?) _]". }
    iAssert (⌜ picks_valid Ω picks2 ⌝)%I as %val2.
    { iDestruct "H" as "[_ ($ & ?)]". }
    iSplit.
    { iPureIntro. apply picks_valid_merge; done. }
    iAssert (⌜m_contains_tokens_for_picks Ω picks1 m1⌝)%I as %tok1.
    { iDestruct "H" as "[(? & ? & $ & ?) _]". }
    iAssert (⌜m_contains_tokens_for_picks Ω picks2 m2⌝)%I as %tok2.
    { iDestruct "H" as "[_ (? & ? & $ & ?)]". }
    pose proof (tokens_persistent _ _ tok1).
    pose proof (tokens_persistent _ _ tok2).
    iAssert (uPred_ownM (m1)) as "#M1".
    { iDestruct "H" as "[(? & $ & ? & ?) _]". }
    iAssert (uPred_ownM (m2)) as "#M2".
    { iDestruct "H" as "[_ (? & $ & ? & ?)]". }
    iSplitL "".
    { iSplitL ""; iFrame "#". }
    iDestruct (tokens_for_picks_agree_overlap with "M1 M2") as %disj;
      [done|done|].
    iDestruct (tokens_for_picks_agree_overlap' with "M1 M2") as %disj2;
      [done|done|].
    iSplit. { iPureIntro. apply m_contains_tokens_for_picks_merge; try done. }
    iIntros (fG ? resp).
    iSplit.
    - iDestruct "H" as "[(? & ? & ? & HP) _]".
      iApply "HP".
      iPureIntro.
      eapply fG_resp_merge_l. done.
    - iDestruct "H" as "[_ (? & ? & ? & HQ)]".
      iApply "HQ".
      iPureIntro.
      eapply fG_resp_merge_r; done.
  Qed.

  Lemma nextgen_sep_2 P Q : (⚡==> P) ∗ (⚡==> Q) ⊢ ⚡==> (P ∗ Q) .
  Proof.
    rewrite /nextgen.
    iIntros "[P1 P2]".
    iDestruct "P1" as (picks1 m1 ?) "(m1 & %toks1 & HP)".
    iDestruct "P2" as (picks2 m2 ?) "(m2 & %toks2 & HQ)".
    iDestruct (tokens_for_picks_agree_overlap with "m1 m2") as %disj;
      [done|done|].
    iDestruct (tokens_for_picks_agree_overlap' with "m1 m2") as %disj2;
      [done|done|].
    iExists (merge_picks picks1 picks2), (m1 ⋅ m2).
    iSplit.
    { iPureIntro. apply picks_valid_merge; try done. }
    iCombine "m1 m2" as "$".
    iSplit.
    { iPureIntro. apply m_contains_tokens_for_picks_merge; done. }
    iIntros (fG fGgt resp).
    iSpecialize ("HP" $! fG with "[]").
    { iPureIntro. eapply fG_resp_merge_l. done. }
    iSpecialize ("HQ" $! fG with "[]").
    { iPureIntro. eapply fG_resp_merge_r; done. }
    iModIntro.
    iFrame "HP HQ".
  Qed.

  Lemma nextgen_mono P Q :
    (P ⊢ Q) → (⚡==> P) ⊢ ⚡==> Q.
  Proof.
    intros Hi.
    rewrite /nextgen.
    iDestruct 1 as (? m ?) "(? & ? & HP)".
    iExists picks, m.
    iFrame.
    iSplit; first done.
    iIntros (fG ? resp).
    iApply bnextgen_mono.
    { apply Hi. }
    iApply "HP".
    done.
  Qed.

  Lemma nextgen_intro_plain P `{!Plain P} : P ⊢ ⚡==> P.
  Proof.
    rewrite /nextgen.
    iIntros "P".
    iExists (λ i, ∅), ε.
    rewrite ownM_unit'.
    rewrite left_id.
    iSplit. { iPureIntro. apply picks_valid_empty. }
    iSplit.
    { iPureIntro. apply m_contains_tokens_for_picks_empty. }
    iIntros (fG ? resp).
    iModIntro.
    done.
  Qed.

  Lemma nextgen_emp_2 : emp ⊢ ⚡==> emp.
  Proof. apply: nextgen_intro_plain. Qed.

  (** This and the next lemma holds since it holds for the basic generational
  update modality and since [<pers>] commutes with all the connectives used in
  the non-basic nextgen modality (exists, separation, etc.). *)
  Lemma nextgen_intuitinistically_1 P : (⚡==> (<pers> P)) ⊢ <pers> (⚡==> P).
  Proof.
    rewrite /nextgen.
    iDestruct 1 as (picks m) "(#? & m & %tok & #HP)".
    pose proof (tokens_persistent _ _ tok).
    iDestruct "m" as "#m".
    iExists picks, m.
    iFrame "#". iFrame (tok).
    iIntros (fG ? resp).
    iDestruct ("HP" $! fG _ resp) as "#HP'".
    iModIntro. iModIntro.
    iApply "HP'".
  Qed.

  Lemma nextgen_intuitinistically_2 P : <pers> (⚡==> P) ⊢ ⚡==> (<pers> P).
  Proof.
    rewrite /nextgen.
    iDestruct 1 as (picks m) "(#? & #? & #? & HP)".
    iExists picks, m.
    iFrame "#".
    iIntros (fG ? resp).
    iDestruct ("HP" $! fG _ resp) as "#HP".
    iModIntro. iModIntro.
    iApply "HP".
  Qed.

  Global Instance nextgen_mono' :
    Proper ((⊢) ==> (⊢)) nextgen.
  Proof. intros P Q. apply nextgen_mono. Qed.

  Global Instance nextgen_ne : NonExpansive nextgen.
  Proof. solve_proper. Qed.

  Global Instance nextgen_proper : Proper ((≡) ==> (≡)) nextgen := ne_proper _.

  Lemma modality_nextgen_mixin :
    modality_mixin (@nextgen _ _)
      (MIEnvTransform (IntoNextgen))
      (MIEnvTransform (IntoNextgen)).
  Proof.
    split; simpl; split_and?.
    - intros ?? Hi.
      rewrite Hi.
      rewrite 2!intuitionistically_into_persistently.
      apply nextgen_intuitinistically_2.
    - intros. rewrite nextgen_and_2. done.
    - done.
    - apply nextgen_emp_2.
    - apply nextgen_mono.
    - apply nextgen_sep_2.
  Qed.
  Definition modality_nextgen :=
    Modality _ modality_nextgen_mixin.

  Global Instance from_modal_nextgen P :
    FromModal True modality_nextgen (⚡==> P) (⚡==> P) P | 1.
  Proof. by rewrite /FromModal. Qed.

  Lemma nextgen_plain_soundness P `{!Plain P} :
    (⊢ ⚡==> P) → ⊢ P.
  Proof.
    rewrite /nextgen.
    intros HP.
    iDestruct HP as (picks m picksGT) "(m & % & HP)".
    clear HP.
    set (fG := (build_trans Ω picks)).
    pose proof (build_trans_generation Ω _ picksGT).
    rewrite <- (bnextgen_plain fG P).
    iApply ("HP" $!  _ with "[%]").
    apply build_trans_resp; done.
  Qed.

  Lemma nextgen_later_2 P :
    (⚡==> ▷ P) ⊢ ▷ (⚡==> P).
  Proof. rewrite /nextgen. iIntros "?". iNext. done. Qed.

  Lemma nextgen_later P :
    ▷ (⚡==> P) ⊣⊢ ◇ ⚡==> (▷ P).
  Proof.
    iSplit.
    - rewrite /nextgen.
      iIntros "H".
      assert (Inhabited (Picks Σ)). { admit. }
      iDestruct "H" as (??) "(>? & O & >? & P)".
      rewrite later_ownM.
      iDestruct "O" as (m') "(M & eq)".
      iModIntro.
      iExists picks, m'.
      iFrame.
      iSplit. { admit. }
      iIntros (fG ? resp).
      setoid_rewrite <- bnextgen_later.
      iNext.
      iApply "P".
      done.
    - rewrite nextgen_later_2.
      iApply except_0_later.
  Admitted.

  (* Global Instance into_nextgen_gen_picked_out P Q : *)
  (*   IntoNextgen P Q → IntoNextgen (▷ P) (▷ Q). *)
  (* Proof. *)
  (*   rewrite /IntoNextgen. *)
  (*   (* rewrite /nextgen. *) *)
  (*   intros Hw. *)
  (*   iIntros "P". *)
  (*   rewrite Hw. *)
  (*   apply gen_picked_next_nextgen. *)
  (* Qed. *)

  Global Instance into_nextgen_gen_picked_out γ t :
    IntoNextgen (gen_picked_out γ t) (gen_picked_in γ t).
  Proof. apply gen_picked_next_nextgen. Qed.

  Global Instance into_nextgen_gen_token_used γ :
    IntoNextgen (gen_token_used γ) (gen_token γ).
  Proof. apply gen_token_used_nextgen. Qed.

  Global Instance into_nextgen_gen_own γ m : IntoNextgen (gen_own γ m) _ :=
    own_generational_update γ m.

  Lemma own_generational_update_tok γ a t `{!GenTrans t} :
    gen_token_used γ -∗ gen_picked_out γ t -∗ gen_own γ a -∗
    ⚡==> gen_token γ ∗ gen_own γ (t a) ∗ gen_picked_in γ t.
  Proof.
    iIntros "tok pick own".
    iModIntro.
    iDestruct "own" as (t' cond) "(own & pick')".
    iDestruct (gen_picked_in_agree with "pick pick'") as %->.
    iFrame.
  Qed.

  Lemma nextgen_persistent P : Persistent P → Persistent (⚡==> P).
  Proof.
    rewrite /Persistent.
    intros ?.
    rewrite -nextgen_intuitinistically_1.
    iIntros "H".
    iDestruct (nextgen_mono with "H") as "HH"; first apply H.
    done.
  Qed.

End own_properties.
