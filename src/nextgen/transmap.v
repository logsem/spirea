From nextgen Require Import cmra_morphism_extra.

From self.nextgen Require Import types omega.

Definition map_agree_overlap `{FinMap K M} {A} (m1 m2 : M A) :=
  ∀ (k : K) (i j : A), m1 !! k = Some i → m2 !! k = Some j → i = j.

#[global]
Instance map_agree_overlap_sym `{FinMap K M} {A} :
  Symmetric (map_agree_overlap : relation (M A)).
Proof.
  unfold map_agree_overlap. intros ?? Ha.
  symmetry. eapply Ha; done.
Qed.

Lemma lookup_union_r_overlap `{FinMap K M} {B} (m1 m2 : M B) γ t :
  map_agree_overlap m1 m2 →
  m2 !! γ = Some t →
  (m1 ∪ m2) !! γ = Some t.
Proof.
  intros lap look.
  destruct (m1 !! γ) eqn:eq.
  - apply lookup_union_Some_l.
    rewrite eq.
    f_equiv.
    eapply lap; done.
  - rewrite -look. apply lookup_union_r. done.
Qed.

Lemma map_union_subseteq_l_overlap `{FinMap K M} {B} (m1 m2 : M B) :
  map_agree_overlap m1 m2 →
  m2 ⊆ m1 ∪ m2.
Proof.
  intros lap.
  apply map_subseteq_spec => i x look.
  apply lookup_union_r_overlap; done.
Qed.

(** A [TransMap] contains transformation functions for a subset of ghost
 * names. We use one to represent the transformations that a user has picked.
 * the entries that we have picked generational transformations for. *)
Notation TransMap := (λ Ω, ∀ i, gmap gname (Oc Ω i → Oc Ω i)).

Section transmap.
  Context `{Σ : gFunctors, Ω : gGenCmras Σ}.

  Implicit Types (transmap : TransMap Ω).

  #[global]
  Instance transmap_subseteq : SubsetEq (TransMap Ω) :=
    λ p1 p2, ∀ i, p1 i ⊆ p2 i.

  #[global]
  Instance transmap_subseteq_reflexive : Reflexive transmap_subseteq.
  Proof. intros ??. done. Qed.

  #[global]
  Instance transmap_subseteq_transitive : Transitive transmap_subseteq.
  Proof. intros ??? H1 H2 ?. etrans. - apply H1. - apply H2. Qed.

  #[global]
  Instance transmap_subseteq_preorder : PreOrder transmap_subseteq.
  Proof. constructor; apply _. Qed.

  #[global]
  Instance transmap_subseteq_antisym : AntiSymm eq transmap_subseteq.
  Proof. intros ?? H1 H2. (* apply function_extensionality. lol jk. *) Abort.

  #[global]
  Instance transmap_union : Union (TransMap Ω) :=
    λ p1 p2 i, p1 i ∪ p2 i.

  Lemma transmap_union_subseteq_l transmap1 transmap2 :
    transmap1 ⊆ transmap1 ∪ transmap2.
  Proof. intros ?. apply map_union_subseteq_l. Qed.

  Lemma transmap_union_subseteq_r transmap1 transmap2 :
    (∀ i, map_agree_overlap (transmap1 i) (transmap2 i)) →
    transmap2 ⊆ transmap1 ∪ transmap2.
  Proof. intros ? i. apply map_union_subseteq_l_overlap. done. Qed.

  Lemma transmap_lookup_union_Some_l (m1 m2 : TransMap Ω) i γ t :
    m1 i !! γ = Some t → (m1 ∪ m2) i !! γ = Some t.
  Proof.
    intros look. eapply lookup_union_Some_l in look. apply look.
  Qed.

  Lemma transmap_lookup_union_Some transmap1 transmap2 γ i t :
    (transmap1 ∪ transmap2) i !! γ = Some t →
    transmap1 i !! γ = Some t ∨ transmap2 i !! γ = Some t.
  Proof.
    intros [look|[? look]]%lookup_union_Some_raw; naive_solver.
  Qed.

  (** Every pick in [transmap] is a valid generational transformation and satisfies
  the conditions for that cmra in [Ω]. *)
  Definition transmap_valid transmap :=
    ∀ i γ t, transmap i !! γ = Some t → CmraMorphism t.

  (** A map of picks that for the resource at [idx] and the ghost name [γ] picks
  the generational transformation [t]. *)
  Definition transmap_singleton i (γ : gname)
      (t : Oc Ω i → Oc Ω i) : TransMap Ω :=
    λ j, match decide (i = j) with
           left Heq =>
             (eq_rect _ (λ i, gmap gname (Oc Ω i → _)) {[ γ := t ]} _ Heq)
         | right _ => ∅
         end.

  Definition transmap_singleton_lookup idx γ (f : Oc Ω idx → Oc Ω idx) :
    transmap_singleton idx γ f idx !! γ = Some f.
  Proof.
    rewrite /transmap_singleton.
    case (decide (idx = idx)); last by congruence.
    intros eq'.
    assert (eq' = eq_refl) as ->.
    { rewrite (proof_irrel eq' eq_refl). done. }
    simpl.
    apply lookup_singleton.
  Qed.

  Definition transmap_singleton_dom_index_eq idx γ f :
    dom (transmap_singleton idx γ f idx) = {[ γ ]}.
  Proof.
    rewrite /transmap_singleton.
    case (decide (idx = idx)); last congruence.
    intros [].
    simpl.
    apply dom_singleton_L.
  Qed.

  Definition transmap_singleton_dom_index_neq idx γ f idx' :
    idx ≠ idx' →
    dom (transmap_singleton idx γ f idx') = ∅.
  Proof.
    intros neq.
    rewrite /transmap_singleton.
    case (decide (idx = idx')); first congruence.
    intros ?.
    apply dom_empty_L.
  Qed.

  Definition gen_f_singleton_lookup_Some idx' idx γ γ' f (f' : Oc Ω idx' → _) :
    (transmap_singleton idx γ f) idx' !! γ' = Some f' →
    ∃ (eq : idx' = idx),
      γ = γ' ∧
      f = match eq in (_ = r) return (Oc Ω r → Oc Ω r) with eq_refl => f' end.
  Proof.
    rewrite /transmap_singleton.
    case (decide (idx = idx')); last first.
    { intros ?. rewrite lookup_empty. inversion 1. }
    intros ->.
    simpl.
    intros [-> ->]%lookup_singleton_Some.
    exists eq_refl.
    done.
  Qed.

  Lemma transmap_valid_union (picks1 picks2 : TransMap Ω) :
    transmap_valid picks1 →
    transmap_valid picks2 →
    transmap_valid (picks1 ∪ picks2).
  Proof.
    intros p1 p2.
    intros i γ t.
    intros [look | [? look]]%lookup_union_Some_raw.
    - apply p1 in look. done.
    - apply p2 in look. done.
  Qed.

End transmap.

Equations transmap_insert_go `{Ω : gGenCmras Σ} (transmap : TransMap Ω)
    (id : ggid Ω) (γ : gname)
    (pick : Oc Ω id → Oc Ω id)
    (id' : ggid Ω) : gmap gname (Oc Ω id' → Oc Ω id') :=
| transmap, _, γ, pick, id', with decide (id = id') => {
  | left eq_refl => <[ γ := pick ]>(transmap id')
  | right _ => transmap id'
}.

Definition transmap_insert `{Ω : gGenCmras Σ} transmap id γ pick : TransMap Ω :=
  transmap_insert_go transmap id γ pick.

Section transmap_insert.
  Context `{Σ : gFunctors, Ω : gGenCmras Σ}.

  Implicit Types (transmap : TransMap Ω).

  Lemma transmap_insert_lookup transmap id γ t  :
    (transmap_insert transmap id γ t) id !! γ = Some t.
  Proof.
    rewrite /transmap_insert.
    rewrite transmap_insert_go_equation_1.
    destruct (decide (id = id)) as [eq | neq]; last congruence.
    assert (eq = eq_refl) as ->.
    { rewrite (proof_irrel eq eq_refl). done. }
    simpl.
    rewrite lookup_insert. done.
  Qed.

  Lemma transmap_insert_lookup_ne transmap id1 γ1 t id2 γ2 :
    id1 ≠ id2 ∨ γ1 ≠ γ2 →
    (transmap_insert transmap id1 γ1 t) id2 !! γ2 = transmap id2 !! γ2.
  Proof.
    intros neq.
    rewrite /transmap_insert.
    rewrite transmap_insert_go_equation_1.
    destruct (decide (id1 = id2)) as [eq | neq2]; last done.
    destruct neq as [neq | neq]; first congruence.
    subst. simpl.
    rewrite lookup_insert_ne; done.
  Qed.

  Lemma transmap_insert_subseteq_r i γ t transmap1 transmap2 :
    transmap1 i !! γ = None →
    transmap1 ⊆ transmap2 →
    transmap1 ⊆ transmap_insert transmap2 i γ t.
  Proof.
    intros look sub.
    intros i'.
    apply map_subseteq_spec => γ' t' look'.
    destruct (decide (i = i' ∧ γ = γ')) as [[-> ->]|Hneq].
    - congruence.
    - rewrite transmap_insert_lookup_ne.
      * specialize (sub i').
        rewrite map_subseteq_spec in sub.
        apply sub.
        done.
      * apply not_and_r in Hneq; done.
  Qed.

  Lemma transmap_valid_singleton id γ t `{!CmraMorphism t} :
    transmap_valid (transmap_singleton id γ t).
  Proof.
    intros id' ??. unfold transmap_singleton.
    destruct (decide (id = id')) as [eq2|] eqn:eq; last done.
    destruct eq2.
    simpl.
    intros [-> <-]%lookup_singleton_Some. done.
  Qed.

  Lemma transmap_valid_insert map id γ t :
    CmraMorphism t →
    transmap_valid map →
    transmap_valid (transmap_insert map id γ t).
  Proof.
    intros gt val.
    intros id' γ' t'.
    destruct (path_equal_or_different id id' γ γ') as [H|H].
    - destruct H as [-> ->].
      rewrite transmap_insert_lookup.
      intros [= ->].
      done.
    - rewrite transmap_insert_lookup_ne; last done.
      apply (val id' γ').
  Qed.

End transmap_insert.
