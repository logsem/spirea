(* A collection of a few fairly general constructions and lemmas. *)

From stdpp Require Import countable numbers gmap fin_maps list.
From iris.bi Require Import big_op monpred.
From iris.algebra Require Import cmra updates gmap agree big_op auth.
From iris.proofmode Require Import tactics.
Import interface.bi derived_laws.bi derived_laws_later.bi.

From iris.bi Require Import derived_laws_later.

(* We define our own relation. Workaround for universe issues in stdpp and Iris. *)
Definition relation2 A := A -> A -> Prop.

Lemma auth_auth_grow {A : ucmra} (a a' : A) :
  ✓ a' → a ≼ a' → ● a ~~> ● a'.
Proof.
  intros val [a'' eq]. rewrite eq.
  apply (auth_update_auth _ _ a'').
  rewrite comm.
  rewrite -{2}(right_id _ _ a'').
  apply op_local_update => n.
  rewrite comm -eq.
  intros ?.
  apply cmra_valid_validN.
  done.
Qed.

Lemma singleton_included_insert `{Countable K} {A : cmra} (k : K) (a a' : A) (m : gmap K A) :
  a ≼ a' → {[k := a]} ≼ <[k:=a']> m.
Proof.
  intros le.
  apply singleton_included_l.
  exists a'.
  split. - by rewrite lookup_insert. - apply Some_included. right. done.
Qed.

Lemma singleton_included_look {A : cmra} `{Countable K} (m : gmap K A) (k : K) (a b : A) :
  m !! k = Some b → a ≼ b → {[k := a]} ≼ m.
Proof.
  intros L incl.
  apply singleton_included_l.
  eexists b. rewrite L. split; first reflexivity.
  by apply Some_included_2.
Qed.

Lemma map_Forall_subseteq `{Countable K} {A} (m1 m2 : gmap K A) (P : K → A → Prop) :
  m1 ⊆ m2 → map_Forall P m2 → map_Forall P m1.
Proof.
  rewrite map_subseteq_spec.
  rewrite /map_Forall.
  intros sub all2 i x ?.
  apply all2.
  apply sub.
  done.
Qed.

Lemma map_Forall_singleton `{FinMap K M} {A} (j : K) (y : A) (P : K → A → Prop) :
  P j y ↔
  map_Forall P ({[j := y]} : M A).
Proof.
  split; intros HP.
  - by intros i x [-> ->]%lookup_singleton_Some.
  - apply HP, lookup_singleton.
Qed.

Lemma map_Forall_singleton' `{FinMap K M} {A} (j : K) (y : A) (P : K → A → Prop) :
  P j y ↔
  map_Forall (λ (i : K) (x : A), P i x) ({[j := y]} : M A).
Proof.
  split; intros HP.
  - by intros i x [-> ->]%lookup_singleton_Some.
  - apply HP, lookup_singleton.
Qed.

Lemma option_not_included_None {A : cmra} (x : A) : ¬ (Some x ≼ None).
Proof. intros [[y|] eq]; inversion eq. Qed.

Lemma to_agree_fmap {A : ofe} `{!LeibnizEquiv A} (a b : gmap nat A) :
  a ⊆ b ↔ to_agree <$> a ≼ to_agree <$> b.
Proof.
  rewrite lookup_included.
  rewrite  map_subseteq_spec.
  setoid_rewrite lookup_fmap.
  split.
  - intros sub.
    intros i.
    destruct (a !! i) eqn:eq.
    2: { eexists _. rewrite left_id. reflexivity. }
    rewrite (sub i o); done.
  - intros incl.
    intros i.
    destruct (a !! i) eqn:eq.
    2: { done. }
    intros x [= ->].
    specialize (incl i).
    setoid_rewrite eq in incl.
    simpl in incl.
    destruct (b !! i) eqn:eq'.
    2: { apply option_not_included_None in incl. done. }
    simpl in incl.
    setoid_rewrite Some_included_total in incl.
    setoid_rewrite to_agree_included in incl.
    apply leibniz_equiv in incl.
    setoid_rewrite incl.
    done.
Qed.

Section map_zip_with.
  Context `{FinMap K M}.

  Lemma map_zip_with_mono {A B C}
        (f : A → B → C) (mx1 mx2 : M A) (my1 my2 : M B) :
    mx1 ⊆ mx2 →
    my1 ⊆ my2 →
    map_zip_with f mx1 my1 ⊆ map_zip_with f mx2 my2.
  Proof.
    rewrite !map_subseteq_spec => sub1 sub2 k x.
    rewrite !map_lookup_zip_with_Some.
    intros (? & ? & ? & ? & ?).
    eexists _, _.
    split_and!; try naive_solver.
  Qed.

  (* Upstream this. *)
  Lemma dom_map_zip_with_fst `{FinMapDom K M D} {A B C}
        (f : A → B → C) (ma : M A) (mb : M B) : dom D (map_zip_with f ma mb) ⊆ dom D ma.
  Proof.
    intros ?. rewrite 2!elem_of_dom. intros [? ?%map_lookup_zip_with_Some].
    naive_solver.
  Qed.

  Lemma dom_map_zip_with_snd `{FinMapDom K M D} {A B C}
        (f : A → B → C) (ma : M A) (mb : M B) : dom D (map_zip_with f ma mb) ⊆ dom D mb.
  Proof. rewrite map_zip_with_flip. apply dom_map_zip_with_fst. Qed.

  Lemma dom_map_zip_with_eq_l `{FinMapDom K M D} {A B C}
        (f : A → B → C) (ma : M A) (mb : M B) :
    dom D ma ⊆ dom D mb →
    dom D (map_zip_with f ma mb) ≡ dom D ma.
  Proof. rewrite dom_map_zip_with. set_solver. Qed.

  Lemma dom_map_zip_with_eq_r `{FinMapDom K M D} {A B C}
        (f : A → B → C) (ma : M A) (mb : M B) :
    dom D mb ⊆ dom D ma →
    dom D (map_zip_with f ma mb) ≡ dom D mb.
  Proof. rewrite dom_map_zip_with. set_solver. Qed.

  Lemma dom_eq_alt `{FinMapDom K M D} {A B} (m1 : M A) (m2 : M B) :
    (∀ k : K, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) ↔
    (dom D m1 ≡ dom D m2).
  Proof. setoid_rewrite <- elem_of_dom. rewrite set_equiv. done. Qed.

  Lemma dom_eq_alt_L `{FinMapDom K M D} `{!LeibnizEquiv D} {A B} (m1 : M A) (m2 : M B) :
    (∀ k : K, is_Some (m1 !! k) ↔ is_Some (m2 !! k)) ↔
    (dom D m1 = dom D m2).
  Proof. unfold_leibniz. apply dom_eq_alt. Qed.

  (* Could be upstreamed. *)
  Lemma dom_omap_id `{FinMapDom K M D} `{!LeibnizEquiv D} {A B} (f : A → option B) (m : M A) :
    map_Forall (λ _ v, is_Some (f v)) m → dom D (omap f m) ≡ dom D m.
  Proof.
    intros Ha. apply set_equiv. intros k.
    rewrite !elem_of_dom. unfold is_Some. setoid_rewrite lookup_omap_Some.
    split; first naive_solver.
    intros [? Hl].
    eapply map_Forall_lookup_1 in Ha as [??]; last done.
    eexists _, _. done.
  Qed.

End map_zip_with.

Definition restrict `{FinMap K M, ElemOf K D, !RelDecision (∈@{D})} {A} (s : D) (m : M A) :=
  filter (λ '(k, _), k ∈ s) m.

Section restrict.
  Context `{FinMap K M, ElemOf K D}.
  Context `{!RelDecision (∈@{D})}.
  Context {A : Type}.
  Implicit Types (s : D) (m : M A) (k : K).

  Lemma restrict_lookup_elem_of k s m :
    k ∈ s → restrict s m !! k = m !! k.
  Proof.
    intros elem.
    destruct (m !! k) eqn:look.
    - by apply map_filter_lookup_Some.
    - apply map_filter_lookup_None. by left.
  Qed.

  Lemma restrict_lookup_not_elem_of k s m :
    k ∉ s → restrict s m !! k = None.
  Proof.
    intros elem.
    apply map_filter_lookup_None.
    right. intros ??. done.
  Qed.

  Lemma restrict_lookup_None_lookup k s m :
    m !! k = None → restrict s m !! k = None.
  Proof. intros elem. apply map_filter_lookup_None. left. done. Qed.

  Lemma restrict_lookup_Some (s : D) (m : M A) (k : K) (x : A) :
    restrict s m !! k = Some x ↔ (m !! k = Some x) ∧ k ∈ s.
  Proof. by rewrite map_filter_lookup_Some. Qed.

  Lemma restrict_lookup_Some_2 (s : D) (m : M A) (k : K) (x : A) :
    m !! k = Some x → k ∈ s → restrict s m !! k = Some x.
  Proof. by rewrite restrict_lookup_Some. Qed.

  Lemma restrict_subseteq s m : restrict s m ⊆ m.
  Proof. rewrite /restrict. apply map_filter_subseteq. Qed.

  Lemma restrict_insert k s v m :
    k ∈ s →
    restrict s (<[k := v]>m) = <[k:= v]>(restrict s m).
  Proof. intros elm. by apply map_filter_insert_True. Qed.

End restrict.

Section restrict_set.
  Context `{FinMap K M, SemiSet K D}.
  (* Context `{FinMapDom K M D}. *)
  Context `{!RelDecision (∈@{D})}.
  Context {A : Type}.
  Implicit Types (s : D) (m : M A) (k : K).

  Lemma restrict_lookup_union_eq l t s m :
    l ∉ s →
    restrict (s ∪ t) m !! l = restrict t m !! l.
  Proof.
    intros elem.
    destruct (decide (l ∈ t)).
    - rewrite !restrict_lookup_elem_of; auto with set_solver.
    - rewrite !restrict_lookup_not_elem_of; auto with set_solver.
  Qed.

  Lemma restrict_empty (m : M A) : restrict (D := D) ∅ m = ∅.
  Proof. apply map_filter_empty_iff. intros ???. set_solver. Qed.

  Lemma restrict_insert_union k s v m :
    restrict ({[k]} ∪ s) (<[k := v]>m) = <[k:= v]>(restrict s m).
  Proof.
    rewrite restrict_insert; last set_solver.
    apply map_eq. intros l.
    case (decide (k = l)); intros eq.
    - subst. by rewrite !lookup_insert.
    - rewrite !lookup_insert_ne; try apply eq.
      eapply restrict_lookup_union_eq.
      set_solver.
  Qed.

  Lemma restrict_insert_not_elem k s v m :
    k ∉ s →
    restrict s (<[ k := v ]>m) = restrict s m.
  Proof. intros elm. by apply map_filter_insert_not. Qed.

End restrict_set.

Section restrict_dom.
  Context `{FinMapDom K M D}.
  Context `{!RelDecision (∈@{D})}.
  Context {A : Type}.
  Implicit Types (s : D) (m : M A) (k : K).

  Lemma restrict_dom s m : dom _ (restrict s m) ≡ s ∩ dom _ m.
  Proof.
    apply dom_filter => i.
    rewrite elem_of_intersection.
    rewrite elem_of_dom.
    rewrite /is_Some.
    naive_solver.
  Qed.

  Lemma restrict_dom_subseteq s m : dom _ (restrict s m) ⊆ s.
  Proof. rewrite restrict_dom. set_solver. Qed.

  Lemma restrict_superset_id (s : D) (m : M A) :
    dom _ m ⊆ s → restrict s m = m.
  Proof.
    rewrite /restrict.
    intros Hsub.
    apply map_filter_id.
    intros i x look%elem_of_dom_2.
    set_solver.
  Qed.

  Lemma restrict_id (s : D) (m : M A) : dom _ m = s → restrict s m = m.
  Proof. intros eq. apply restrict_superset_id. set_solver. Qed.

  Lemma restrict_union (s1 s2 : D) (m : M A) :
    restrict s1 m ∪ restrict s2 m = restrict (s1 ∪ s2) m.
  Proof.
    rewrite /restrict. apply map_eq. intros i.
    destruct (filter (λ '(k, _), k ∈ s1 ∪ s2) m !! i) eqn:look.
    - apply map_filter_lookup_Some in look as [ha elem].
      destruct (decide (i ∈ s1)).
      + apply lookup_union_Some_l. apply map_filter_lookup_Some. naive_solver.
      + apply lookup_union_Some_raw. right.
        split.
        * apply map_filter_lookup_None_2. right. intros _ _. done.
        * apply map_filter_lookup_Some_2; first done. set_solver.
    - apply map_filter_lookup_None in look as [look|notElem].
      + apply lookup_union_None.
        split; apply map_filter_lookup_None_2; by left.
      + apply lookup_union_None.
        split; apply map_filter_lookup_None; right; set_solver.
  Qed.

  Lemma disjoint_weaken s1 s1' s2 s2' :
    s1' ## s2' → s1 ⊆ s1' → s2 ⊆ s2' → s1 ## s2.
  Proof. intros disj sub1 sub2. set_solver. Qed.

  Lemma restrict_disjoint s1 s2 m : s1 ## s2 → restrict s1 m ##ₘ restrict s2 m.
  Proof.
    intros dis.
    apply map_disjoint_dom_2.
    eapply disjoint_weaken; first apply dis; rewrite restrict_dom; set_solver.
  Qed.

  Lemma restrict_dom_subset (s : D) (m : M A) :
    s ⊆ dom _ m → dom _ (restrict s m) ≡ s.
  Proof. rewrite restrict_dom. set_solver. Qed.

  Lemma restrict_disjoint_union s1 s2 m :
    s1 ∪ s2 = dom _ m →
    m = restrict s1 m ∪ restrict s2 m.
  Proof.
    intros domEq.
    rewrite restrict_union.
    rewrite domEq.
    symmetry.
    apply restrict_id.
    done.
  Qed.

End restrict_dom.

Section restrict_leibniz.
  Context `{FinMapDom K M D}.
  Context `{!RelDecision (∈@{D})}.
  Context {A : Type}.
  Context `{!LeibnizEquiv D}.

  Lemma restrict_dom_L (s : D) (m : M A) : dom _ (restrict s m) = s ∩ dom _ m.
  Proof. unfold_leibniz. apply restrict_dom. Qed.

  Lemma restrict_dom_subset_L (s : D) (m : M A) :
    s ⊆ dom _ m → dom _ (restrict s m) = s.
  Proof. unfold_leibniz. apply restrict_dom_subset. Qed.

End restrict_leibniz.

Lemma valid_to_agree_fmap `{Countable K} {B : ofe} (m : gmap K B) :
  ✓ (to_agree <$> m : gmapUR _ _).
Proof. intros ℓ. rewrite lookup_fmap. by case (m !! ℓ). Qed.

Section big_sepM.
  Context {PROP : bi}.
  (* Context `{BiAffine PROP}. *)
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  (* Lemma big_sepM_impl Φ Ψ m : *)
  (*   ([∗ map] k↦x ∈ m, Φ k x) -∗ *)
  (*   □ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x -∗ Ψ k x) -∗ *)
  (*   [∗ map] k↦x ∈ m, Ψ k x. *)
  (* Proof. *)
  (*   apply wand_intro_l. rewrite big_sepM_intro -big_sepM_sep. *)
  (*   by setoid_rewrite wand_elim_l. *)
  (* Qed. *)

  Lemma big_sepM_thread_resource Φ m R :
    R ∗ ([∗ map] k↦x ∈ m, R -∗ R ∗ Φ k x) ⊣⊢ R ∗ ([∗ map] k↦x ∈ m, Φ k x).
  Proof.
    induction m as [|i x m ? IH] using map_ind.
    - rewrite 2!big_sepM_empty. naive_solver.
    - rewrite big_sepM_insert; last done.
      rewrite assoc.
      rewrite (comm _ R).
      rewrite -assoc.
      rewrite IH.
      rewrite big_sepM_insert; last done.
      apply (anti_symm _).
      * rewrite assoc.
        rewrite wand_elim_l.
        rewrite -assoc.
        done.
      * rewrite assoc.
        rewrite (comm _ R).
        rewrite -assoc.
        apply sep_mono_l.
        apply wand_intro_r.
        done.
  Qed.

  Lemma big_sepM_thread_resource_1 Φ m R :
    R -∗ ([∗ map] k↦x ∈ m, R -∗ R ∗ Φ k x) -∗ R ∗ ([∗ map] k↦x ∈ m, Φ k x).
  Proof. apply wand_intro_r. rewrite big_sepM_thread_resource. done. Qed.

  Lemma big_sepM_thread_resource_2 Φ m R :
    R -∗ ([∗ map] k↦x ∈ m, Φ k x) -∗ R ∗ ([∗ map] k↦x ∈ m, R -∗ R ∗ Φ k x).
  Proof. apply wand_intro_r. rewrite big_sepM_thread_resource. done. Qed.

End big_sepM.

Lemma big_sepM_impl_dom_subseteq_with_resource {PROP : bi} `{Countable K} {A B : Type}
    R (Φ : K → A → PROP) (Ψ : K → B → PROP) (m1 : gmap K A) (m2 : gmap K B) :
  dom (gset _) m2 ⊆ dom _ m1 →
  R -∗
  ([∗ map] k↦x ∈ m1, Φ k x) -∗
  □ (∀ (k : K) (x : A) (y : B),
      ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ →
      R -∗ Φ k x -∗ R ∗ Ψ k y) -∗
  R ∗
  ([∗ map] k↦y ∈ m2, Ψ k y) ∗
  ([∗ map] k↦x ∈ filter (λ '(k, _), m2 !! k = None) m1, Φ k x).
Proof.
  iIntros (sub) "R map #impl".
  iDestruct (big_sepM_thread_resource_2 with "R map") as "[R map]".
  rewrite assoc.
  rewrite -(big_sepM_thread_resource _ _ R).
  rewrite -assoc.
  iDestruct (big_sepM_impl_dom_subseteq with "map []") as "[$ B]".
  { done. }
  { iIntros "!>" (k x y look1 look2) "w R".
    iDestruct ("w" with "R") as "[R H]".
    iApply ("impl" $! _ _ _ look1 look2 with "R H"). }
  iApply (big_sepM_thread_resource_1 with "R B").
Qed.

Section big_sepM2.
  Context {PROP : bi}.
  Context `{Countable K} {A B : Type}.
  Implicit Types Φ Ψ : K → A → B → PROP.

  Lemma map_dom_eq_lookup_Some {V W} (a : gmap K V) (b : gmap K W) v k :
    dom (gset _) a = dom (gset _) b →
    b !! k = Some v →
    is_Some (a !! k).
  Proof.
    intros domEq look. rewrite -elem_of_dom domEq elem_of_dom. done.
  Qed.

  Lemma map_dom_eq_lookup_None {V W} (a : gmap K V) (b : gmap K W) k :
    dom (gset _) a = dom (gset _) b →
    b !! k = None →
    a !! k = None.
  Proof.
    intros domEq look. rewrite -not_elem_of_dom domEq not_elem_of_dom. done.
  Qed.

  Lemma big_sepM2_empty_either m1 m2 Φ :
    m1 = ∅ ∨ m2 = ∅ →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) ⊢ emp.
  Proof.
    intros disj.
    rewrite big_sepM2_eq /big_sepM2_def. apply pure_elim_l => Hl.
    assert (m1 = ∅ ∧ m2 = ∅) as [-> ->].
    { apply dom_eq_alt_L in Hl.
      destruct disj as [-> | ->].
      * split.
        + set_solver.
        + apply dom_empty_iff_L. rewrite dom_empty_L in Hl. done.
      * split.
        + apply dom_empty_iff_L. rewrite dom_empty_L in Hl. done.
        +  reflexivity. }
    rewrite map_zip_with_empty.
    rewrite big_sepM_empty. done.
  Qed.

  (* Lemma big_sepM_bupd m1 m2 Φ : *)
  Lemma big_sepM2_bupd `{BiBUpd PROP} m1 m2 Φ :
    ([∗ map] k ↦ x1;x2 ∈ m1;m2, |==> Φ k x1 x2) -∗
    |==> ([∗ map] k ↦ x1;x2 ∈ m1;m2, Φ k x1 x2).
  Proof.
    rewrite 2!big_sepM2_alt big_sepM_bupd. apply pure_elim_l => ?.
    rewrite pure_True; [|assumption]. by rewrite left_id.
  Qed.

  Lemma big_sepM_exist_r Φ m1 :
    ([∗ map] k ↦ x1 ∈ m1, ∃ x2, Φ k x1 x2) ⊣⊢
      ∃ m2, ([∗ map] k ↦ x1; x2 ∈ m1;m2, Φ k x1 x2).
  Proof.
    induction m1 as [|i x m1' ? IH] using map_ind.
    - rewrite big_sepM_empty.
      apply (anti_symm _).
      * rewrite -(exist_intro ∅). rewrite big_sepM2_empty. done.
      * apply exist_elim.
        intros m2. apply big_sepM2_empty_either. left. done.
    - rewrite big_sepM_insert; last done.
      rewrite IH.
      apply (anti_symm _).
      * rewrite sep_exist_r. apply exist_elim => b.
        rewrite sep_exist_l. apply exist_elim => m2'.
        rewrite -(exist_intro (<[i:=b]>m2')).
        eapply pure_elim. { rewrite big_sepM2_dom. apply: sep_elim_r. }
        intros dom.
        rewrite big_sepM2_insert; [done|done|].
        by rewrite -not_elem_of_dom -dom not_elem_of_dom.
      * apply exist_elim => m2.
        eapply pure_elim; first apply big_sepM2_dom. intros dom.
        destruct (m2 !! i) as [|y] eqn:Hlook.
        2: {
          apply not_elem_of_dom in Hlook.
          rewrite -dom in Hlook.
          set_solver. }
        rewrite big_sepM2_delete; try done.
        2: { apply lookup_insert. }
        f_equiv.
        + apply exist_intro.
        + rewrite delete_insert; last done. apply exist_intro.
  Qed.

  (* Lemma big_sepM2_thread_resource Φ m1 m2 R : *)
  (*   R ∗ ([∗ map] k↦x1;x2 ∈ m1;m2, R -∗ Φ k x1 x2 ∗ R) ⊣⊢ *)
  (*   R ∗ ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2). *)
  (* Proof. *)
  (*   rewrite 2!big_sepM2_alt. *)
  (*   iSplit. *)
  (*   - iIntros "R [$ M]". *)
  (*   rewrit (big_sepM_thread_resource with "R M"). *)
  (*   iApply (big_sepM_thread_resource with "R M"). *)
  (* Qed. *)

  Lemma big_sepM2_impl_dom_subseteq_with_resource `{!BiAffine PROP}
        Φ Ψ m1 m2 n1 n2 R :
    dom (gset _) n1 ⊆ dom (gset _) m1 →
    dom (gset _) n1 = dom (gset _) n2 →
    R -∗
    ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2) -∗
    □ (∀ (k : K) x1 x2 y1 y2,
        ⌜m1 !! k = Some x1⌝ → ⌜m2 !! k = Some x2⌝ →
        ⌜n1 !! k = Some y1⌝ → ⌜n2 !! k = Some y2⌝ → R -∗ Φ k x1 x2 -∗ R ∗ Ψ k y1 y2) -∗
    R ∗ ([∗ map] k↦y1;y2 ∈ n1;n2, Ψ k y1 y2).
  Proof.
    iIntros (sub1 domEq).
    rewrite !big_sepM2_alt.
    iIntros "R [%impl sep] #impl".
    apply dom_eq_alt_L in impl.
    rewrite persistent_and_sep.
    rewrite comm. rewrite -assoc.
    iSplit. { iPureIntro. apply dom_eq_alt_L. congruence. }
    iDestruct (big_sepM_impl_dom_subseteq_with_resource with "R sep []")
      as "(A & $ & C)".
    { rewrite 2!dom_map_zip_with. rewrite -domEq -impl. set_solver. }
    iIntros "!>" (k [??] [??] [l1 l2]%map_lookup_zip_Some [l3 l4]%map_lookup_zip_Some) "R phi".
    simpl in *.
    iApply ("impl" with "[//] [//] [//] [//] R phi").
    iFrame.
  Qed.

  (* This could be upstreamed but we'd need to drop the affine requirement and
  rewrite the proof to not use the proofmode. *)
  Lemma big_sepM2_impl_dom_subseteq {C D} `{!BiAffine PROP}
        Φ (Ψ : K → C → D → _) m1 m2 n1 n2 :
    dom (gset _) n1 ⊆ dom (gset _) m1 →
    dom (gset _) n1 = dom (gset _) n2 →
    ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2) -∗
    □ (∀ (k : K) x1 x2 y1 y2,
        ⌜m1 !! k = Some x1⌝ → ⌜m2 !! k = Some x2⌝ →
        ⌜n1 !! k = Some y1⌝ → ⌜n2 !! k = Some y2⌝ → Φ k x1 x2 -∗ Ψ k y1 y2) -∗
    ([∗ map] k↦y1;y2 ∈ n1;n2, Ψ k y1 y2).
  Proof.
    iIntros (sub1 domEq).
    rewrite !big_sepM2_alt.
    iIntros "[%impl sep] #impl".
    assert (dom _ m1 = dom (gset _) m2) as domEq2.
    { rewrite set_eq. setoid_rewrite elem_of_dom. done. }
    iSplit. { iPureIntro. intros k. rewrite -!elem_of_dom domEq. done. }
    iDestruct (big_sepM_impl_dom_subseteq with "sep []") as "[$ H]".
    { etrans; first apply dom_map_zip_with_fst.
      rewrite dom_map_zip_with. rewrite -domEq2. set_solver. }
    { iModIntro.
      iIntros (? [??] [??]).
      iIntros ([??]%map_lookup_zip_Some).
      iIntros ([??]%map_lookup_zip_Some).
      iApply "impl"; eauto. }
  Qed.

  Lemma big_sepM2_impl_subseteq `{!BiAffine PROP} (m1 n1 : gmap K A) (m2 n2 : gmap K B) Φ :
    n1 ⊆ m1 →
    n2 ⊆ m2 →
    dom (gset _) n1 ≡ dom _ n2 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
    [∗ map] k↦y1;y2 ∈ n1;n2, Φ k y1 y2.
  Proof.
    rewrite 2!big_sepM2_alt.
    iIntros (sub sub' eq) "[%impl map]".
    iSplit.
    - setoid_rewrite <- elem_of_dom. rewrite -set_equiv. done.
    - iDestruct (big_sepM_impl_dom_subseteq with "map []") as "[$ temp]".
      { rewrite 2!dom_map_zip_with.
        apply subseteq_dom in sub.
        apply subseteq_dom in sub'.
        set_solver. }
      iModIntro.
      setoid_rewrite map_subseteq_spec in sub.
      setoid_rewrite map_subseteq_spec in sub'.
      iIntros (? [??] [??] [? ?]%map_lookup_zip_Some
               [look1%sub look2%sub']%map_lookup_zip_Some).
      naive_solver.
  Qed.

  (* Lemma big_sepM2_insert_override Φ m1 m2 i x1 x2 x1' x2' : *)
  (*   m1 !! i = Some x1 → *)
  (*   m2 !! i = Some x2 → *)
  (*   (Φ i x1 x2 ⊣⊢ Φ i x1' x2') → *)
  (*   ([∗ map] k↦y1;y2 ∈ <[i:=x1']>m1; <[i:=x2']>m2, Φ k y1 y2) ⊣⊢ *)
  (*     ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2). *)
  (* Proof. *)
  (*   intros Hm1 Hm2 Hp. rewrite big_sepM2_eq /big_sepM2_def -map_insert_zip_with. *)
  (*   rewrite big_sepM_insert_override. *)
  (*   2: { by rewrite map_lookup_zip_with Hm1 Hm2. } *)
  (*   2: { done. } *)
  (*   apply (anti_symm _). *)
  (*   - rewrite pure_intro. *)
  (*   -  *)
  (*   split. *)
  (*   rewrite pure_True. 2: { set_solver.. } *)
  (* Qed. *)

  Lemma big_sepM2_update Φ m1 m2 i x1 x2 x1' x2' :
    m1 !! i = Some x1 →
    m2 !! i = Some x2 →
    ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2) -∗
    (Φ i x1 x2 -∗ Φ i x1' x2') -∗
    ([∗ map] k↦y1;y2 ∈ <[i:=x1']> m1; <[i:=x2']> m2, Φ k y1 y2).
  Proof.
    iIntros (look1 look2) "H I".
    iDestruct (big_sepM2_insert_acc with "H") as "[P I2]"; eauto.
    iSpecialize ("I" with "P").
    iApply "I2".
    done.
  Qed.

  Lemma big_sepM2_update_right m1 m2 k v__a v1 v2 (Φ : K → A → B → PROP) :
    m1 !! k = Some v__a →
    m2 !! k = Some v1 →
    ([∗ map] k↦a;b ∈ m1;m2, Φ k a b) -∗
    (Φ k v__a v1 -∗ Φ k v__a v2) -∗
    ([∗ map] k↦a;b ∈ m1;<[k:=v2]>m2, Φ k a b).
  Proof.
    intros ??. rewrite <- (insert_id m1 k v__a) at 2; eauto.
    iApply big_sepM2_update; eauto.
  Qed.

  Lemma big_sepM2_update_left m1 m2 k v__a v__b v2 (Φ : K → A → B → PROP) :
    m1 !! k = Some v__a →
    m2 !! k = Some v__b →
    ([∗ map] k↦a;b ∈ m1;m2, Φ k a b) -∗
    (Φ k v__a v__b -∗ Φ k v2 v__b) -∗
    ([∗ map] k↦a;b ∈ <[k:=v2]>m1;m2, Φ k a b).
  Proof.
    intros ??. rewrite <- (insert_id m2 k v__b) at 2; eauto.
    iApply big_sepM2_update; eauto.
  Qed.

  Lemma monPred_at_big_sepM2 {I : biIndex} `{Countable K}
        i (Φ : K → A → B → monPred I PROP) (m1 : gmap K A) (m2 : gmap K B) :
    ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2) i ⊣⊢ [∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2 i.
  Proof.
    by rewrite 2!big_sepM2_alt monPred_at_and monPred_at_pure monPred_at_big_sepM.
  Qed.

End big_sepM2.

Lemma big_sepM_exist_l {PROP : bi} {K A B} `{Countable K}
      (Φ : K → A → B → PROP) (m2 : gmap K B) :
  ([∗ map] k ↦ x2 ∈ m2, ∃ x1, Φ k x1 x2) ⊣⊢
    ∃ m1, ([∗ map] k ↦ x1; x2 ∈ m1;m2, Φ k x1 x2).
Proof. setoid_rewrite big_sepM2_flip. apply big_sepM_exist_r. Qed.

(* Applicative notation. *)
Definition mapply {A B} `{MBind M, FMap M} (mf : M (A → B)) (a : M A) :=
  mf ≫= (λ f, f <$> a).

Notation "mf <*> a" := (mapply mf a) (at level 61, left associativity).
