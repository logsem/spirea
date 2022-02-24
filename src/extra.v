(* A collection of a few fairly general constructions and lemmas. In other
words, our own little (std++)++. *)

From stdpp Require Import countable numbers gmap fin_maps list.
From iris.bi Require Import big_op.
From iris.algebra Require Import cmra updates gmap agree big_op auth.
From iris.proofmode Require Import tactics.
Import interface.bi derived_laws.bi derived_laws_later.bi.

From iris.bi Require Import derived_laws_later.

(* We define our own relation. Workaround for universe issues in stdpp and Iris. *)
Definition relation2 A := A -> A -> Prop.

(** The map [m] is undefined for all natural numbers greater than [t]. *)
Definition map_no_later`{FinMap nat M} {A : Type} (m : M A) t :=
  ∀ t', t < t' → m !! t' = None.

(* Lemmas about finite maps of natural numbers. *)
Section nat_map.
  Context `{FinMap nat M} {A : Type}.

  Implicit Types m : M A.

  (** Expresses that the map [m] contains, in order, the values [xs] from the
  indeces starting at exactly [lo] ending at exactly [hi]. *)
  Fixpoint map_slice m (lo hi : nat) (xs : list A) :=
    match xs with
    | [] => False
    | [x] => m !! hi = Some x ∧ lo = hi
    | x :: xs =>
      m !! lo = Some x ∧
      ∃ lo',
        lo < lo' ∧
        (∀ lo'', lo < lo'' < lo' → m !! lo'' = None) ∧ (* There are no elements in between. *)
        map_slice m lo' hi xs
    end.

  Lemma map_slice_lt m lo hi xs : map_slice m lo hi xs → lo ≤ hi.
  Proof.
    generalize dependent lo.
    induction xs as [|x1 xs IH]; first done.
    destruct xs as [|x2 xs]. { naive_solver. }
    intros lo (look & lo' & ? & between & slice).
    apply IH in slice. lia.
  Qed.

  Lemma map_slice_lookup_between m lo hi xs t x :
    map_slice m lo hi xs → lo ≤ t ≤ hi → m !! t = Some x → x ∈ xs.
  Proof.
    generalize dependent m. generalize dependent lo. generalize dependent hi.
    induction xs as [|x1 xs IH]; first done. (* Base case is trivial. *)
    intros hi lo m.
    (* We destruct [xs] to handle the special case where the list is a singleton. *)
    destruct xs as [|x2 xs].
    - intros [mLook ->] ? ?.
      apply elem_of_list_singleton.
      assert (t = hi) as -> by lia.
      congruence.
    - intros (mLook & lo' & ? & between & slice) ? ?.
      assert (lo = t ∨ lo < t) as [eq | gt] by lia.
      * simplify_eq. apply elem_of_list_here.
      * apply elem_of_list_further.
        assert (t < lo' ∨ lo' ≤ t) as [lt | ge] by lia.
        { assert (m !! t = None) by (apply between; lia). congruence. }
        eapply IH; [apply slice | lia | done].
  Qed.

  Lemma map_slice_lookup_lo m lo hi xs :
    map_slice m lo hi xs → m !! lo = xs !! 0.
  Proof.
    destruct xs as [|x xs]; [done|]. simpl.
    destruct xs.
    - intros [? ->]. done.
    - intros [? _]. done.
  Qed.

  Lemma map_slice_nonempty m lo hi xs : map_slice m lo hi xs → xs ≠ [].
  Proof. by destruct xs. Qed.

  Lemma map_slice_lookup_hi m lo hi xs :
    map_slice m lo hi xs → m !! hi = last xs.
  Proof.
    generalize dependent lo. generalize dependent hi.
    induction xs as [|x xs IH]; [done|].
    intros hi lo. simpl.
    destruct xs as [|x' xs].
    - intros [? ->]. done.
    - intros [? [lo' Hh]]. apply (IH hi lo').
      apply Hh.
  Qed.

  Lemma map_slice_lookup_hi_alt m lo hi xs :
    map_slice m lo hi xs → ∃ x, m !! hi = Some x ∧ last xs = Some x.
  Proof.
    intros ?.
    assert (is_Some (last xs)) as [x eq].
    { apply last_is_Some. eapply map_slice_nonempty. done. }
    exists x. split; last done. rewrite -eq. by eapply map_slice_lookup_hi.
  Qed.

  Lemma map_slice_snoc m lo hi hi2 xs x :
    hi2 < hi ∧
    m !! hi = Some x ∧
    (∀ hi'', hi2 < hi'' < hi → m !! hi'' = None) ∧ (* There are no elements in between. *)
    map_slice m lo hi2 xs
    → map_slice m lo hi (xs ++ [x]).
  Proof.
    generalize dependent lo.
    induction xs as [|x1 xs IH].
    { naive_solver. }
    simpl.
    destruct xs as [|x2 xs].
    * intros lo.
      destruct 1 as (? & ? & ? & [??]).
      subst.
      split; first done.
      exists hi. split_and!; done.
    * intros lo.
      destruct 1 as (? & ? & ? & [look (lo' & next)]).
      split; first apply look.
      exists lo'.
      split_and!; [apply next|apply next|].
      apply IH.
      split_and!; try done. apply next.
  Qed.

  Lemma map_slice_equiv m1 m2 lo hi xs :
    (∀ t, lo ≤ t ≤ hi → m1 !! t = m2 !! t) →
    map_slice m1 lo hi xs → map_slice m2 lo hi xs.
  Proof.
    generalize dependent lo.
    induction xs as [|x1 xs IH]; first done.
    intros lo eq slice.
    assert (lo ≤ hi) by (by eapply map_slice_lt).
    simpl.
    destruct xs as [|x2 xs].
    - destruct slice as [<- ->]. split; last done. symmetry. by apply eq.
    - destruct slice as [<- (lo' & le & between & slice)].
      assert (lo' ≤ hi) by (by eapply map_slice_lt).
      split. { symmetry. apply eq. lia. }
      exists lo'. split; first apply le.
      split. { intros ? ?. rewrite -eq. apply between. lia. lia. }
      apply IH.
      + intros ??. apply eq. lia.
      + done.
  Qed.

  Lemma map_slice_insert_snoc m lo hi hi2 xs x :
    hi < hi2 →
    map_no_later m hi →
    map_slice m lo hi xs →
    map_slice (<[hi2:=x]> m) lo hi2 (xs ++ [x]).
  Proof.
    intros lt nolater sl.
    eapply map_slice_snoc.
    split_and!.
    - done.
    - apply lookup_insert.
    - intros ??.
      rewrite lookup_insert_ne; last lia.
      apply nolater. lia.
    - eapply map_slice_equiv; last apply sl.
      intros t ?. rewrite lookup_insert_ne; first done. lia.
  Qed.

  Lemma map_no_later_Some_agree m t t' :
    map_no_later m t →
    map_no_later m t' →
    is_Some (m !! t) →
    is_Some (m !! t') →
    t = t'.
  Proof.
    rewrite /map_no_later.
    intros Hl1 Hl2 [? Hs1] [? Hs2].
    destruct (Nat.le_gt_cases t t') as [le|lt].
    - apply Nat.lt_eq_cases in le.
      destruct le as [lt|]; last done.
      apply Hl1 in lt.
      congruence.
    - apply Hl2 in lt. congruence.
  Qed.

End nat_map.

Section map_no_later.
  Context `{FinMap nat M} {A : Type}.

  Implicit Types m : M A.

  Lemma map_no_later_Some m t t' :
    map_no_later m t → is_Some (m !! t') → t' ≤ t.
  Proof. intros ? ?%not_eq_None_Some. apply not_gt. naive_solver. Qed.

  Lemma map_no_later_singleton t (x : A) :
    map_no_later {[ t := x ]} t.
  Proof. intros ??. rewrite lookup_singleton_ne; [done | lia]. Qed.

  Lemma map_slice_no_later_elem_of m tP t tStore xs x :
    m !! t = Some x →
    tP ≤ t →
    map_slice m tP tStore xs →
    map_no_later m tStore →
    x ∈ xs.
  Proof.
    intros ??? nolater.
    eapply map_slice_lookup_between; [done | | done].
    split; first done.
    apply not_gt.
    intros gt%nolater.
    congruence.
  Qed.

  Lemma map_no_later_fmap {B} (f : A → B) t m :
    map_no_later m t ↔ map_no_later (f <$> m) t.
  Proof.
    rewrite /map_no_later.
    setoid_rewrite lookup_fmap.
    setoid_rewrite fmap_None.
    reflexivity.
  Qed.

  Lemma map_no_later_weaken m t1 t2 :
    t1 ≤ t2 → map_no_later m t1 → map_no_later m t2.
  Proof. intros ? nolater ??. apply nolater. lia. Qed.

  Lemma map_no_later_insert m t1 t2 s :
    t1 ≤ t2 → map_no_later m t1 → map_no_later (<[t2 := s]> m) t2.
  Proof.
    intros le nolater.
    intros t' ?.
    rewrite lookup_insert_ne; last lia.
    apply nolater. lia.
  Qed.

End map_no_later.

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

  (* (* upstreamed *) *)
  (* Lemma dom_map_zip_with `{FinMapDom K M D} {A B C} *)
  (*       (f : A → B → C) (ma : M A) (mb : M B) : *)
  (*   dom D (map_zip_with f ma mb) ≡ dom D ma ∩ dom D mb. *)
  (* Proof. *)
  (*   rewrite set_equiv=> x. *)
  (*   rewrite elem_of_intersection. *)
  (*   rewrite !elem_of_dom. *)
  (*   rewrite map_lookup_zip_with. *)
  (*   destruct (ma !! x), (mb !! x); rewrite !is_Some_alt; naive_solver. *)
  (* Qed. *)

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

End restrict_dom.

Section restrict_leibniz.
  Context `{FinMapDom K M D}.
  Context `{!RelDecision (∈@{D})}.
  Context {A : Type}.
  Context `{!LeibnizEquiv D}.

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

  Admitted.

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
    induction m1 as [|i x m ? IH] using map_ind.
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
        rewrite big_sepM2_insert.
        done.
        done.
        admit.
      * apply exist_elim => m2.
  Admitted.

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
    ([∗ map] k↦y1;y2 ∈ n1;n2, Ψ k y1 y2).
  Proof.
    iIntros (sub1 domEq).
    rewrite !big_sepM2_alt.
    iIntros "R [%impl sep] #impl".
    apply dom_eq_alt_L in impl.
    iSplit. { iPureIntro. apply dom_eq_alt_L. congruence. }
    iDestruct (big_sepM_impl_dom_subseteq_with_resource with "R sep []")
      as "(A & $ & C)".
    { rewrite 2!dom_map_zip_with. rewrite -domEq -impl. set_solver. }
    iIntros "!>" (k [??] [??] [l1 l2]%map_lookup_zip_Some [l3 l4]%map_lookup_zip_Some) "R phi".
    simpl in *.
    iApply ("impl" with "[//] [//] [//] [//] R phi").
  Qed.

  (* This could be upstreamed but we'd need to drop the affine requirement and
  rewrite the proof to not use the proofmode. *)
  Lemma big_sepM2_impl_dom_subseteq `{!BiAffine PROP} Φ Ψ m1 m2 n1 n2 :
    dom (gset _) n1 ⊆ dom (gset _) m1 →
    dom (gset _) n1 = dom (gset _) n2 →
    ([∗ map] k↦x1;x2 ∈ m1;m2, Φ k x1 x2) -∗
    □ (∀ (k : K) x1 x2 y1 y2,
        ⌜m1 !! k = Some x1⌝ → ⌜m2 !! k = Some x2⌝ →
        ⌜n1 !! k = Some y1⌝ → ⌜n2 !! k = Some y2⌝ → Φ k x1 x2 -∗ Ψ k y1 y2) -∗
    ([∗ map] k↦y1;y2 ∈ n1;n2, Ψ k y1 y2).
    (* ∗ ([∗ map] k↦x ∈ filter (λ '(k, _), m2 !! k = None) m1, Φ k x). *)
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
