(* A collection of a few fairly general constructions and lemmas. In other
words, our own little (std++)++. *)

From stdpp Require Import countable numbers gmap fin_maps list.
From iris Require Import cmra.
From iris.bi Require Import big_op.
From iris.algebra Require Import gmap agree big_op.
From iris.proofmode Require Import tactics.
Import interface.bi derived_laws.bi derived_laws_later.bi.

From iris.bi Require Import derived_laws_later.

(* We define our own relation. Workaround for universe issues in stdpp and Iris. *)
Definition relation2 A := A -> A -> Prop.

(* Section union_with.

  Context `{FinMap K M}.

  Context {A} (f : A → A → option A).

  Implicit Types m : M A.

  Lemma union_with_comm m1 m2 :
    (∀ i x y, m1 !! i = Some x → m2 !! i = Some y → f x y = f y x) →
    union_with f m1 m2 = union_with f m2 m1.
  Proof.
    intros. apply (merge_comm _). intros i.
    destruct (m1 !! i) eqn:?, (m2 !! i) eqn:?; simpl; eauto.
  Qed.
  Global Instance: Comm (=) f → Comm (=@{M A}) (union_with f).
  Proof. intros ???. apply union_with_comm. eauto. Qed.

End union_with. *)

(* Definition max_list := foldr max 0. *)

Definition min_list := foldr min 0.

(* Lemmas about finite maps of natural numbers. *)
Section nat_map.
  Context `{FinMap nat M} {A : Type}.

  Implicit Types m : M A.

  Definition max_member m t v :=
    (m !! t = Some v) ∧ (∀ t', t < t' → m !! t' = None).
  
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
        (∀ lo'', lo < lo'' < lo' → m !! lo'' = None) ∧ (* There are not elements in between. *)
        map_slice m lo' hi xs
        (* map_slice m (min_list $ elements $ filter (λ t, lo < t) (dom (gset nat) m)) hi xs *)
    end.

  Lemma map_slice_lookup_between m lo hi xs t x :
    map_slice m lo hi xs → lo ≤ t ≤ hi → m !! t = Some x → x ∈ xs.
  Proof. Admitted.

  Lemma map_slice_lookup_lo m lo hi xs :
    map_slice m lo hi xs → m !! lo = xs !! 0.
  Proof.
    destruct xs as [|x xs]; [done|]. simpl.
    destruct xs.
    - intros [? ->]. done.
    - intros [? _]. done.
  Qed.

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
  
End nat_map.

(* This section has been upstreamed. *)
Section max_list.
  (* Context {A : Type}. *)

  Lemma max_list_elem_of_le n ns:
    n ∈ ns → n ≤ max_list ns.
  Proof. induction 1; simpl; lia. Qed.

  Lemma max_list_elem_of ns : ns ≠ [] → max_list ns ∈ ns.
  Proof.
    intros H. induction ns; [done|]. simpl.
    edestruct (Nat.max_spec a) as [[Hle ->]|[HO ->]].
    - destruct ns; [simpl in *; lia|].
      by apply elem_of_list_further, IHns.
    - apply elem_of_list_here.
  Qed.

  Lemma max_list_not_elem_of_gt n ns : max_list ns < n → n ∉ ns.
  Proof. intros ?. induction 1; simpl in *; lia. Qed.

End max_list.

Lemma singleton_included_insert `{Countable K} {A : cmra} (k : K) (a a' : A) (m : gmap K A) :
  a ≼ a' → {[k := a]} ≼ <[k:=a']> m.
Proof.
  intros le.
  apply singleton_included_l.
  exists a'.
  split. - by rewrite lookup_insert. - apply Some_included. right. done.
Qed.

Lemma big_sepM_imap {PROP : bi} `{Countable K} {A B} (f : K → A → B) (Φ : K → B → PROP) (m : gmap K A) :
  ([∗ map] k↦y ∈ map_imap (λ (k : K) a, Some (f k a)) m, Φ k y) ⊣⊢ ([∗ map] k↦y ∈ m, Φ k (f k y)).
Proof. Admitted.

Lemma big_sepM_impl' {PROP : bi} `{Countable K} {A B} (Φ : K → A → PROP) (Ψ : K → B → PROP) (m1 : gmap K A) (m2 : gmap K B) :
  dom (gset K) m1 = dom _ m2 →
  ([∗ map] k↦x ∈ m1, Φ k x) -∗
  □ (∀ (k : K) (x : A) (y : B), ⌜m1 !! k = Some x⌝ → ⌜m2 !! k = Some y⌝ → Φ k x -∗ Ψ k y) -∗
  [∗ map] k↦y ∈ m2, Ψ k y.
Proof. Admitted.

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

Lemma to_agree_fmap (a b : gmap nat positive) :
  a ⊆ b ↔ to_agree <$> a ≼ to_agree <$> b.
Proof.
  rewrite lookup_included.
  rewrite  map_subseteq_spec.
  setoid_rewrite lookup_fmap.
  split.
  - intros sub.
    intros i.
    (* apply option_included_total. *)
    destruct (a !! i) eqn:eq.
    2: { eexists _. rewrite left_id. reflexivity. }
    rewrite (sub i p); done.
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
    setoid_rewrite incl.
    done.
Qed.

Section big_sepM.
  Context {PROP : bi}.
  Context `{BiAffine PROP}.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.

  Lemma big_sepM_impl Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    □ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x -∗ Ψ k x) -∗
    [∗ map] k↦x ∈ m, Ψ k x.
  Proof.
    apply wand_intro_l. rewrite big_sepM_intuitionistically_forall -big_sepM_sep.
    by setoid_rewrite wand_elim_l.
  Qed.

  (* upstreamed *)
  Lemma map_filter_id (P : (K * A → Prop)) `{∀ (x : (K * A)), Decision (P x)} m
    : (∀ k x, m !! k = Some x → P (k, x)) → filter P m = m.
  Proof.
    intros Hi. induction m as [|i y m ? IH] using map_ind; [done|].
    rewrite map_filter_insert.
    - rewrite IH; [done|].
      intros j ??. apply Hi. destruct (decide (i = j)); [naive_solver|].
      apply lookup_insert_Some. naive_solver.
    - apply Hi. by rewrite lookup_insert.
  Qed.

  Lemma big_sepM_impl_strong {B}
        (Φ : K → A → PROP) (Ψ : K → B → PROP) (m1 : gmap K A) (m2 : gmap K B) :
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    □ (∀ (k : K) (y : B),
          ⌜m2 !! k = Some y⌝ -∗
          ((∃ (x : A), ⌜m1 !! k = Some x⌝ ∗ Φ k x) ∨ ⌜m1 !! k = None⌝) -∗
          Ψ k y) -∗
    ([∗ map] k↦y ∈ m2, Ψ k y) ∗
    ([∗ map] k↦x ∈ (filter (λ '(k, _), m2 !! k = None) m1), Φ k x).
  Proof.
    revert Φ m1. induction m2 as [|i y m ? IH] using map_ind=> Φ.
    - iIntros (m1) "H _". rewrite map_filter_id; [by iFrame| naive_solver].
    - iIntros (m1) "A #H".
      rewrite big_sepM_insert; last done.
      destruct (m1 !! i) as [x|] eqn:look.
      * iDestruct (big_sepM_delete with "A") as "[phi A]"; first apply look.
        iDestruct ("H" $! i y with "[%] [phi]") as "HΨ".
        { by rewrite lookup_insert. }
        { iLeft. iExists x. iFrame. done. }
        iFrame.
        iDestruct (IH with "[A] [H]") as "[$ Hi]".
        { iFrame "A". }
        { iModIntro.
          iIntros (i' y' look1) "disj".
          iSpecialize ("H" $! i' y').
          destruct (decide (i = i')) as [?|neq]; first simplify_eq.
          rewrite lookup_insert_ne; last done.
          rewrite lookup_delete_ne; last done.
          iSpecialize ("H" $! look1 with "disj").
          done.
        }
        erewrite map_filter_strong_ext.
        { iFrame "Hi". }
        simpl.
        intros j x'.
        destruct (decide (i = j)).
        { simplify_eq. rewrite lookup_delete. rewrite lookup_insert. naive_solver. }
        rewrite lookup_delete_ne // lookup_insert_ne //.
      * iDestruct ("H" $! i y with "[%] []") as "$".
        { by rewrite lookup_insert. }
        { iRight. iFrame. done. }
        (* iFrame "HΨ". *)
        iDestruct (IH with "[A] [H]") as "Hi".
        { iFrame "A". }
        { iModIntro.
          iIntros (i' y' look1) "disj".
          iSpecialize ("H" $! i' y').
          destruct (decide (i = i')) as [?|neq]; first simplify_eq.
          rewrite lookup_insert_ne; last done.
          iSpecialize ("H" $! look1 with "disj").
          done. }
        iDestruct "Hi" as "[$ Hi]".
        erewrite map_filter_strong_ext.
        { iFrame "Hi". }
        intros i' x'. simpl.
        destruct (decide (i = i')) as [?|neq]; first naive_solver.
        by rewrite lookup_insert_ne.
  Qed.

  Lemma big_sepM_impl_sub {B}
        (Φ : K → A → PROP) (Ψ : K → B → PROP) (m1 : gmap K A) (m2 : gmap K B) :
    dom (gset _) m2 ⊆ dom _ m1 →
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    □ (∀ (k : K) (x : A) (y : B),
          ⌜m1 !! k = Some x⌝ -∗
          ⌜m2 !! k = Some y⌝ -∗
          Φ k x -∗
          Ψ k y) -∗
    ([∗ map] k↦y ∈ m2, Ψ k y) ∗
    ([∗ map] k↦x ∈ (filter (λ '(k, _), m2 !! k = None) m1), Φ k x).
  Proof.
    intros sub.
    iIntros "M #impl".
    iApply (big_sepM_impl_strong with "M [impl]").
    iIntros "!>" (?? look1) "H".
    iDestruct "H" as "[H|%]".
    2: { setoid_rewrite <- not_elem_of_dom in H1.
         apply elem_of_dom_2 in look1.
         set_solver. }
    iDestruct "H" as (x look) "ϕ".
    iApply ("impl" with "[//] [//] ϕ").
  Qed.

End big_sepM.

Section map_zip_with.
  Context `{FinMap K M}.

  (* upstreamed *)
  Lemma map_lookup_zip_with_None {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) i :
    map_zip_with f m1 m2 !! i = None ↔ m1 !! i = None ∨ m2 !! i = None.
  Proof. rewrite map_lookup_zip_with. destruct (m1 !! i), (m2 !! i); naive_solver. Qed.

  (* Upstreamed. *)
  Lemma map_lookup_zip_Some {A B} (m1 : M A) (m2 : M B) l p :
    (map_zip m1 m2) !! l = Some p ↔ m1 !! l = Some p.1 ∧ m2 !! l = Some p.2.
  Proof. rewrite map_lookup_zip_with_Some. destruct p. naive_solver. Qed.

  (* Upstream this. *)
  Lemma map_zip_with_dom_fst `{FinMapDom K M D} {A B C}
        (f : A → B → C) (ma : M A) (mb : M B) : dom D (map_zip_with f ma mb) ⊆ dom D ma.
  Proof.
    intros ?. rewrite 2!elem_of_dom. intros [? ?%map_lookup_zip_with_Some].
    naive_solver.
  Qed.

  Lemma map_zip_with_dom_snd `{FinMapDom K M D} {A B C}
        (f : A → B → C) (ma : M A) (mb : M B) : dom D (map_zip_with f ma mb) ⊆ dom D mb.
  Proof. rewrite map_zip_with_flip. apply map_zip_with_dom_fst. Qed.

  (* upstreamed *)
  Lemma map_zip_with_dom `{FinMapDom K M D} {A B C}
        (f : A → B → C) (ma : M A) (mb : M B) :
    dom D (map_zip_with f ma mb) ≡ dom D ma ∩ dom D mb.
  Proof.
    rewrite set_equiv=> x.
    rewrite elem_of_intersection.
    rewrite !elem_of_dom.
    rewrite map_lookup_zip_with.
    destruct (ma !! x), (mb !! x); rewrite !is_Some_alt; naive_solver.
  Qed.

  Lemma map_zip_with_dom_eq_l `{FinMapDom K M D} {A B C}
        (f : A → B → C) (ma : M A) (mb : M B) :
    dom D ma ⊆ dom D mb →
    dom D (map_zip_with f ma mb) ≡ dom D ma.
  Proof. rewrite map_zip_with_dom. set_solver. Qed.

  Lemma map_zip_with_dom_eq_r `{FinMapDom K M D} {A B C}
        (f : A → B → C) (ma : M A) (mb : M B) :
    dom D mb ⊆ dom D ma →
    dom D (map_zip_with f ma mb) ≡ dom D mb.
  Proof. rewrite map_zip_with_dom. set_solver. Qed.

  (* Upstreamed *)
  Lemma not_elem_of_weaken `{Countable A} l (m1 m2 : gset A) :
    l ∉ m2 → m1 ⊆ m2 → l ∉ m1.
  Proof. set_solver. Qed.

End map_zip_with.

Definition restrict `{FinMap K M, ElemOf K D, !RelDecision (∈@{D})} {A} (s : D) (m : M A) :=
  filter (λ '(k, _), k ∈ s) m.

Section restrict.
  Context `{FinMapDom K M D}.
  Context `{!RelDecision (∈@{D})}.
  Context {A : Type}.
  Implicit Types (s : D) (m : M A) (k : K).

  Lemma restrict_lookup_Some (s : D) (m : M A) (k : K) (x : A) :
    restrict s m !! k = Some x ↔ (m !! k = Some x) ∧ k ∈ s.
  Proof. by rewrite map_filter_lookup_Some. Qed.

  Lemma restrict_lookup_Some_2 (s : D) (m : M A) (k : K) (x : A) :
    m !! k = Some x → k ∈ s → restrict s m !! k = Some x.
  Proof. by rewrite restrict_lookup_Some. Qed.

  (* Upstreamed. *)
  Lemma map_filter_subseteq f `{∀ (x : (K *A)), Decision (f x)} m :
    filter f m ⊆ m.
  Proof. apply map_subseteq_spec, map_filter_lookup_Some_1_1. Qed.

  Lemma restrict_subseteq s m : restrict s m ⊆ m.
  Proof. rewrite /restrict. apply map_filter_subseteq. Qed.

  Lemma restrict_intersection s m : dom _ (restrict s m) = s ∩ (dom _ m).
  Proof. Abort. (* This is true, but we haven't needed it yet. *)

  (*
  Lemma restrict_superset_id (s : D) (m : M A) :
    dom _ m ⊆ s → restrict s m = m.
  Proof.
    intros Hsub.
  Admitted.
  *)

  Lemma restrict_dom s m : dom _ (restrict s m) ≡ s ∩ dom _ m.
  Proof.
    apply dom_filter => i.
    rewrite elem_of_intersection.
    rewrite elem_of_dom.
    rewrite /is_Some.
    naive_solver.
  Qed.

  Lemma restrict_dom_subset (s : D) (m : M A) :
    s ⊆ dom _ m → dom _ (restrict s m) ≡ s.
  Proof. rewrite restrict_dom. set_solver. Qed.

End restrict.

Section restrict_leibniz.
  Context `{FinMapDom K M D}.
  Context `{!RelDecision (∈@{D})}.
  Context {A : Type}.
  Context `{!LeibnizEquiv D}.

  Lemma restrict_dom_subset_L (s : D) (m : M A) :
    s ⊆ dom _ m → dom _ (restrict s m) = s.
  Proof. unfold_leibniz. apply restrict_dom_subset. Qed.

End restrict_leibniz.
