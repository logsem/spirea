(* A collection of a few fairly general constructions and lemmas. In other
words, our own little (std++)++. *)

From stdpp Require Import countable numbers gmap fin_maps list.
From iris Require Import cmra.
From iris.bi Require Import big_op.
From iris.algebra Require Import gmap agree.
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

  From iris.algebra Require Export big_op.

  Lemma big_sepM_impl Φ Ψ m :
    ([∗ map] k↦x ∈ m, Φ k x) -∗
    □ (∀ k x, ⌜m !! k = Some x⌝ → Φ k x -∗ Ψ k x) -∗
    [∗ map] k↦x ∈ m, Ψ k x.
  Proof.
    apply wand_intro_l. rewrite big_sepM_intuitionistically_forall -big_sepM_sep.
    by setoid_rewrite wand_elim_l.
  Qed.

  Lemma big_sepM_impl_2 {B}
        (Φ : K → A → PROP) (Ψ : K → B → PROP) (m1 : gmap K A) (m2 : gmap K B) :
    ([∗ map] k↦x ∈ m1, Φ k x) -∗
    □ (∀ (k : K) (y : B),
          ⌜m2 !! k = Some y⌝ -∗
          ((∃ (x : A), ⌜m1 !! k = Some x⌝ ∗ Φ k x) ∨ ⌜m1 !! k = None⌝) -∗
          Ψ k y) -∗
    [∗ map] k↦y ∈ m2, Ψ k y.
  Proof.
    revert Φ m1. induction m2 as [|i y m ? IH] using map_ind=> Φ.
    - iIntros (m1) "_ _". done.
    - iIntros (m1) "A #H".
      rewrite big_sepM_insert; last done.
      destruct (m1 !! i) as [x|] eqn:look.
      * iDestruct (big_sepM_delete with "A") as "[phi A]"; first apply look.
        iDestruct ("H" $! i y with "[%] [phi]") as "HΨ".
        { by rewrite lookup_insert. }
        { iLeft. iExists x. iFrame. done. }
        iFrame.
        iApply (IH with "[A] [H]").
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
      * iDestruct ("H" $! i y with "[%] []") as "HΨ".
        { by rewrite lookup_insert. }
        { iRight. iFrame. done. }
        iFrame "HΨ".
        iApply (IH with "[A] [H]").
        { iFrame "A". }
        { iModIntro.
          iIntros (i' y' look1) "disj".
          iSpecialize ("H" $! i' y').
          destruct (decide (i = i')) as [?|neq]; first simplify_eq.
          rewrite lookup_insert_ne; last done.
          iSpecialize ("H" $! look1 with "disj").
          done. }
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
    [∗ map] k↦y ∈ m2, Ψ k y.
  Proof.
    intros sub.
    iIntros "M #impl".
    iApply (big_sepM_impl_2 with "M [impl]").
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

  Lemma map_lookup_zip_with_None {A B C} (f : A → B → C) (m1 : M A) (m2 : M B) i :
    map_zip_with f m1 m2 !! i = None ↔ m1 !! i = None ∨ m2 !! i = None.
  Proof. rewrite map_lookup_zip_with. destruct (m1 !! i), (m2 !! i); naive_solver. Qed.

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

  (* Upstream. *)
  Lemma map_filter_subseteq f `{∀ (x : (K *A)), Decision (f x)} m : filter f m ⊆ m.
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

  Lemma restrict_dom_subset (s : D) (m : M A) :
    s ⊆ dom _ m → dom _ (restrict s m) ≡ s.
  Proof.
    intros Hsub.
    rewrite /restrict.
    eapply dom_filter.
    intros i.
    split; [|by intros [_ [_ ?]]].
    intros.
    assert (is_Some (m !! i)) as [x ?] by (apply elem_of_dom; set_solver).
    by exists x.
  Qed.

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
