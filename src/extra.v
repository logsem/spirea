(* A collection of a few fairly general constructions and lemmas. In other
words, our own little (std++)++. *)

From stdpp Require Import countable numbers gmap fin_maps list.
From iris Require Import cmra.
From iris.bi Require Import big_op.
From iris.algebra Require Import gmap.

From iris.bi Require Import derived_laws_later.

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

Global Instance max_list_perm_proper : Proper ((≡ₚ) ==> (=)) max_list.
Proof. apply _. Qed.

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
  map_Forall (λ (i : K) (x : A), P i x) ({[j := y]} : M A).
Proof.
  split; intros HP.
  - by intros i x [-> ->]%lookup_singleton_Some.
  - apply HP, lookup_singleton.
Qed.
