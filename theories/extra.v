From stdpp Require Import countable numbers gmap fin_maps list.

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

Definition max_list := foldr max 0.

Global Instance max_list_perm_proper : Proper ((≡ₚ) ==> (=)) max_list.
Proof. apply _. Qed.

Section max_list.
  Context {A : Type}.

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

End max_list.