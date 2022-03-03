(* Various constructions and lemmas about maps. *)

From stdpp Require Import countable numbers gmap fin_maps list.
From iris.proofmode Require Import tactics.

(** [map_no_later] *)

(** The map [m] is undefined for all natural numbers greater than [t]. *)
Definition map_no_later`{FinMap nat M} {A : Type} (m : M A) t :=
  ∀ t', t < t' → m !! t' = None.

(* Lemmas about finite maps of natural numbers. *)
Section map_sequence.
  Context `{FinMap nat M} {A : Type}.

  Implicit Types m : M A.

  (** Expresses that the map [m] contains, in order, the values [xs] from the
  indeces starting at exactly [lo] ending at exactly [hi]. *)
  Fixpoint map_sequence m (lo hi : nat) (xs : list A) :=
    match xs with
    | [] => False
    | [x] => m !! hi = Some x ∧ lo = hi
    | x :: xs =>
      m !! lo = Some x ∧
      ∃ lo',
        lo < lo' ∧
        (∀ lo'', lo < lo'' < lo' → m !! lo'' = None) ∧ (* There are no elements in between. *)
        map_sequence m lo' hi xs
    end.

  Lemma map_sequence_lt m lo hi xs : map_sequence m lo hi xs → lo ≤ hi.
  Proof.
    generalize dependent lo.
    induction xs as [|x1 xs IH]; first done.
    destruct xs as [|x2 xs]. { naive_solver. }
    intros lo (look & lo' & ? & between & slice).
    apply IH in slice. lia.
  Qed.

  Lemma map_sequence_lookup_between m lo hi xs t x :
    map_sequence m lo hi xs → lo ≤ t ≤ hi → m !! t = Some x → x ∈ xs.
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

  Lemma map_sequence_lookup_lo m lo hi xs :
    map_sequence m lo hi xs → m !! lo = xs !! 0.
  Proof.
    destruct xs as [|x xs]; [done|]. simpl.
    destruct xs.
    - intros [? ->]. done.
    - intros [? _]. done.
  Qed.

  Lemma map_sequence_nonempty m lo hi xs : map_sequence m lo hi xs → xs ≠ [].
  Proof. by destruct xs. Qed.

  Lemma map_sequence_lookup_hi m lo hi xs :
    map_sequence m lo hi xs → m !! hi = last xs.
  Proof.
    generalize dependent lo. generalize dependent hi.
    induction xs as [|x xs IH]; [done|].
    intros hi lo. simpl.
    destruct xs as [|x' xs].
    - intros [? ->]. done.
    - intros [? [lo' Hh]]. apply (IH hi lo').
      apply Hh.
  Qed.

  Lemma map_sequence_lookup_hi_alt m lo hi xs :
    map_sequence m lo hi xs → ∃ x, m !! hi = Some x ∧ last xs = Some x.
  Proof.
    intros ?.
    assert (is_Some (last xs)) as [x eq].
    { apply last_is_Some. eapply map_sequence_nonempty. done. }
    exists x. split; last done. rewrite -eq. by eapply map_sequence_lookup_hi.
  Qed.

  Lemma map_sequence_snoc m lo hi hi2 xs x :
    hi2 < hi ∧
    m !! hi = Some x ∧
    (∀ hi'', hi2 < hi'' < hi → m !! hi'' = None) ∧ (* There are no elements in between. *)
    map_sequence m lo hi2 xs
    → map_sequence m lo hi (xs ++ [x]).
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

  Lemma map_sequence_equiv m1 m2 lo hi xs :
    (∀ t, lo ≤ t ≤ hi → m1 !! t = m2 !! t) →
    map_sequence m1 lo hi xs → map_sequence m2 lo hi xs.
  Proof.
    generalize dependent lo.
    induction xs as [|x1 xs IH]; first done.
    intros lo eq slice.
    assert (lo ≤ hi) by (by eapply map_sequence_lt).
    simpl.
    destruct xs as [|x2 xs].
    - destruct slice as [<- ->]. split; last done. symmetry. by apply eq.
    - destruct slice as [<- (lo' & le & between & slice)].
      assert (lo' ≤ hi) by (by eapply map_sequence_lt).
      split. { symmetry. apply eq. lia. }
      exists lo'. split; first apply le.
      split. { intros ? ?. rewrite -eq. apply between. lia. lia. }
      apply IH.
      + intros ??. apply eq. lia.
      + done.
  Qed.

  Lemma map_sequence_insert_snoc m lo hi hi2 xs x :
    hi < hi2 →
    map_no_later m hi →
    map_sequence m lo hi xs →
    map_sequence (<[hi2:=x]> m) lo hi2 (xs ++ [x]).
  Proof.
    intros lt nolater sl.
    eapply map_sequence_snoc.
    split_and!.
    - done.
    - apply lookup_insert.
    - intros ??.
      rewrite lookup_insert_ne; last lia.
      apply nolater. lia.
    - eapply map_sequence_equiv; last apply sl.
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

End map_sequence.

Section map_no_later.
  Context `{FinMap nat M} {A : Type}.

  Implicit Types m : M A.

  Lemma map_no_later_Some m t t' :
    map_no_later m t → is_Some (m !! t') → t' ≤ t.
  Proof. intros ? ?%not_eq_None_Some. apply not_gt. naive_solver. Qed.

  Lemma map_no_later_singleton t (x : A) :
    map_no_later {[ t := x ]} t.
  Proof. intros ??. rewrite lookup_singleton_ne; [done | lia]. Qed.

  Lemma map_sequence_no_later_elem_of m tP t tStore xs x :
    m !! t = Some x →
    tP ≤ t →
    map_sequence m tP tStore xs →
    map_no_later m tStore →
    x ∈ xs.
  Proof.
    intros ??? nolater.
    eapply map_sequence_lookup_between; [done | | done].
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
