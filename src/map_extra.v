(* Various constructions and lemmas about maps. *)

From stdpp Require Import countable numbers gmap fin_maps list.
From iris.proofmode Require Import tactics.
From self Require Import extra.

Section lemmas.
  Context `{FinMapDom K M D}.

  Lemma map_eq_dom {A} (m1 m2 : M A) :
    dom m1 = dom m2 →
    m1 = m2 ↔ (∀ (i : K) (x y : A), m1 !! i = Some x → m2 !! i = Some y → x = y).
  Proof.
    intros domEq.
    rewrite map_eq_iff. split.
    - intros ? ? ? ? ? ?. apply (inj Some). congruence.
    - intros l k1.
      destruct (m1 !! k1) as [mi|] eqn:eq.
      * assert (is_Some (m2 !! k1)) as [mi' eq2].
        { apply elem_of_dom. rewrite -domEq. apply elem_of_dom. done. }
        rewrite eq2.
        f_equal.
        eapply l; try done.
      * symmetry.
        apply not_elem_of_dom.
        rewrite -domEq.
        apply not_elem_of_dom.
        done.
  Qed.

  Lemma map_eq_dom_subseteq {A} (m1 m2 m3 : M A) :
    dom m1 = dom m2 →
    m1 ⊆ m3 →
    m2 ⊆ m3 →
    m1 = m2.
  Proof.
    intros domEq sub1 sub2.
    eapply map_eq_dom; first apply domEq.
    setoid_rewrite (map_subseteq_spec m1 m3) in sub1.
    setoid_rewrite (map_subseteq_spec m2 m3) in sub2.
    intros k x y look1 look2.
    apply (inj Some).
    erewrite <- sub1; last done.
    erewrite <- sub2; last done.
    done.
  Qed.

End lemmas.

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
  Fixpoint map_sequence (m : M A) (lo hi : nat) (xs : list A) :=
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

  (* FIXME: Renamed to [le]. *)
  Lemma map_sequence_lt m lo hi xs : map_sequence m lo hi xs → lo ≤ hi.
  Proof.
    generalize dependent lo.
    induction xs as [|x1 xs IH]; first done.
    destruct xs as [|x2 xs]. { naive_solver. }
    intros lo (look & lo' & ? & between & slice).
    apply IH in slice. lia.
  Qed.

  Lemma map_sequence_eq m lo hi x :
    map_sequence m lo hi [x] → lo = hi.
  Proof. naive_solver. Qed.

  Lemma map_sequence_lt' m lo hi x1 x2 xs :
    map_sequence m lo hi (x1 :: x2 :: xs) → lo < hi.
  Proof.
    intros (look & (lo2 & lt & all & seq)).
    apply map_sequence_lt in seq.
    lia.
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

  Lemma map_sequence_lookup_lo_cons m lo hi xs x :
    m !! lo = Some x → map_sequence m lo hi xs → ∃ xs', x :: xs' = xs.
  Proof.
    destruct xs as [|? xs]; [done|]. simpl.
    destruct xs as [|x' xs].
    - intros ? [? ->]. exists []. congruence.
    - intros ? [? _]. exists (x' :: xs). congruence.
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

  Lemma map_sequence_list_lookup m lo hi l i s :
    l !! i = Some s →
    map_sequence m lo hi l →
    ∃ t_i, lo ≤ t_i ≤ hi ∧ m !! t_i = Some s.
  Proof.
    generalize dependent lo.
    generalize dependent i.
    induction l as [|x l IH]; first done.
    intros i lo lLook seq.
    eassert _ as le; first (eapply map_sequence_lt; done).
    destruct l.
    { apply list_lookup_singleton_Some in lLook as [-> ->].
      exists hi. split; [lia|apply seq]. }
    destruct seq as [mLook seq].
    destruct i; simpl in lLook.
    { simplify_eq.
      exists lo. split; [lia | done]. }
    destruct seq as (lo' & lt & all & seq).
    specialize (IH i lo' lLook seq) as (t_i & ? & mLook2).
    exists t_i. split; last apply mLook2. lia.
  Qed.

  Lemma map_sequence_list_lookup_mono m lo hi l i j s1 s2 :
    map_sequence m lo hi l →
    i < j →
    l !! i = Some s1 →
    l !! j = Some s2 →
    ∃ t_i t_j, t_i < t_j ∧
               m !! t_i = Some s1 ∧
               m !! t_j = Some s2.
  Proof.
    generalize dependent lo. generalize dependent j. generalize dependent i.
    induction l as [|x l IH]; first done.
    intros i j lo. destruct l.
    { intros ? ? ?%list_lookup_singleton_Some ?%list_lookup_singleton_Some.
      lia. }
    intros [Ha (lo' & ? & ? & ?)].
    intros le look1 look2.
    assert (∃ j', j = S j') as [j' ->]. { exists (j - 1). lia. }
    simpl in look2.
    (* If [i] is [0] then we've found the first element. *)
    destruct i; simpl in look1.
    { simplify_eq.
      exists lo.
      eapply map_sequence_list_lookup in look2 as (t_j & ? & ?); last done.
      simplify_eq.
      exists t_j. split_and!; try done. lia. }
    eapply (IH i j' lo'); done || lia.
   Qed.

  Lemma map_sequence_cons_drop m lo hi x y xs :
    map_sequence m lo hi (x :: y :: xs) →
    ∃ lo2,
      lo < lo2 ∧
      (∀ lo'', lo < lo'' < lo2 → m !! lo'' = None) ∧
      map_sequence m lo2 hi (y :: xs).
  Proof. intros [a (lo2 & ?)]. exists lo2. naive_solver. Qed.

  Lemma map_sequence_prefix_alt lo hi t xs x m :
    m !! t = Some x →
    map_sequence m lo hi xs →
    lo ≤ t ≤ hi →
    ∃ xs', (xs' ++ [x]) `prefix_of` xs ∧ map_sequence m lo t (xs' ++ [x]).
  Proof.
    intros look.
    generalize dependent lo.
    induction xs as [|x1 xs IH]; first done.
    intros lo.
    destruct (decide (lo = t)).
    { simplify_eq.
      intros. eexists [].
      eassert _ as eq. { eapply map_sequence_lookup_lo_cons; done. }
      destruct eq as [xs' <-].
      split_and!; try done.
      apply prefix_cons. apply prefix_nil. }
    destruct xs as [|x2 xs].
    { simpl. intros ??. lia. }
    intros (look' & lo' & ? & between & slice) inter.
    assert (lo' <= t <= hi) as inter2.
    { split; last lia.
      destruct (Nat.le_gt_cases lo' t) as [?|lt]; first done.
      assert (m !! t = None); last congruence.
      apply between. lia. }
    destruct (IH _ slice inter2) as (xs' & ? & ?).
    eexists (x1 :: xs').
    split. { apply prefix_cons. done. }
    destruct xs'. { naive_solver. }
    split; first done. exists lo'. done.
  Qed.

  Lemma map_sequence_prefix lo hi t xs x m :
    m !! t = Some x →
    map_sequence m lo hi xs →
    lo ≤ t ≤ hi →
    ∃ xs', xs' `prefix_of` xs ∧ map_sequence m lo t xs' ∧ last xs' = Some x.
  Proof.
    intros look seq int.
    eassert (_) as T.
    { eapply map_sequence_prefix_alt; done. }
    destruct T as (xs' & ? & ?).
    exists (xs' ++ [x]).
    split; first done.
    split; first done.
    apply last_snoc.
  Qed.

  Lemma map_sequence_singleton t (x : A) :
    map_sequence {[ t := x ]} t t [x].
  Proof. simpl. split; last done. apply lookup_singleton. Qed.

  Lemma map_sequence_is_singleton m t xs :
    map_sequence m t t xs → ∃ x, xs = [x].
  Proof.
    destruct xs as [|x1 [|x2 xs]].
    - done.
    - naive_solver.
    - intros (? & (lo2 & ? & all & ?%map_sequence_lt)). lia.
  Qed.

  Lemma map_sequence_delete_below lo1 lo2 m hi ss :
    lo1 < lo2  →
    map_sequence m lo2 hi ss →
    map_sequence (delete lo1 m) lo2 hi ss.
  Proof.
    intros lt. apply map_sequence_equiv. intros t le.
    symmetry. apply lookup_delete_ne. lia.
  Qed.

  Lemma map_sequence_delete_above lo m hi1 hi2 ss :
    hi1 < hi2  →
    map_sequence m lo hi1 ss →
    map_sequence (delete hi2 m) lo hi1 ss.
  Proof.
    intros lt. apply map_sequence_equiv. intros t le.
    symmetry. apply lookup_delete_ne. lia.
  Qed.

End map_sequence.

Lemma map_sequence_fmap `{FinMap nat M} {A B} (f : A  → B) (m : M A) lo hi xs :
  map_sequence m lo hi xs →
  map_sequence (f <$> m) lo hi (f <$> xs).
Proof.
  generalize dependent lo.
  induction xs as [|x1 xs IH]; first done.
  intros lo.
  destruct xs as [|x2 xs].
  { simpl. intros [look ?]. rewrite lookup_fmap. rewrite look. done. }
  (* simpl. *)
  intros [look (lo' & ? & all & ?)].
  split. { rewrite lookup_fmap. rewrite look. done. }
  exists lo'. split; first done.
  split.
  - intros. rewrite lookup_fmap. rewrite all; done.
  - apply IH. done.
Qed.

Section map_sequence_dom.
  Context `{FinMapDom nat M D} {A : Type}.
  Implicit Types m : M A.

  Lemma map_sequence_lo_eq {B} lo lo2 lo2' m1 (m2 : M B) x xs y ys hi :
    dom m1 = dom m2 →
    map_sequence m1 lo2 hi (x :: xs) →
    map_sequence m2 lo2' hi (y :: ys) →
    lo < lo2 →
    (∀ lo'' : nat, lo < lo'' < lo2 → m1 !! lo'' = None) →
    lo < lo2' →
    (∀ lo'' : nat, lo < lo'' < lo2' → m2 !! lo'' = None) →
    lo2 = lo2'.
  Proof.
    intros domEq seq1 seq2 ? all1 ? all2.
    (* We want to show that [lo2] is equal to [lo2']. We do this by considering
    * three cases and by deriving contradictions in the other two. *)
    assert (lo2 < lo2' ∨ lo2' < lo2 ∨ lo2 = lo2') as [lt|[lt|<-]] by lia.
    - apply map_sequence_lookup_lo in seq1. simpl in seq1.
      assert (m1 !! lo2 = None); last congruence.
      apply not_elem_of_dom.
      assert (m2 !! lo2 = None) as eq%not_elem_of_dom. { eapply all2. lia. }
      rewrite domEq. apply eq.
    - apply map_sequence_lookup_lo in seq2. simpl in seq2.
      assert (m2 !! lo2' = None); last congruence.
      apply not_elem_of_dom.
      assert (m1 !! lo2' = None) as eq%not_elem_of_dom. { eapply all1. lia. }
      rewrite -domEq. apply eq.
    - done.
  Qed.

  Lemma map_sequence_dom_length {B} m1 (m2 : M B) lo hi xs ys :
    map_sequence m1 lo hi xs →
    map_sequence m2 lo hi ys →
    dom m1 = dom m2 →
    length xs = length ys.
  Proof.
    generalize dependent lo.
    generalize dependent ys.
    induction xs as [|x1 xs IH]; first done.
    intros ys lo.
    destruct ys as [|y1 ys]; first done.

    destruct xs as [|x2 xs].
    { intros [look1 ->]. intros [? ->]%map_sequence_is_singleton. done. }
    destruct ys as [|y2 ys].
    { intros ?%map_sequence_lt'.
      intros ?%map_sequence_eq.
      lia. }

    intros [look1 (lo2 & ? & all1 & seq1)].
    intros [look2 (lo2' & ? & all2 & seq2)].
    intros domEq.
    eassert (lo2 = lo2') as <-. { eapply map_sequence_lo_eq; done. }
    simpl.
    f_equiv.
    apply (IH (y2 :: ys) lo2); done.
  Qed.

  Lemma map_sequence_zip {B} (m1 : M A) (m2 : M B) lo hi xs (ys : list B) :
    dom m1 = dom m2 →
    map_sequence m1 lo hi xs →
    map_sequence m2 lo hi ys →
    map_sequence (map_zip m1 m2) lo hi (zip xs ys).
  Proof.
    intros domEq seq1 seq2.
    eassert _ as lenEq. { eapply map_sequence_dom_length; done. }
    generalize dependent lo.
    generalize dependent ys.
    induction xs as [|x1 [|x2 xs] IH]; first done.
    { intros [|y1 [|y2 ys]] ? ?; first done; last done.
      intros [look1 ->] [look2 _].
      split; last done.
      apply map_lookup_zip_with_Some.
      eexists _, _. split_and!; done. }
    intros [|y1 [|y2 ys]] ? ?; [done|done|].
    intros [look1 (lo2 & ? & all1 & seq1)].
    intros [look2 (lo2' & ? & all2 & seq2)].
    split. { apply map_lookup_zip_with_Some. naive_solver. }
    exists lo2.
    split; first done.
    split. { intros. apply map_lookup_zip_with_None. auto. }
    eassert (lo2 = lo2') as <-. { eapply map_sequence_lo_eq; done. }
    apply IH; try done.
    apply (inj S).
    apply lenEq.
  Qed.

End map_sequence_dom.

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

Section map_no_later_dom.
  Context `{FinMapDom nat M D} {A : Type}.

  Implicit Types m : M A.

  Lemma map_no_later_dom {B} (m1 : M A) (m2 : M B) t :
    dom m1 = dom m2 → map_no_later m1 t → map_no_later m2 t.
  Proof.
    intros domEq.
    rewrite /map_no_later.
    intros no t2 le.
    eapply map_dom_eq_lookup_None; first done.
    apply no. done.
  Qed.

End map_no_later_dom.

Definition drop_above {A} t (m : gmap nat A) : gmap nat A :=
  filter (λ '(t', ev), t' ≤ t) m.

Section drop_above.
  Context {A : Type}.
  Implicit Types (m : gmap nat A).

  (* Removes all entries from [m] after [t]. Note, there aren't that many lemmas
  about [drop_above]. In most cases we unfold it and use lemmas for [filter]. *)

  Lemma drop_above_fmap {B} t m (f : A → B) :
    f <$> drop_above t m = drop_above t (f <$> m).
  Proof. rewrite /drop_above. rewrite map_filter_fmap. done. Qed.

  Lemma drop_above_lookup_le m t1 t2 :
    t1 ≤ t2 → drop_above t2 m !! t1 = m !! t1.
  Proof.
    intros le.
    rewrite map_filter_lookup.
    destruct (m !! t1); last done. simpl.
    rewrite option_guard_True; done.
  Qed.

  Lemma drop_above_lookup_t m t :
    drop_above t m !! t = m !! t.
  Proof. apply drop_above_lookup_le. done. Qed.

  Lemma drop_above_lookup_gt m t1 t2 :
    t1 < t2 → drop_above t1 m !! t2 = None.
  Proof.
    intros gt. apply map_filter_lookup_None.
    right. intros ??. lia.
  Qed.

  Lemma map_no_later_drop_above t m :
    map_no_later (drop_above t m) t.
  Proof. rewrite /map_no_later => ??. apply drop_above_lookup_gt. done. Qed.

End drop_above.

Lemma drop_above_dom_eq {A B} t (m1 : gmap nat A) (m2 : gmap nat B) :
  dom m1 = dom m2 →
  dom (drop_above t m1) = dom (drop_above t m2).
Proof.
  rewrite !set_eq.
  setoid_rewrite elem_of_dom. unfold is_Some.
  intros eq. rewrite /drop_above.
  setoid_rewrite map_filter_lookup_Some.
  naive_solver.
Qed.

Lemma map_sequence_drop_above {A : Type} (m : gmap nat A) lo hi xs :
  map_sequence m lo hi xs →
  map_sequence (drop_above hi m) lo hi xs.
Proof.
  generalize dependent lo.
  induction xs as [|x1 xs IH]; first done.
  intros lo.
  destruct xs as [|x2 xs].
  { simpl. intros [??]. rewrite drop_above_lookup_t. done. }
  intros seq.
  eassert (lo ≤ hi). { eapply map_sequence_lt. done. }
  destruct seq as (look & lo' & ? & between & slice).
  eassert (lo' ≤ hi). { eapply map_sequence_lt. done. }
  split.
  { rewrite drop_above_lookup_le; done. }
  exists lo'.
  split; first done.
  split.
  { intros.
    rewrite drop_above_lookup_le; last lia.
    apply between. done. }
  apply IH.
  done.
Qed.

