From stdpp Require Import gmap.

From self Require Export extra.

(* NOTE: The definition uses [i < j] and not [i ≤ j] in order to make the
lemma [increasing_map_singleton] provable. When we use [increasing_map] the
relation [R] will always be reflexive, and hence this does not matter. The
_knowledge_ that [R] is reflexive may not always be available however (since
we may not know that [R] is in fact the encoding of some preorder, and hence
this definition works best. *)
Definition increasing_map {A} (R : relation2 A) (ss : gmap nat A) :=
  ∀ i j (s s' : A),
    i < j → (ss !! i = Some s) → (ss !! j = Some s') → R s s'.

Section increasing_map.
  Context {A : Type}.
  Implicit Types (s : A) (R : relation2 A).

  Lemma increasing_map_increasing `{!Reflexive R} m i j s1 s2 :
    increasing_map R m →
    i ≤ j →
    m !! i = Some s1 →
    m !! j = Some s2 →
    R s1 s2.
  Proof.
    unfold increasing_map.
    intros incr le lookI lookJ.
    destruct (le_lt_eq_dec _ _ le).
    - eapply incr; done.
    - simplify_eq. reflexivity.
  Qed.

  Lemma increasing_map_singleton R t s :
    increasing_map R {[ t := s ]}.
  Proof. intros ????? ?%lookup_singleton_Some ?%lookup_singleton_Some. lia. Qed.

  Lemma increasing_map_empty R : increasing_map R ∅.
  Proof. intros ????? [=]. Qed.

  Lemma increasing_map_insert R m t_i s_i :
    increasing_map R m →
    (forall t s, m !! t = Some s → t < t_i → R s s_i) →
    (forall t s, m !! t = Some s → t_i < t → R s_i s) →
    increasing_map R (<[t_i := s_i]> m).
  Proof.
    intros increasing before after.
    intros t1 t2 s1 s2 lt.
    destruct (decide (t_i = t1)) as [eq1|neq1];
      destruct (decide (t_i = t2)) as [eq2|neq2];
      subst; rewrite ?lookup_insert; rewrite ?lookup_insert_ne; try done.
    - lia.
    - intros [= ->] ?.
      eapply after; done.
    - intros ? [= ->].
      eapply before; done.
    - by apply increasing.
  Qed.

  Lemma increasing_map_insert_after R `{!Transitive R} m t_i t_t s_i s_t :
    increasing_map R m →
    m !! t_i = Some s_i →
    R s_i s_t →
    t_i < t_t →
    (forall t_c (s_c : A),
      m !! t_c = Some s_c → t_i < t_c → R s_t s_c ∧ R s_c s_t) →
    increasing_map R (<[t_t := s_t]> m).
  Proof.
    intros increasing look sLe tLe par.
    intros t1 t2 s1 s2 lt.
    destruct (decide (t_t = t1)) as [eq1|neq1];
      destruct (decide (t_t = t2)) as [eq2|neq2].
      (* subst; rewrite ?lookup_insert; try (rewrite lookup_insert_ne; last done). *)
    - lia.
    - subst.
      rewrite lookup_insert.
      rewrite lookup_insert_ne; last done.
      intros [= ->] ?.
      eapply par; [done | lia].
    - rewrite <- eq2 in *.
      rewrite lookup_insert_ne; last done.
      rewrite lookup_insert.
      intros look2 [= ->].
      pose proof (Nat.lt_total t_i t1) as [lt2|[?|?]].
      * eapply par; done.
      * simplify_eq. done.
      * etrans; last apply sLe.
        eapply increasing; [| apply look2 | apply look].
        lia.
    - do 2 (rewrite lookup_insert_ne; last done).
      by apply increasing.
  Qed.

  Lemma increasing_map_insert_last R `{!Transitive R} m t_l s_l t_t s :
    increasing_map R m →
    map_no_later m t_l →
    t_l < t_t →
    m !! t_l = Some s_l →
    R s_l s →
    increasing_map R (<[t_t := s]> m).
  Proof.
    intros ? nolater ? ? ?.
    eapply increasing_map_insert_after; eauto.
    intros t b c lt.
    unfold map_no_later in *.
    specialize (nolater t lt).
    congruence.
  Qed.

End increasing_map.

Definition increasing_list {A} (R : relation A) (ss : list A) :=
  ∀ i j s s', i < j → (ss !! i = Some s) → (ss !! j = Some s') → R s s'.

Section increasing_list.
  Context {A : Type}.
  Implicit Types (s : A) (R : relation2 A).

  (* Context `{SqSubsetEq ST, !PreOrder (⊑@{ST})}. *)
  (* Implicit Types (s : ST). *)

  Lemma increasing_list_singleton R s : increasing_list R [s].
  Proof. intros [|][|]?????; try naive_solver. lia. Qed.

  Lemma lookup_snoc_Some (l : list A) x x2 i :
    (l ++ [x]) !! i = Some x2 →
    (l !! i = Some x2) ∨ (length l = i ∧ x = x2).
  Proof.
    intros [look|[? [??]%list_lookup_singleton_Some]]%lookup_app_Some.
    - left. apply look.
    - right. auto with lia.
  Qed.

  Lemma increasing_list_last_greatest R `{!PreOrder R} ss s i s' :
    increasing_list R ss →
    last ss = Some s →
    ss !! i = Some s' →
    R s' s.
  Proof.
    rewrite last_lookup.
    unfold increasing_list.
    intros incr lookLast look.
    destruct (decide (i = pred (length ss))).
    { simplify_eq. reflexivity. }
    eapply incr; try done.
    apply lookup_lt_Some in look.
    lia.
  Qed.

  Lemma increasing_list_snoc `{!PreOrder R} xs xs__last (x : A) :
    (last xs) = Some xs__last →
    R xs__last x →
    increasing_list R xs → increasing_list R (xs ++ [x]).
  Proof.
    intros last incl incr.
    intros ?????.
    intros [?|[??]]%lookup_snoc_Some; intros [look|[??]]%lookup_snoc_Some.
    * eapply incr; done.
    * simplify_eq.
      etrans; last apply incl.
      eapply increasing_list_last_greatest; done.
    * apply lookup_lt_Some in look. lia.
    * lia.
  Qed.

  (** A lemma that ties [increasing_map] and [increasing_list] together. *)
  Lemma increasing_map_to_increasing_list R m lo hi l :
    increasing_map R m → map_slice m lo hi l → increasing_list R l.
  Proof.
    intros incr sl.
    intros ?? ?? lt look1 look2.
  Admitted. (* Prove this later if we need it. *)

End increasing_list.
