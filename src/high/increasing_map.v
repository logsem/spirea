From stdpp Require Import gmap.
From iris.proofmode Require Import tactics.

From self Require Export extra map_extra.

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

  Lemma increasing_map_increasing_base R m i j s1 s2 :
    R s1 s1 →
    increasing_map R m →
    i ≤ j →
    m !! i = Some s1 →
    m !! j = Some s2 →
    R s1 s2.
  Proof.
    unfold increasing_map.
    intros refl incr le lookI lookJ.
    destruct (le_lt_eq_dec _ _ le).
    - eapply incr; done.
    - simplify_eq. assumption.
  Qed.

  Lemma increasing_map_increasing `{!Reflexive R} m i j s1 s2 :
    increasing_map R m →
    i ≤ j →
    m !! i = Some s1 →
    m !! j = Some s2 →
    R s1 s2.
  Proof. apply increasing_map_increasing_base. reflexivity. Qed.

  Lemma increasing_map_lookup_lt `{!Reflexive R} m t1 t2 s1 s2 :
    increasing_map R m →
    m !! t1 = Some s1 →
    m !! t2 = Some s2 →
    ¬ (R s2 s1) →
    t1 < t2.
  Proof.
    rewrite /increasing_map.
    intros increasing look1 look2 neg.
    destruct (decide (t1 < t2)); first done.
    exfalso.
    apply neg.
    eapply increasing_map_increasing; [done| |eassumption|eassumption]. lia.
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

  (* NOTE: We probably could've used the [increasing_map_insert] lemma above to
  show the three insert lemmas below. *)

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

  Lemma increasing_map_insert_succ R `{!Transitive R} m t_i s_i s_t :
    increasing_map R m →
    m !! t_i = Some s_i →
    R s_i s_t →
    (∀ t_c (s_c : A),
      m !! t_c = Some s_c → (S t_i) < t_c → R s_t s_c) →
    increasing_map R (<[(t_i + 1) := s_t]> m).
  Proof.
    intros increasing look sLe tLe.
    intros t1 t2 s1 s2 lt.
    destruct (decide ((t_i + 1) = t1)) as [eq1|neq1];
      destruct (decide ((t_i + 1) = t2)) as [eq2|neq2].
    - lia.
    - subst.
      rewrite lookup_insert.
      rewrite lookup_insert_ne; last done.
      intros [= ->] ?.
      eapply tLe; [done | lia].
    - subst.
      rewrite lookup_insert_ne; last done.
      rewrite lookup_insert.
      intros look2 [= <-].
      assert (t1 = t_i ∨ t1 < t_i) as [<-|ho] by lia.
      * simplify_eq. done.
      * etrans; last apply sLe.
        rewrite /increasing_map in increasing.
        eapply increasing; done.
    - do 2 (rewrite lookup_insert_ne; last done).
      apply increasing; done.
  Qed.

  Lemma increasing_map_fmap R m f `{!Proper (R ==> R) f} :
    increasing_map R m →
    increasing_map R (f <$> m).
  Proof.
    intros incr.
    intros ????? (? & <- & ?)%lookup_fmap_Some (? & <- & ?)%lookup_fmap_Some.
    f_equiv.
    eapply incr; done.
  Qed.

  Lemma increasing_map_filter R P `{∀ x, Decision (P x)} m :
    increasing_map R m →
    increasing_map R (filter P m).
  Proof.
    intros incr.
    intros ????? [??]%map_filter_lookup_Some [??]%map_filter_lookup_Some.
    eapply incr; done.
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

  Lemma increasing_list_lookup_le `{!PreOrder R} xs i j (x y : A) :
    increasing_list R xs →
    xs !! i = Some x →
    xs !! j = Some y →
    i ≤ j →
    R x y.
  Proof.
    intros incr look1 look2 [lt | ->]%Nat.lt_eq_cases.
    - naive_solver.
    - simplify_eq. reflexivity.
  Qed.

  Lemma increasing_list_last_greatest R `{!PreOrder R} ss s i s' :
    increasing_list R ss →
    ss !! i = Some s' →
    last ss = Some s →
    R s' s.
  Proof.
    rewrite last_lookup.
    intros ? look ?.
    eapply increasing_list_lookup_le; try done.
    apply lookup_lt_Some in look.
    lia.
  Qed.

  Lemma increasing_list_snoc `{!PreOrder R} xs xs__last (x : A) :
    last xs = Some xs__last →
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

  Lemma prefix_increasing_list_snoc R `{!PreOrder R} (ss1 : list A) s1 ss2 s2 :
    increasing_list R (ss2 ++ [s2]) →
    ss1 ++ [s1] `prefix_of` ss2 ++ [s2] →
    R s1 s2.
  Proof.
    intros incr pref.
    apply: increasing_list_last_greatest; eauto using last_snoc.
    eapply prefix_lookup_Some; last done.
    apply lookup_app_Some.
    right.
    split; first done.
    replace (length _ - length _) with 0 by lia.
    done.
  Qed.

  (** A lemma that ties [increasing_map] and [increasing_list] together. *)
  Lemma increasing_map_to_increasing_list R m lo hi l :
    increasing_map R m → map_sequence m lo hi l → increasing_list R l.
  Proof.
    intros incr sl.
    intros ?? ?? lt look1 look2.
    eassert _ as H. { eapply map_sequence_list_lookup_mono; done. }
    destruct H as (? & ? & ? & ? & ?).
    eapply incr; done.
  Qed.

End increasing_list.
