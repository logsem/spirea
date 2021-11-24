From stdpp Require Import gmap.

From self Require Export extra.

(* NOTE: The definition uses [i < j] and not [i ≤ j] in order to make the
lemma [increasing_map_singleton] provable. When we use [increasing_map] the
relation [R] will always be reflexive, and hence this does not matter. The
_knowledge_ that [R] is reflexive may not always be available however (since
we may not know that [R] is in fact the encoding of some preorder, and hence
this definition works best. *)
Definition increasing_map (R : relation2 positive) (ss : gmap nat positive) :=
  ∀ i j (s s' : positive),
    i < j → (ss !! i = Some s) → (ss !! j = Some s') → R s s'.

Lemma increasing_map_singleton R t s :
  increasing_map R {[ t := s ]}.
Proof. intros ????? ?%lookup_singleton_Some ?%lookup_singleton_Some. lia. Qed.

Lemma increasing_map_empty R : increasing_map R ∅.
Proof. intros ????? [=]. Qed.

Lemma increasing_map_insert order m t_i s_i :
  increasing_map order m →
  (forall t (s : positive), m !! t = Some s → t < t_i → order s s_i) →
  (forall t (s : positive), m !! t = Some s → t_i < t → order s_i s) →
  increasing_map order (<[t_i := s_i]> m).
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

Lemma increasing_map_insert_after order `{!Transitive order} m t_i s_i t_t s_t :
  increasing_map order m →
  m !! t_i = Some s_i →
  order s_i s_t →
  t_i < t_t →
  (forall t_c (s_c : positive),
    m !! t_c = Some s_c → t_i < t_c → order s_t s_c ∧ order s_c s_t) →
  increasing_map order (<[t_t := s_t]> m).
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

Lemma increasing_map_insert_last order `{!Transitive order} m t_l s_l t_t s_t :
  increasing_map order m →
  map_no_later m t_l →
  t_l < t_t →
  m !! t_l = Some s_l →
  order s_l s_t →
  increasing_map order (<[t_t := s_t]> m).
Proof.
  intros ? nolater ? ? ?.
  eapply increasing_map_insert_after; eauto.
  intros t b c lt.
  unfold map_no_later in *.
  specialize (nolater t lt).
  congruence.
Qed.
