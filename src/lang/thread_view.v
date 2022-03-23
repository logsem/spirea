From self.algebra Require Export view.

Notation thread_view := (view * view * view)%type.

Instance thread_view_bottom : Bottom thread_view := ε.

Notation store_view tv := (tv.1).1.
Notation flush_view tv := (tv.1).2.
Notation buffer_view tv := (tv.2).

(* A few lattice rules for thread_view. *)

Lemma thread_view_sqsubseteq_antisym (TV1 TV2 : thread_view) :
  TV1 ⊑ TV2 → TV2 ⊑ TV1 → TV1 = TV2.
Proof.
  destruct TV1 as [[??]?]. destruct TV2 as [[??]?]. intros [[??] ?] [[??] ?].
  rewrite 2!pair_equal_spec.
  auto using view_sqsubseteq_antisym.
Qed.

Lemma thread_view_le_l (tv1 tv2 : thread_view) : tv1 ⊑ tv1 ⊔ tv2.
Proof.
  destruct tv1 as [[??]?], tv2 as [[??]?].
  repeat split; apply view_le_l.
Qed.

Lemma thread_view_le_r (tv1 tv2 : thread_view) : tv1 ⊑ tv2 ⊔ tv1.
Proof.
  destruct tv1 as [[??]?], tv2 as [[??]?].
  repeat split; apply view_le_r.
Qed.

Lemma thread_view_le (SV1 SV2 FV1 FV2 BV1 BV2 : view) :
  SV1 ⊑ SV2 →
  FV1 ⊑ FV2 →
  BV1 ⊑ BV2 →
  (SV1, FV1, BV1) ⊑ (SV2, FV2, BV2).
Proof. done. Qed.

Lemma thread_view_lub (SV1 SV2 FV1 FV2 BV1 BV2 : view) :
  (SV1, FV1, BV1) ⊔ (SV2, FV2, BV2) = (SV1 ⊔ SV2, FV1 ⊔ FV2, BV1 ⊔ BV2).
Proof. done. Qed.
