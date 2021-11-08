From stdpp Require Import countable.
From iris.base_logic.lib Require Import own.

From self Require Import extra.

Section encode_relation.
  Context `{Countable A}.
  Implicit Type (R : relation2 A).

  Definition encode_relation R : relation2 positive :=
    λ (a b : positive), default False (R <$> decode a <*> decode b).

  Lemma encode_relation_iff R (a b : A) :
    R a b ↔ (encode_relation R) (encode a) (encode b).
  Proof.
    rewrite /encode_relation.
    rewrite !decode_encode.
    reflexivity.
  Qed.

  (* If we know that two encoded values are related by an encoded relation, then
  we can "recover" related unencoded values taht are related by the unencoded
  relation. *)
  Lemma encode_relation_inv R ea eb :
    (encode_relation R) ea eb →
    ∃ a b, decode ea = Some a ∧ decode eb = Some b ∧ R a b.
  Proof.
    rewrite /encode_relation.
    destruct (decode ea) as [|], (decode eb) as [|]; try done.
    intros ?. eexists _, _. done.
  Qed.

  Lemma encode_relation_decode_iff R ea eb (a b : A) :
    decode ea = Some a →
    decode eb = Some b →
    (encode_relation R) ea eb ↔ R a b.
  Proof. rewrite /encode_relation. intros -> ->. done. Qed.

  Lemma encode_relation_decode_iff_1 R ea eb (a b : A) :
    decode ea = Some a →
    decode eb = Some b →
    (encode_relation R) ea eb →
    R a b.
  Proof. rewrite /encode_relation. intros -> ->. done. Qed.

  Lemma encode_relation_decode_iff_2 R ea eb (a b : A) :
    decode ea = Some a →
    decode eb = Some b →
    R a b →
    (encode_relation R) ea eb.
  Proof. rewrite /encode_relation. intros -> ->. done. Qed.

  Global Instance encode_relation_trans R :
    Transitive R → Transitive (encode_relation R).
  Proof.
    intros T. intros encX encY encZ.
    intros (x & y & decX & decY & Rxy)%encode_relation_inv.
    intros (? & z & ? & decZ & Ryz)%encode_relation_inv.
    simplify_eq.
    eapply encode_relation_decode_iff; [done|done|].
    etrans; done.
  Qed.

End encode_relation.
