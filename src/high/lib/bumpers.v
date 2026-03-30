From stdpp Require Import countable ssreflect.
From self Require Export options.

(* Pure facts about bumpers *)
Section bumpers.
  Context `{Countable ST}.
  
  Definition encode_bumper (bumper : ST → ST) :=
    λ e, encode <$> (bumper <$> decode e).

  Lemma encode_bumper_Some_decode (bumper : ST → ST) (x x' : positive) :
    encode_bumper bumper x = Some x' →
    ∃ (s : ST), decode x = Some s ∧ encode (bumper s) = x'.
  Proof.
    rewrite /encode_bumper => eq.
    destruct (decode x) as [s|].
    - exists s. inversion eq. done.
    - inversion eq.
  Qed.

  Lemma encode_bumper_encode (bumper : ST → ST) (s : ST) :
    encode_bumper bumper (encode s) = Some (encode (bumper s)).
  Proof. rewrite /encode_bumper. rewrite decode_encode. done. Qed.

  (* An encoded bumper returns some encoded value then that encoded value will
  also result in some other encoded bumper again. This represents that encoded
  bumpers take "valid" encodings to "valid" encodings. *)
  Lemma encode_bumper_bump_to_valid bumper e e' :
    encode_bumper bumper e = Some e' → is_Some (encode_bumper bumper e').
  Proof.
    intros (s' & ? & encodeEq)%encode_bumper_Some_decode.
    rewrite <- encodeEq. rewrite encode_bumper_encode. done.
  Qed.
End bumpers.
