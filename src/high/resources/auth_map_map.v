From iris.algebra Require Import auth gmap.

From self.lang Require Import lang.
From self Require Import extra.

Definition auth_map_mapR (A : ofe) :=
  authR (gmapUR loc (gmapUR time (agreeR A))).

Definition fmap_fmap_to_agree_ol (m : gmap loc (gmap time positive)) : gmapUR loc _ :=
  (λ n : gmap _ _, to_agree <$> n) <$> m.

(* Set Printing All. *)
(* Print fmap_fmap_to_agree_ol. *)
(* positiveO *)

Section fmap_fmap_to_agree.
  Context {A : Type}.

  Definition fmap_fmap_to_agree (m : gmap loc (gmap time A)) : gmapUR loc (gmapUR time (agreeR (leibnizO A))) :=
    (λ n : gmap _ _, (to_agree) <$> n) <$> m.

  Lemma fmap_fmap_to_agree_valid m : ✓ fmap_fmap_to_agree m.
  Proof.
    rewrite /fmap_fmap_to_agree.
    intros ?.
    rewrite lookup_fmap.
    destruct (m !! i); last done.
    simpl.
    apply Some_valid.
    apply (valid_to_agree_fmap (B := leibnizO A)).
  Qed.

  Lemma fmap_fmap_to_agree_incl (* `{!LeibnizEquiv A} *) m m' :
    dom (gset _) m ⊆ dom _ m' →
    (∀ ℓ mi mi', m !! ℓ = Some mi → m' !! ℓ = Some mi' → mi ⊆ mi') →
    (fmap_fmap_to_agree m) ≼ (fmap_fmap_to_agree m').
  Proof.
    intros subOut subIn.
    rewrite /fmap_fmap_to_agree.
    apply lookup_included => ℓ.
    rewrite 2!lookup_fmap.
    destruct (m !! ℓ) as [mi|] eqn:lookM.
    2: { apply option_included. naive_solver. }
    destruct (m' !! ℓ) as [mi'|] eqn:lookM'.
    2: { exfalso.
         apply not_elem_of_dom in lookM'.
         apply elem_of_dom_2 in lookM.
         set_solver. }
    simpl.
    apply Some_included_total.
    apply (to_agree_fmap (A := leibnizO A)).
    eapply subIn; done.
  Qed.

End fmap_fmap_to_agree.
