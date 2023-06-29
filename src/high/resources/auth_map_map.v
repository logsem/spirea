From iris.algebra Require Import auth gmap.
From iris.base_logic.lib Require Import own.
From iris.proofmode Require Import proofmode.

From self.lang Require Import lang.
From self Require Import extra.

Definition auth_map_mapR (A : ofe) :=
  authR (gmapUR loc (gmapUR time (agreeR A))).

Definition fmap_fmap_to_agree_ol (m : gmap loc (gmap time positive)) : gmapUR loc _ :=
  (λ n : gmap _ _, to_agree <$> n) <$> m.

Section fmap_fmap_to_agree.
  Context {A : ofe}.
  Implicit Types (m : gmap loc (gmap time A)).

  Definition fmap_fmap_to_agree m : gmap loc (gmap time (agreeR A)) :=
    (λ n : gmap _ _, (to_agree) <$> n) <$> m.

  Lemma fmap_fmap_to_agree_valid m : ✓ fmap_fmap_to_agree m.
  Proof.
    rewrite /fmap_fmap_to_agree.
    intros ?.
    rewrite lookup_fmap.
    destruct (m !! i); last done.
    simpl.
    apply Some_valid.
    apply valid_to_agree_fmap.
  Qed.

  Lemma fmap_fmap_to_agree_mono m1 m2 :
    m1 ⊆ m2 → fmap_fmap_to_agree m1 ≼ fmap_fmap_to_agree m2.
  Proof.
    rewrite map_subseteq_spec.
    intros sub.
    rewrite /fmap_fmap_to_agree.
    rewrite lookup_included.
    setoid_rewrite lookup_fmap.
    intros i.
    destruct (m1 !! i) eqn:eq.
    2: { eexists _. rewrite left_id. reflexivity. }
    rewrite (sub i g); last done.
    done.
  Qed.

  Lemma fmap_fmap_to_agree_singleton_included_l `{!LeibnizEquiv A}
        m (i : loc) (x : gmap time A) :
    fmap_fmap_to_agree {[ i := x ]} ≼ fmap_fmap_to_agree m →
    (∃ (y : gmap _ _), m !! i ≡ Some y ∧ x ⊆ y).
  Proof.
    rewrite /fmap_fmap_to_agree.
    rewrite map_fmap_singleton.
    rewrite singleton_included_l.
    rewrite lookup_fmap.
    intros [agh [equiv incl]].
    apply fmap_Some_equiv in equiv as [h [look equiv]].
    exists h.
    split; first by rewrite look. 
    move: incl.
    rewrite Some_included_total.
    rewrite equiv.
    rewrite -to_agree_fmap. done.
  Qed.

  Lemma fmap_fmap_to_agree_incl `{!LeibnizEquiv A} m m' :
    dom m ⊆ dom m' →
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
    apply to_agree_fmap.
    eapply subIn; done.
  Qed.

  Lemma fmap_fmap_to_agree_singleton ℓ h :
    fmap_fmap_to_agree {[ℓ := h]} = {[ℓ := to_agree <$> h]}.
  Proof. by rewrite /fmap_fmap_to_agree map_fmap_singleton. Qed.

End fmap_fmap_to_agree.

Section auth_map_map.
  Context {A : ofe}.
  Context `{inG Σ (auth_map_mapR A)}.

  Implicit Types (m : gmap loc (gmap time A)).

  Definition auth_map_map_auth γ m :=
    own γ (● (fmap_fmap_to_agree m)).

  Definition auth_map_map_auth_dq γ dq m :=
    own γ (●{dq} (fmap_fmap_to_agree m)).

  Definition auth_map_map_frag γ m :=
    own γ (◯ (fmap_fmap_to_agree m)).

  Definition auth_map_map_frag_singleton γ ℓ t a :=
    auth_map_map_frag γ {[ ℓ := {[ t := a ]} ]}.

  Lemma auth_map_map_alloc m :
    ⊢ |==> ∃ γ, auth_map_map_auth γ m ∗ auth_map_map_frag γ m.
  Proof.
    rewrite /auth_map_map_auth /auth_map_map_frag.
    setoid_rewrite <- own_op.
    iApply own_alloc.
    apply auth_both_valid_2.
    - apply fmap_fmap_to_agree_valid.
    - done.
  Qed.

  Lemma auth_map_map_lookup `{!LeibnizEquiv A} γ m ℓ t h a :
    m !! ℓ = Some h →
    h !! t = Some a →
    auth_map_map_auth γ m ==∗
    auth_map_map_auth γ m ∗ auth_map_map_frag_singleton γ ℓ t a.
  Proof.
    iIntros (mLook hLook) "N".
    rewrite /auth_map_map_auth /auth_map_map_frag. setoid_rewrite <- own_op.
    iApply (own_update with "N").
    apply: auth_update_dfrac_alloc.
    rewrite fmap_fmap_to_agree_singleton.
    eapply singleton_included_look.
    { rewrite /fmap_fmap_to_agree lookup_fmap mLook /=. reflexivity. }
    simpl.
    rewrite map_fmap_singleton.
    eapply singleton_included_look.
    { rewrite lookup_fmap. rewrite hLook. simpl. reflexivity. }
    { done. }
  Qed.

  Lemma auth_map_map_insert_top `{!LeibnizEquiv A} γ m ℓ hist :
    m !! ℓ = None →
    auth_map_map_auth γ m ==∗
    auth_map_map_auth γ (<[ℓ:=hist]> m) ∗
    auth_map_map_frag γ {[ ℓ := hist ]}.
  Proof.
    iIntros (look).
    rewrite -own_op.
    iApply own_update.
    apply auth_update_alloc.
    rewrite /fmap_fmap_to_agree.
    rewrite fmap_insert.
    rewrite map_fmap_singleton.
    apply alloc_local_update.
    - rewrite lookup_fmap look. done.
    - apply valid_to_agree_fmap.
  Qed.

  (* NOTE: The requirement on leibniz equiv may not be strictly necessary, but
  it is convenient right now. *)
  Lemma auth_map_map_insert `{!LeibnizEquiv A} γ m ℓ t h a :
    m !! ℓ = Some h →
    h !! t = None →
    auth_map_map_auth γ m ==∗
    auth_map_map_auth γ (<[ℓ:=<[t:=a]> h]> m) ∗
      auth_map_map_frag γ ({[ ℓ:=<[t:=a]> h ]}) ∗
      auth_map_map_frag_singleton γ ℓ t a.
  Proof.
    iIntros (mLook hLook) "N".
    iMod (own_update _ _ (● fmap_fmap_to_agree (<[ℓ:=<[t:=a]> h]> m)) with "N ") as "H".
    { apply auth_auth_grow.
      { apply fmap_fmap_to_agree_valid. }
      apply fmap_fmap_to_agree_incl.
      * set_solver.
      * intros ℓ' mi mi' look1 look2.
        destruct (decide (ℓ = ℓ')).
        + simplify_eq.
          rewrite lookup_insert in look2.
          simplify_eq.
          by apply insert_subseteq.
        + rewrite lookup_insert_ne in look2; last done.
          simplify_eq.
          reflexivity. }
    rewrite assoc. rewrite comm.
    iMod (own_update with "H") as "[H $]".
    { apply: auth_update_dfrac_alloc.
      rewrite /fmap_fmap_to_agree.
      rewrite -> fmap_insert.
      rewrite map_fmap_singleton.
      apply singleton_included_insert.
      apply to_agree_fmap.
      apply map_singleton_subseteq_l.
      apply lookup_insert. }
    iMod (own_update with "H") as "[$ $]".
    { apply: auth_update_dfrac_alloc.
      rewrite /fmap_fmap_to_agree.
      rewrite -> fmap_insert.
      rewrite map_fmap_singleton.
      apply singleton_included_insert.
      apply to_agree_fmap.
      reflexivity. }
    done.
  Qed.

  Lemma auth_map_map_auth_frag `{!OfeDiscrete A} `{!LeibnizEquiv A} γ dq m ℓ t a :
    auth_map_map_auth_dq γ dq m -∗
    auth_map_map_frag_singleton γ ℓ t a -∗
    ⌜ ∃ h, m !! ℓ = Some h ∧ h !! t = Some a ⌝.
  Proof.
    iIntros "O F".
    iDestruct (own_valid_2 with "O F") as %V.
    iPureIntro.
    apply auth_both_dfrac_valid_discrete in V as (_ & incl & _).
    apply fmap_fmap_to_agree_singleton_included_l in incl.
    destruct incl as (h & equiv & sub).
    exists h.
    split. { apply leibniz_equiv. apply equiv. }
    apply map_singleton_subseteq_l. done.
  Qed.

  Lemma auth_map_map_frag_lookup `{!LeibnizEquiv A} γ m ℓ h :
    m !! ℓ = Some h →
    auth_map_map_frag γ m -∗
    auth_map_map_frag γ {[ ℓ := h ]}.
  Proof.
    iIntros (mLook).
    rewrite /auth_map_map_frag.
    rewrite /auth_map_map_frag_singleton.
    rewrite /auth_map_map_frag.
    iApply own_mono.
    simpl.
    apply auth_frag_mono.
    rewrite /fmap_fmap_to_agree.
    rewrite map_fmap_singleton.
    apply singleton_included_l.
    eexists _.
    split. { rewrite lookup_fmap. rewrite mLook. simpl. reflexivity. }
    done.
  Qed.

  Lemma auth_map_map_frag_lookup_singleton `{!LeibnizEquiv A} γ m ℓ h t a :
    m !! ℓ = Some h →
    h !! t = Some a →
    auth_map_map_frag γ m -∗
    auth_map_map_frag_singleton γ ℓ t a.
  Proof.
    iIntros (mLook hLook).
    rewrite /auth_map_map_frag.
    rewrite /auth_map_map_frag_singleton.
    rewrite /auth_map_map_frag.
    iApply own_mono.
    simpl.
    apply auth_frag_mono.
    rewrite /fmap_fmap_to_agree.
    rewrite map_fmap_singleton.
    apply singleton_included_l.
    eexists _.
    split. { rewrite lookup_fmap. rewrite mLook. simpl. reflexivity. }
    apply Some_included_total.
    apply to_agree_fmap.
    apply map_singleton_subseteq_l.
    done.
  Qed.

  Lemma auth_map_map_lookup_agree `{!OfeDiscrete A} `{!LeibnizEquiv A} γ m ℓ h t a a' :
    m !! ℓ = Some h →
    h !! t = Some a →
    auth_map_map_auth γ m -∗
    auth_map_map_frag_singleton γ ℓ t a' -∗
    ⌜ a = a' ⌝.
  Proof.
    iIntros (mLook hLook) "O F".
    iDestruct (auth_map_map_auth_frag with "O F") as %(? & ? & ?).
    iPureIntro. congruence.
  Qed.

End auth_map_map.
