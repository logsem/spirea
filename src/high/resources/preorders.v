(* Resource algebra to store the preorders that are associated with each
   location.

   The preorders are stored in encoded format in the RA because the preorder may
   be over an arbitrary type. *)

From iris.algebra Require Import auth gmap.
From iris.base_logic.lib Require Import own.
From iris.heap_lang Require Export locations.
From iris.proofmode Require Import proofmode.

From self Require Import extra encode_relation.

(* Resource algebra that stores the encoded preorder for each location. *)
Definition relationO := leibnizO (positive → positive → Prop).
Definition preordersR := authR (gmapUR loc (agreeR relationO)).

Section preorders.
  Context `{inG Σ preordersR}.
  Context `{Countable A}.

  Implicit Type (preorders : gmap loc (relation2 positive)).

  Definition map_to_agree preorders : gmapUR _ (agreeR relationO) :=
    to_agree <$> preorders.

  Definition own_all_preorders γ preorders :=
    own γ (● (map_to_agree preorders)).

  (* Definition own_all_preorders preorders := *)
  (*   own_all_preorders_gname preorders_name preorders. *)

  Definition own_know_preorder_loc γ ℓ (preorder : relation2 A) : iProp Σ :=
    own γ (◯ ({[ ℓ := to_agree (encode_relation preorder) ]})).

  (* Global Instance persistent_know_preorder_loc ℓ preorder : *)
  (*   Persistent (know_preorder_loc ℓ preorder). *)
  (* Proof. apply _. Qed. *)

  Lemma own_all_preorders_gname_alloc (preorders : gmap loc (relation2 positive)) :
    ⊢ |==> ∃ γ, own_all_preorders γ preorders ∗
                own γ (◯ ((to_agree <$> preorders) : gmapUR _ (agreeR relationO))).
  Proof.
    setoid_rewrite <- own_op.
    iApply own_alloc.
    apply auth_both_valid_discrete. split; first done.
    rewrite /map_to_agree.
    apply (valid_to_agree_fmap (B := relationO) preorders).
  Qed.

  Lemma own_all_preorders_persist γ preorders :
    own_all_preorders γ preorders ==∗
    own γ (●□ ((to_agree <$> preorders) : gmapUR _ (agreeR relationO))).
  Proof. iApply own_update. apply auth_update_auth_persist. Qed.

  Lemma auth_valid_to_agree_singleton_l {B}
        dq (m : gmap loc (leibnizO B)) e (ℓ : loc) :
    ✓ (●{dq} (to_agree <$> m : gmapUR _ (agreeR _)) ⋅
       ◯ {[ℓ := to_agree e]}) →
    m !! ℓ = Some e.
  Proof.
    intros [_ [incl _]]%auth_both_dfrac_valid_discrete.
    move: incl.
    rewrite singleton_included_l.
    intros [y [eq incl]].
    move: incl.
    rewrite lookup_fmap in eq.
    apply Some_equiv_eq in eq.
    destruct eq as [y' [look' eq]].
    rewrite -eq.
    rewrite <- look'.
    rewrite option_included_total.
    intros [|(? & ? & [= ?] & [= ?] & incl)]; first done.
    destruct (m !! ℓ) as [encOrder|]; last done.
    simpl in *.
    simplify_eq.
    setoid_rewrite to_agree_included in incl.
    f_equiv.
    apply leibniz_equiv.
    done.
  Qed.

  Lemma own_all_preorders_singleton_frag dq γ (ℓ : loc) preorders
        (preorder : relation A) :
    own γ (●{dq} (map_to_agree preorders)) -∗
    own γ (◯ ({[ ℓ := to_agree (encode_relation preorder)]})) -∗
    ⌜preorders !! ℓ = Some (encode_relation preorder)⌝.
  Proof.
    iIntros "auth frag".
    iDestruct (own_valid_2 with "auth frag") as %V.
    iPureIntro.
    eapply auth_valid_to_agree_singleton_l.
    apply V.
  Qed.

  Lemma orders_lookup γ ℓ order1 order2 (orders : gmap loc (relation2 positive)) :
    orders !! ℓ = Some order1 →
    own_all_preorders γ orders -∗
    own_know_preorder_loc γ ℓ order2 -∗
    ⌜order1 = encode_relation order2⌝.
  Proof.
    iIntros (look) "auth frag".
    iDestruct (own_all_preorders_singleton_frag with "auth frag")
      as %look'.
    simplify_eq. done.
  Qed.

  Lemma orders_frag_lookup γ preorders (ℓ : loc) order :
    preorders !! ℓ = Some order →
    own γ (◯ (map_to_agree preorders)) -∗
    own γ (◯ ({[ ℓ := to_agree order ]} : gmapUR _ (agreeR relationO))).
  Proof.
    intros look. f_equiv. simpl.
    apply auth_frag_mono.
    rewrite singleton_included_l.
    eexists _.
    rewrite lookup_fmap look.
    naive_solver.
  Qed.

End preorders.
