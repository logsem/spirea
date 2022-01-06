(* Resource algebra to store the preorders that are associated with each
   location.

   The preorders are stored in encoded format in the RA because the preorder may
   be over an arbitrary type. *)

From iris.algebra Require Import auth gmap gmap_view.
From iris.base_logic.lib Require Import own.
From iris.heap_lang Require Export locations.
From iris.proofmode Require Import proofmode.

From self Require Import extra encode_relation.
From self.algebra Require Import ghost_map.

(* Resource algebra that stores the encoded preorder for each location. *)
Definition relationO := leibnizO (positive → positive → Prop).
(* Definition preordersG Σ := ghost_mapG Σ loc (relation2 positive). *)

Section preorders.
  (* Context `{preordersG Σ}. *)
  Context `{ghost_mapG Σ loc (relation2 positive)}.
  Context `{Countable A}.

  Implicit Type (preorders : gmap loc (relation2 positive)).

  Definition own_all_preorders γ preorders :=
    ghost_map_auth γ (DfracOwn 1) preorders.

  Definition own_know_preorder_loc γ ℓ (preorder : relation2 A) : iProp Σ :=
    ℓ ↪[γ]□ encode_relation preorder.

  Lemma own_all_preorders_gname_alloc (preorders : gmap loc (relation2 positive)) :
    ⊢ |==> ∃ γ,
      own_all_preorders γ preorders ∗ ([∗ map] ℓ ↦ p ∈ preorders, ℓ ↪[γ]□ p).
  Proof. by iMod (ghost_map_alloc_persistent). Qed.

  (* Lemma auth_valid_to_agree_singleton_l {B} *)
  (*       dq (m : gmap loc (leibnizO B)) e (ℓ : loc) : *)
  (*   ✓ (●{dq} (to_agree <$> m : gmapUR _ (agreeR _)) ⋅ *)
  (*      ◯ {[ℓ := to_agree e]}) → *)
  (*   m !! ℓ = Some e. *)
  (* Proof. *)
  (*   intros [_ [incl _]]%auth_both_dfrac_valid_discrete. *)
  (*   move: incl. *)
  (*   rewrite singleton_included_l. *)
  (*   intros [y [eq incl]]. *)
  (*   move: incl. *)
  (*   rewrite lookup_fmap in eq. *)
  (*   apply Some_equiv_eq in eq. *)
  (*   destruct eq as [y' [look' eq]]. *)
  (*   rewrite -eq. *)
  (*   rewrite <- look'. *)
  (*   rewrite option_included_total. *)
  (*   intros [|(? & ? & [= ?] & [= ?] & incl)]; first done. *)
  (*   destruct (m !! ℓ) as [encOrder|]; last done. *)
  (*   simpl in *. *)
  (*   simplify_eq. *)
  (*   setoid_rewrite to_agree_included in incl. *)
  (*   f_equiv. *)
  (*   apply leibniz_equiv. *)
  (*   done. *)
  (* Qed. *)

  Lemma orders_lookup γ ℓ order1 order2 (orders : gmap loc (relation2 positive)) :
    orders !! ℓ = Some order1 →
    own_all_preorders γ orders -∗
    own_know_preorder_loc γ ℓ order2 -∗
    ⌜order1 = encode_relation order2⌝.
  Proof.
    iIntros (look) "auth frag".
    iDestruct (ghost_map_lookup with "auth frag") as "%".
    iPureIntro. congruence.
  Qed.

End preorders.
