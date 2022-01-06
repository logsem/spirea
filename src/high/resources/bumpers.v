From iris.algebra Require Import gmap auth gmap_view.
From iris.base_logic.lib Require Import own.
From iris.heap_lang Require Export locations.
From iris.proofmode Require Import proofmode.

From self Require Import extra.
From self.algebra Require Import ghost_map.
From self.high Require Import abstract_state.

Definition bumpersR :=
  (* authR (gmapUR loc (agreeR (leibnizO (positive → option positive)))). *)
  gmap_viewR loc (leibnizO (positive → option positive)).

Notation bumpersG Σ := (ghost_mapG Σ loc (positive → option positive)).

Section bumpers.
  Context `{bumpersG Σ}.
  Context `{AbstractState ST}.

  Definition encode_bumper (bumper : ST → ST) :=
    λ e, encode <$> (bumper <$> decode e).

  Definition own_know_bumper γ (ℓ : loc) (bumper : ST → ST) : iProp Σ :=
    let encodedBumper := encode_bumper bumper
    in ⌜∀ s1 s2, s1 ⊑ s2 → bumper s1 ⊑ bumper s2⌝ ∗
       ℓ ↪[γ]□ encodedBumper.
       (* own γ ((◯ {[ ℓ := to_agree encodedBumper ]}) : bumpersR). *)

  Definition own_all_bumpers γ encoded_bumpers :=
    ghost_map_auth γ (DfracOwn 1) encoded_bumpers.
    (* own γ (● (to_agree <$> encoded_bumpers) : bumpersR). *)

  (* Definition own_all_bumpers encoded_bumpers := *)
  (*   own_all_bumpers bumpers_name encoded_bumpers. *)

  Lemma own_all_bumpers_alloc bumpers :
    ⊢ |==> ∃ γ, own_all_bumpers γ bumpers ∗
                ([∗ map] ℓ ↦ bumper ∈ bumpers, ℓ ↪[γ]□ bumper).
  Proof.
    (* TODO: Add some more lemmas to ghost_map that will make this easy. *)
  Admitted.
  (*   (* iApply ghost_map_alloc. *) *)
  (* Qed. *)

  (* Lemma own_all_bumpers_persist γ encoded_bumpers : *)
  (*   own_all_bumpers γ encoded_bumpers ==∗ *)
  (*   own γ (●□ ((to_agree <$> encoded_bumpers) : gmapUR _ (agreeR _))). *)
  (* Proof. iApply own_update. apply auth_update_auth_persist. Qed. *)

  (* Lemma bumpers_frag_extract γ (bumpers : gmap loc (positive → option positive)) *)
  (*       (ℓ : loc) (bumper : positive → option positive) : *)
  (*   bumpers !! ℓ = Some bumper → *)
  (*   own γ (◯ (to_agree <$> bumpers) : bumpersR) -∗ *)
  (*   own γ (◯ {[ ℓ := to_agree bumper ]}). *)
  (* Proof. *)
  (*   intros look. f_equiv. simpl. *)
  (*   apply auth_frag_mono. *)
  (*   rewrite singleton_included_l. *)
  (*   eexists _. *)
  (*   rewrite lookup_fmap look. *)
  (*   naive_solver. *)
  (* Qed. *)

  Lemma own_all_bumpers_insert (bumpers : gmap loc _) ℓ γ (bumper : ST → ST)
        `{!Proper ((⊑@{ST}) ==> (⊑))%signature bumper} :
    bumpers !! ℓ = None →
    own_all_bumpers γ bumpers ==∗
    own_all_bumpers γ (<[ℓ := encode_bumper bumper]>bumpers) ∗ own_know_bumper γ ℓ bumper.
  Proof.
    rewrite /own_all_bumpers /own_know_bumper. iIntros (look) "A".
    iMod (ghost_map_insert_persist with "A") as "[$ $]"; done.
  Qed.

  Definition bumperO := leibnizO (positive → option positive).

  Lemma bumpers_lookup γ ℓ encoded_bumpers bumper :
    own_all_bumpers γ encoded_bumpers -∗
    own_know_bumper γ ℓ bumper -∗
    ⌜ encoded_bumpers !! ℓ = Some (encode_bumper bumper) ⌝.
  Proof.
    iIntros "A [mono F]".
    iDestruct (ghost_map_lookup with "A F") as "$".
  Qed.

End bumpers.
