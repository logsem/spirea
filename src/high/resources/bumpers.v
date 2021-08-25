From iris.algebra Require Import gmap auth.
From iris.base_logic.lib Require Import own.
From iris.heap_lang Require Export locations.
From iris.proofmode Require Import proofmode.

From self Require Import extra.
From self.high Require Import abstract_state.

Definition bumpersR :=
  authR (gmapUR loc (agreeR (leibnizO (positive → option positive)))).

Section bumpers.
  Context `{inG Σ bumpersR}.
  Context `{AbstractState ST}.

  Definition own_know_bumper γ (ℓ : loc) (bumper : ST → ST) : iProp Σ :=
    let encodedBumper e := encode <$> (bumper <$> decode e)
    in ⌜∀ s1 s2, s1 ⊑ s2 → bumper s1 ⊑ bumper s2⌝ ∗
       own γ ((◯ {[ ℓ := to_agree encodedBumper ]}) : bumpersR).

  Definition own_all_bumpers γ encoded_bumpers :=
    own γ (● (to_agree <$> encoded_bumpers) : bumpersR).

  (* Definition own_all_bumpers encoded_bumpers := *)
  (*   own_all_bumpers bumpers_name encoded_bumpers. *)

  Lemma own_all_bumpers_alloc bumpers :
    ⊢ |==> ∃ γ, own_all_bumpers γ bumpers ∗
                own γ (◯ ((to_agree <$> bumpers) : gmapUR _ (agreeR _))).
  Proof.
    setoid_rewrite <- own_op.
    iApply own_alloc.
    apply auth_both_valid_discrete. split; first done.
    apply valid_to_agree_fmap.
  Qed.

  Lemma own_all_bumpers_persist γ encoded_bumpers :
    own_all_bumpers γ encoded_bumpers ==∗
    own γ (●□ ((to_agree <$> encoded_bumpers) : gmapUR _ (agreeR _))).
  Proof. iApply own_update. apply auth_update_auth_persist. Qed.

  Lemma bumpers_frag_lookup γ (bumpers : gmap loc (positive → option positive))
        (ℓ : loc) (bumper : positive → option positive) :
    bumpers !! ℓ = Some bumper →
    own γ (◯ (to_agree <$> bumpers) : bumpersR) -∗
    own γ (◯ {[ ℓ := to_agree bumper ]}).
  Proof.
    intros look. f_equiv. simpl.
    apply auth_frag_mono.
    rewrite singleton_included_l.
    eexists _.
    rewrite lookup_fmap look.
    naive_solver.
  Qed.

End bumpers.

