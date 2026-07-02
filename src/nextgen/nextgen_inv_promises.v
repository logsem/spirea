From iris.algebra Require Import csum excl.
From PerennialNG.base_logic.lib Require Import fancy_updates.
From iris.proofmode Require Import ltac_tactics.
From iris.bi Require Import fractional.
From self.nextgen Require Import nextgen_promises.

Definition endisR := agreeR (sumO unit unit).
Class endisG Σ :=
  EnDisG { endisG_inG : inG Σ (endisR); }.
#[export] Existing Instance endisG_inG.
Definition endisΣ : gFunctors := #[ GFunctor (endisR) ].
Global Instance subG_endisΣ Σ : subG (endisΣ) Σ → endisG Σ.
Proof. solve_inG. Qed.
Class endisNG Σ Ω :=
  EnDisNG { ng_endisG :: endisG Σ;
            ng_deps :: genInDepsG Σ Ω (endisR) [#] }.
Section endis.
  Context `{os: !endisNG Σ Ω}.

  (* the picked transformation makes enabled into disabled, and leaves disabled the same *)
  Definition endis_trans_rel (t : endisR -> endisR) : Prop :=
    ∀ a, t (to_agree a) ≡ to_agree (inr ()).
  Definition endis_trans : endisR → endisR :=
    λ a, agree_map (λ t, inr ()) a.

  Global Instance endis_trans_cmramorphism : CmraMorphism endis_trans.
  Proof.
    apply agree_map_morphism.
    intros ????. auto.
  Qed.

  Definition endis_en_def γ : iProp Σ := gen_own γ (to_agree (inl ())) ∗ rely_self γ endis_trans_rel.
  Definition endis_en_aux : seal (@endis_en_def). Proof. by eexists. Qed.
  Definition endis_en := endis_en_aux.(unseal).
  Definition endis_en_eq : @endis_en = @endis_en_def := endis_en_aux.(seal_eq).

  Definition endis_dis_def γ : iProp Σ := gen_own γ (to_agree (inr ())) ∗ rely_self γ endis_trans_rel.
  Definition endis_dis_aux : seal (@endis_dis_def). Proof. by eexists. Qed.
  Definition endis_dis := endis_dis_aux.(unseal).
  Definition endis_dis_eq : @endis_dis = @endis_dis_def := endis_dis_aux.(seal_eq).

  Lemma endis_en_alloc :
    ⊢ |==> ∃ γ, endis_en γ.
  Proof.
    rewrite endis_en_eq.
    iMod (own_gen_alloc (DS := [#]) (to_agree (inl ())) [#] [##] with "[]") as (γ) "[Hown Htok]".
    { done. }
    { iIntros (Hcontr). inversion Hcontr. }
    iMod (token_strengthen_promise_0_deps _ _ endis_trans_rel with "Htok") as "Htok";auto.
    { intros;done. }
    { exists endis_trans. split;[apply _|]. intros ??.
      rewrite /endis_trans agree_map_to_agree//. }
    iModIntro. iExists γ. iFrame.
    iApply rely_to_rely_self.
    iApply token_to_rely. iFrame.
  Qed.

  Global Instance endis_dis_persistent γ : Persistent (endis_dis γ).
  Proof. rewrite endis_dis_eq. apply _. Qed.
  Global Instance endis_en_persistent γ : Persistent (endis_en γ).
  Proof. rewrite endis_en_eq. apply _. Qed.

  Lemma endis_en_shot_False γ :
    endis_en γ -∗ endis_dis γ -∗ False.
  Proof.
    iIntros "H1 H2". rewrite endis_en_eq endis_dis_eq.
    iDestruct "H1" as "[H1 _]".
    iDestruct "H2" as "[H2 _]".
    iDestruct (gen_own_valid_2 with "H1 H2") as %Hv%to_agree_op_valid.
    inversion Hv.
  Qed.

  Global Instance endis_dis_timeless γ : Timeless (endis_dis γ).
  Proof. rewrite endis_dis_eq. apply _. Qed.
  Global Instance endis_en_timeless γ : Timeless (endis_en γ).
  Proof. rewrite endis_en_eq. apply _. Qed.

  Lemma nextgen_endis_en γ :
    endis_en γ ⊢ ⚡==> endis_dis γ.
  Proof.
    rewrite endis_en_eq endis_dis_eq.
    iIntros "[Hen Hrely]".
    iModIntro.
    iDestruct "Hen" as (t) "[Hpicked Hen]".
    iDestruct "Hrely" as "[Hrely (%t' & %Ht & Hpicked')]".
    iFrame.
    iDestruct (gen_picked_in_agree with "Hpicked Hpicked'") as %->.
    rewrite Ht. auto.
  Qed.

  Lemma nextgen_endis_dis γ :
    endis_dis γ ⊢ ⚡==> endis_dis γ.
  Proof.
    rewrite endis_dis_eq.
    iIntros "[Hen Hrely]".
    iModIntro.
    iDestruct "Hen" as (t) "[Hpicked Hen]".
    iDestruct "Hrely" as "[Hrely (%t' & %Ht & Hpicked')]".
    iFrame.
    iDestruct (gen_picked_in_agree with "Hpicked Hpicked'") as %->.
    rewrite Ht. auto.
  Qed.

  #[global]
    Instance into_nextgen_endis_en γ : IntoNextgen _ _ := nextgen_endis_en γ.

  #[global]
    Instance into_nextgen_endis_dis γ : IntoNextgen _ _ := nextgen_endis_dis γ.
    
End endis.
