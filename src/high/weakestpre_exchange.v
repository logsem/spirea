From iris.proofmode Require Import proofmode monpred.
From iris_named_props Require Import named_props.
From self Require Export extra ipm_tactics solve_view_le.

From self.high Require Export dprop.
From self.base Require Import generational_resources primitive_laws.
From self.high Require Import
  generational_resources wrappers crash_weakestpre monpred_simpl modalities protocol locations.
From self.high.lib Require Import abstract_state.

From self.lang Require Import syntax tactics lemmas.
From self Require Export lang.

From self.high Require Import weakestpre.

Section weakestpre.
    Context `{AbstractState ST}.
    Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ}.

    Implicit Types (e: expr) (σ: ST) (Q: dProp Σ) (Φ: val → dProp Σ).

    (* TODO: how to write [Atomic] assumption on [e]? *)
    (* TODO: how to write [no_fork] assumption on [e]? *)
    Lemma wp_resource_exchange ℓ prot (σ: ST) e P Q `{!Objective P} Φ s E:
      to_val e = None →
      (∀ v, prot.(p_read) σ v ∗ P -∗ prot.(p_read) σ v ∗ Q) →
      (<fence> Q -∗ WP e @ s; E {{ Φ }}) →
      (⎡ is_at_loc ℓ ⎤ ∗ seen_state ℓ prot σ ∗ P) -∗
      WP e @ s; E {{ Φ }}.
    Proof.
      intros Hval Hxchg Hwp.
      iStartProof (iProp _).
      iIntros (TV) "(#isAtLoc & #seen & P)".
      iApply wp_unfold_at.
      iIntros (? ?) "#val".
      iApply wp_extra_state_interp. { admit. } { assumption. } { admit. }
      iIntros "interp".

      (* use the reasoning to obtain [Q] *)
      iAssert (extra_state_interp ∗ (<fence> Q) _)%I with "[P interp]" as "[interp Q]".
      {
        iNamed "interp". iNamed "seen".
        rename a into t. rename a0 into offset. rename a1 into msg.
        iDestruct (offset_loc_crashed_at_agree with "[] [$]") as %offsetLook.
        { by iNamed "lbBase". }

        (* decode predicates *)
        iPoseProof (own_all_full_preds_pred with "[$] []") as (predFull predFullLook) "#predFullEquiv".
        { iNamed "lbBase". iNamed "locationProtocol". done. }
        iPoseProof (own_all_read_preds_pred with "[$] []") as (predRead predReadLook) "#predReadEquiv".
        { iNamed "lbBase". iNamed "locationProtocol". done. }

        (* [ℓ] is atomic location. *)
        iPoseProof (location_sets_singleton_included with "[$] [$]") as "%isAtLoc".
        (* unify message *)
        iAssert ⌜ ∃ pHist, phys_hists !! ℓ = Some pHist ∧ pHist !! t = Some msg ⌝%I as %[pHist [HphysHistLook HpHistLook]].
        { iPoseProof (auth_map_map_auth_frag with "[$] [$knowPhysMsg]") as "$". }
        
        (* unify abstract state *)
        iAssert ⌜ ∃ aHist encσ, abs_hists !! ℓ = Some aHist ∧ aHist !! t = Some encσ ∧ decode encσ = Some σ ⌝%I
            as %(aHist & encσ & HabsHistLook & HaHistLook & Hdecode).
        { iNamed "lbBase". iPoseProof (full_map_frag_singleton_agreee with "[$] [$knowFragHist]") as "$". }
        
        (* extract [ℓ] from [predsFR] *)
        iDestruct (big_sepM2_lookup_acc _ _ _ ℓ with "predsFullReadHold") as
          "[(%predFull' & %predRead' & %offset' & %predFullLook' & %predReadLook' & %offsetLook' & predFR) predFRRest]".
        { done. } { done. }
        
        (* Try to remove the context as much as possible to make my life easier. *)
        rewrite /extra_state_interp /= /interp.
        repeat (rewrite bi.sep_exist_r; iExists _).
        iFrameNamed.
        simplify_map_eq.
        
        (* extract [t] from [predFR] *)
        iDestruct (big_sepM2_lookup_acc _ _ _ t with "predFR") as
          "[predFRt predFRtRest]".
        { done. } { done. }
        assert (na_views !! ℓ = None) as ->.
        { rewrite -not_elem_of_dom. set_solver. }
        simpl.
        
        set predR := (encoded_predicate_holds predRead _ _ _).
        set predFR := (if (decide _) then _ else _).
        iAssert (predR ∗ (predR -∗ predFR))%I with "[predFRt]" as "[predRt predFRt]".
        { rewrite /predFR.
          destruct (decide (offset ≤ t ∧ pHist !! S t = None)).
          2: { iFrame. by iIntros. }
          admit.
        }
        simplify_map_eq.
        iAssert ((<fence> Q) TV ∗ predR)%I with "[predRt P]" as "[$ predRt]".
        { iPoseProof (predicate_holds_phi_decode_1 (p_read prot) with "[] [$]") as "pRead". { done. }
          { admit. } (* later??? *)
          iPoseProof (Hxchg with "[P $pRead]") as "[pRead Q]".
          { iApply (objective_at with "P"). }
          iDestruct "haveMsg" as %[? ?].
          iSplitL "Q"; last first.
          - rewrite /predR.
            iPoseProof (predicate_holds_phi_decode_2 with "[] pRead") as "predRt". { done. }
            { admit. }
            done.
          - simpl.
            iApply monPred_mono; last done.
            solve_view_le.
        }
        iSpecialize ("predFRt" with "predRt").
        iSpecialize ("predFRtRest" with "predFRt").
        iSpecialize ("predFRRest" with "[predFRtRest]").
        { iExistsN. iFrame. done. }
        done.
      }
      iApply (wp_extra_state_interp_inv with "[Q]"); last done. { admit. } { assumption. } { admit. }
      iPoseProof (Hwp $! _ with "Q") as "wp".
      iPoseProof (wp_fold_at with "wp") as "wp".
      iSpecialize ("wp" with "[] [#$]").
      { iPureIntro. solve_view_le. }
      iApply "wp".
    Admitted.
End weakestpre.
