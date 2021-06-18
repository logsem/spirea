From iris.algebra Require Import auth.
From iris.base_logic Require Import ghost_map.
From iris.proofmode Require Import reduction monpred tactics.

From Perennial.Helpers Require Import ipm NamedProps.
From Perennial.program_logic Require Import recovery_weakestpre.

From self.base Require Import primitive_laws wpr_lifting.
From self.base Require post_crash_modality.
From self.high Require Import dprop resources monpred_simpl.

Set Default Proof Using "Type".

Notation base_post_crash := post_crash_modality.post_crash.

(** We define the post crash modality. *)

Definition know_history_post_crash `{nvmFixedG Σ}
            (hG : nvmDeltaG Σ) ℓ (hist : gmap time positive) : iProp Σ :=
  (∃ CV, crashed_at CV ∗
    ((∃ t s,
      ⌜hist !! t = Some s⌝ ∗
      ⌜CV !! ℓ = Some (MaxNat t)⌝ ∗
      know_full_encoded_history_loc ℓ ({[ 0 := s ]}))
    ∨ ⌜CV !! ℓ = None⌝)).

Definition post_crash_history_impl `{hG : nvmFixedG Σ}
           (hGD hGD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ST (_ : AbstractState ST) ℓ (t : nat) (s : ST),
    know_frag_history_loc (hGD := hGD) ℓ {[ t := s ]} -∗
    (∃ CV, crashed_at (hGD := @nvm_delta_base _ hGD') CV ∗
      ((∃ (s' : ST) t',
           ⌜CV !! ℓ = Some (MaxNat t')⌝ ∗
           ⌜t ≤ t' ↔ s ⊑ s'⌝ ∗
           know_frag_history_loc (hGD := hGD') ℓ {[ 0 := s' ]})
      ∨
      (⌜CV !! ℓ = None⌝))).

Definition post_crash_preorder_impl `{nvmFixedG Σ}
           (hGD hGD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ST (_ : AbstractState ST) ℓ,
    own_preorder_loc (hGD := hGD) ℓ abs_state_relation -∗
    (∃ CV,
      crashed_at (hGD := @nvm_delta_base _ hGD') CV ∗
      (own_preorder_loc (hGD := hGD') ℓ abs_state_relation ∨
       ⌜CV !! ℓ = None⌝)).

Definition post_crash_pred_impl `{nvmFixedG Σ}
           (hGD hGD' : nvmDeltaG Σ) : iProp Σ :=
  □ ∀ ST (_ : AbstractState ST) ℓ (ϕ : ST → val → dProp Σ),
    know_pred (hGD := hGD) ℓ ϕ -∗
    (∃ CV,
      crashed_at (hGD := @nvm_delta_base _ hGD') CV ∗
      ((⌜ℓ ∈ dom (gset _) CV⌝ ∗ (know_pred (hGD := hGD') ℓ ϕ))
      ∨ ⌜CV !! ℓ = None⌝)).

(** This map is used to exchange [know_full_history_loc] valid prior to a crash
into a version valid after the crash. *)
Definition post_crash_map `{nvmFixedG Σ}
           (hh : gmap loc (gmap time positive)) (hGD hGD' : nvmDeltaG Σ) : iProp Σ :=
  (* Used to conclude that the locations owned are included in the heap in question. *)
  (∀ ℓ hist, (know_full_encoded_history_loc (hGD := hGD) ℓ hist) -∗ ⌜hh !! ℓ = Some hist⌝) ∗
  (* The map used to perform the the exchange. *)
  [∗ map] ℓ ↦ hist ∈ hh,
    (know_full_encoded_history_loc (hGD := hGD) ℓ hist) ∨
    (know_history_post_crash hGD' ℓ hist).

Definition post_crash_resource `{nvmFixedG Σ}
           (h : gmap loc (gmap time positive)) (hGD hGD' : nvmDeltaG Σ) : iProp Σ :=
  "#post_crash_history_impl" ∷ post_crash_history_impl hGD hGD' ∗
  "#post_crash_preorder_impl" ∷ post_crash_preorder_impl hGD hGD' ∗
  "#post_crash_pred_impl" ∷ post_crash_pred_impl hGD hGD' ∗
  "post_crash_map" ∷ post_crash_map h hGD hGD'.

Program Definition post_crash `{nvmFixedG Σ, hGD : nvmDeltaG Σ}
        (P : nvmDeltaG Σ → dProp Σ) : dProp Σ :=
  MonPred (λ TV,
    ∀ (hhGD' : nvmHighDeltaG) hh,
      base_post_crash (λ hGD',
        (post_crash_resource hh hGD (NvmDeltaG _ hGD' hhGD')) -∗
        P (NvmDeltaG _ hGD' hhGD') (∅, ∅, ∅) ∗
        (post_crash_resource hh hGD (NvmDeltaG _ hGD' hhGD'))))%I
    _.
(* Next Obligation. solve_proper. Qed. *)

Notation "'<PC>' g , P" := (post_crash (λ g, P))
  (at level 200, g binder, right associativity) : bi_scope.

(** Tiny shortcut for introducing the assumption for a [post_crash]. *)
Ltac iIntrosPostCrash := iIntros (hG' hh).

Section post_crash_prop.
  Context `{nvmFixedG Σ, hGD: nvmDeltaG Σ}.

  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types efs : list thread_state.
  Implicit Types σ : mem_config.

  Global Instance post_crash_objective P : Objective (post_crash P).
  Proof. done. Qed.

  (* Lemma post_crash_intro Q: *)
  (*   (⊢ Q) → *)
  (*   (⊢ post_crash (λ _, Q)). *)
  (* Proof. *)
  (*   iStartProof (iProp _). iIntros (TV'). *)
  (*   iIntros (Hmono). *)
  (*   iIntrosPostCrash. *)
  (*   iFrame "∗". *)
  (*   iApply Hmono. *)
  (* Qed. *)

  (** ** Structural rules *)

  Lemma post_crash_mono P Q :
    (∀ hG, P hG -∗ Q hG) → post_crash P -∗ post_crash Q.
  Proof.
    iStartProof (iProp _). iIntros (Hmono TV') "HP".
    iIntrosPostCrash.
    iDestruct ("HP" $! hG') as "P".
    iApply (post_crash_modality.post_crash_mono with "P").
    iIntros (hG2).
    (* rewrite /post_crash_impl. *)
    iIntros "P M".
    iDestruct ("P" with "M") as "[P $]".
    iDestruct (Hmono with "P") as "H".
    done.
  Qed.

  Lemma post_crash_sep P Q :
    post_crash P ∗ post_crash Q -∗ <PC> hG, P hG ∗ Q hG.
  Proof.
    iStartProof (iProp _). iIntros (TV).
    iIntros "(HP & HQ)".
    iIntrosPostCrash.
    iDestruct ("HP" $! hG' hh) as "HP".
    iDestruct ("HQ" $! hG' hh) as "HQ".
    post_crash_modality.iCrash.
    iIntros "M".
    iDestruct ("HP" with "M") as "[$ M]".
    iDestruct ("HQ" with "M") as "[$ $]".
  Qed.

  Lemma post_crash_pure (P : Prop) : P → ⊢ <PC> _, ⌜P⌝.
  Proof.
    iIntros (HP).
    iStartProof (iProp _). iIntros (TV').
    iIntrosPostCrash.
    iApply post_crash_modality.post_crash_for_all.
    iIntros (hG0) "$".
    iApply monPred_at_pure.
    iFrame "%".
  Qed.

  Lemma post_crash_embed_nodep P :
    ⎡ P ⎤ -∗ <PC> _, ⎡ P ⎤.
  Proof.
    iStartProof (iProp _). iIntros (TV') "P".
    iIntrosPostCrash.
    iApply post_crash_modality.post_crash_for_all.
    iIntros (hG0) "$".
    iApply monPred_at_embed.
    iFrame.
  Qed.

  Lemma post_crash_named P name :
    named name (post_crash (λ hG, P hG)) -∗
    post_crash (λ hG, named name (P hG)).
  Proof. rewrite //=. Qed.

End post_crash_prop.

Section post_crash_interact.
  Context `{nvmFixedG Σ, hGD: nvmDeltaG Σ}.

  Context `{AbstractState ST}.

  (** ** The rules for the "special" assertions

  How the post crash modality interacts with the assertions in the logic. *)

  (* The predicate [P] holds for [ℓ] or [ℓ] has been lost. *)
  Definition or_lost {hGD' : nvmDeltaG Σ} ℓ (P : dProp Σ) : dProp Σ :=
    ∃ CV, ⎡crashed_at CV⎤ ∗ (P ∨ (⌜CV !! ℓ = None⌝)).

  Definition or_lost_with_t {hGD' : nvmDeltaG Σ} ℓ (P : time → dProp Σ) : dProp Σ :=
    ∃ CV, ⎡crashed_at CV⎤ ∗ ((∃ t, ⌜CV !! ℓ = Some (MaxNat t)⌝ ∗ P t)
                          ∨ (⌜CV !! ℓ = None⌝)).

  Lemma post_crash_know_full_history_loc ℓ (abs_hist : abs_history ST) :
    ⎡know_full_history_loc ℓ abs_hist⎤ -∗
    <PC> _, or_lost_with_t ℓ (λ t, ∃ (state : ST),
        ⌜abs_hist !! t = Some state⌝ ∗
        ⎡know_full_history_loc ℓ {[ 0 := state ]}⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    iFrame "post_crash_preorder_impl".
    iDestruct "post_crash_map" as "[in M]".
    rewrite know_full_equiv.
    iAssert (⌜hh !! _ = Some _⌝)%I as %HI.
    { iApply ("in" with "HP"). }
    iDestruct (big_sepM_lookup_acc with "M") as "[[H|H] reIns]"; first done.
    { (* We derive a contradiction. *)
      iExFalso.
      rewrite /know_full_encoded_history_loc.
      iDestruct (ghost_map_elem_valid_2 with "H HP") as %[v _].
      iPureIntro.
      by apply v. }
    iDestruct ("reIns" with "[$HP]") as "$".
    iFrame "in".
    iFrameNamed.
    rewrite /know_history_post_crash /or_lost_with_t.
    iDestruct "H" as (CV) "[crashedAt [H|H]]"; iExists (CV);
      iFrame "crashedAt"; [iLeft|iRight; done].
    iDestruct "H" as (t estate) "(%look & %cvLook & hist)".
    apply lookup_fmap_Some in look as [st [eq ?]].
    iExists t. iFrame (cvLook). iExists st.
    rewrite know_full_equiv. rewrite -eq. rewrite map_fmap_singleton.
    iFrame "%∗".
  Qed.

  Lemma post_crash_preorder ℓ :
    ⎡ own_preorder_loc ℓ abs_state_relation ⎤ -∗
    post_crash (λ hG', or_lost ℓ ⎡own_preorder_loc ℓ abs_state_relation⎤)%I.
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_preorder_impl" with "HP") as (CV) "[crash HI]".
    iExists CV. iFrame.
  Qed.

  Lemma post_crash_frag_history ℓ t (s : ST) :
    ⎡ know_frag_history_loc ℓ {[ t := s ]} ⎤ -∗
    post_crash (λ hG',
      (∃ CV, ⎡crashed_at CV⎤ ∗
        ((∃ (s' : ST) t',
            ⌜CV !! ℓ = Some (MaxNat t')⌝ ∗
            ⌜t ≤ t' ↔ s ⊑ s'⌝ ∗
            ⎡know_frag_history_loc ℓ {[ 0 := s' ]}⎤)
        ∨ (⌜CV !! ℓ = None⌝)))).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_history_impl" with "HP") as (CV) "[crash HI]".
    iExists CV. iFrame.
    (* monPred_simpl. *)
    (* setoid_rewrite monPred_at_sep. *)
    (* setoid_rewrite monPred_at_wand. *)
    (* setoid_rewrite monPred_at_pure. *)
    (* setoid_rewrite monPred_at_embed. *)
    (* iDestruct "HI" as "[HI|HI]". *)
    (* - iLeft. iFrame. *)
    (* - iRight. iIntros (???). iApply "HI". *)
  Qed.

  Lemma post_crash_know_pred ℓ (ϕ : ST → val → dProp Σ) :
    ⎡know_pred ℓ ϕ⎤ -∗ <PC> _, or_lost_with_t ℓ (λ _, ⎡know_pred ℓ ϕ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    rewrite /post_crash_resource. iFrameNamed.
    iDestruct ("post_crash_pred_impl" with "HP") as (CV) "[crash disj]".
    iExists CV. iFrame.
    setoid_rewrite elem_of_dom.
    iDestruct "disj" as "[((%t & %elem) & HP) | %look]"; last naive_solver.
    destruct t as [t].
    naive_solver.
  Qed.

End post_crash_interact.

Class IntoCrash {Σ} `{nvmFixedG Σ, nvmDeltaG Σ}
      (P : dProp Σ) (Q : nvmDeltaG Σ → dProp Σ) :=
  into_crash : P -∗ post_crash (Σ := Σ) (λ hGD', Q hGD').

Section IntoCrash.
  Context `{nvmFixedG Σ, nvmDeltaG Σ}.

  Global Instance pure_into_crash (P: Prop) :
    IntoCrash (⌜ P ⌝%I) (λ _, ⌜ P ⌝%I).
  Proof. rewrite /IntoCrash. iIntros "%". by iApply post_crash_pure. Qed.

  Global Instance lifted_embed_into_crash (P : iProp Σ) Q :
    base.post_crash_modality.IntoCrash P Q →
    IntoCrash (⎡ P ⎤%I) (λ _, ⎡ Q _ ⎤%I).
  Proof.
    rewrite /IntoCrash.
    iStartProof (iProp _).
    iIntros (??) "?".
    iIntrosPostCrash.
    post_crash_modality.iCrash.
    iIntros "$". done.
  Qed.

  (* Global Instance embed_into_crash P : *)
  (*   IntoCrash (⎡ P ⎤%I) (λ _, ⎡ P ⎤%I). *)
  (* Proof. rewrite /IntoCrash. iIntros "P". by iApply post_crash_embed_nodep. Qed. *)

  Global Instance into_crash_preorder `{AbstractState ST} ℓ :
    IntoCrash
    (⎡ own_preorder_loc ℓ abs_state_relation ⎤)
    (λ hG', or_lost ℓ (⎡own_preorder_loc ℓ abs_state_relation⎤))%I.
  Proof. rewrite /IntoCrash. iIntros "P". by iApply post_crash_preorder. Qed.

  Global Instance frag_history_into_crash `{AbstractState ST} ℓ t s :
    IntoCrash
      (⎡ know_frag_history_loc ℓ {[ t := s ]} ⎤)
      (λ hG',
        (∃ CV, ⎡crashed_at CV⎤ ∗
          ((∃ (s' : ST) t',
              ⌜CV !! ℓ = Some (MaxNat t')⌝ ∗
              ⌜t ≤ t' ↔ s ⊑ s'⌝ ∗
              ⎡know_frag_history_loc ℓ {[ 0 := s' ]}⎤)
          ∨ (⌜CV !! ℓ = None⌝))))%I.
  Proof. rewrite /IntoCrash. iIntros "P". by iApply post_crash_frag_history. Qed.

End IntoCrash.

Lemma modus_ponens {Σ} (P Q : dProp Σ)  : P -∗ (P -∗ Q) -∗ Q.
Proof. iIntros "HP Hwand". by iApply "Hwand". Qed.

Ltac crash_env Γ :=
  match Γ with
    | environments.Enil => idtac
    | environments.Esnoc ?Γ' ?id (post_crash _) => crash_env Γ'
    | environments.Esnoc ?Γ' ?id ?A =>
      first [ iEval (rewrite (@into_crash _ _ _ A) ) in id || iClear id ] ; crash_env Γ'
  end.

Ltac crash_ctx :=
  match goal with
  | [ |- environments.envs_entails ?Γ _] =>
    let spatial := pm_eval (environments.env_spatial Γ) in
    let intuit := pm_eval (environments.env_intuitionistic Γ) in
    crash_env spatial; crash_env intuit
  end.

Ltac iCrash :=
  crash_ctx;
  iApply (modus_ponens with "[-]"); [ iNamedAccu | ];
  rewrite ?post_crash_named ?post_crash_sep; iApply post_crash_mono;
  intros; simpl;
  let H := iFresh in iIntros H; iNamed H.

Section post_crash_derived.
  Context `{nvmFixedG Σ, nvmDeltaG Σ}.

  Context `{AbstractState ST}.

  Lemma post_crash_know_frag_history_loc ℓ t (s : ST) :
    ⎡ own_preorder_loc ℓ (⊑@{ST}) ∗
      know_frag_history_loc ℓ {[ t := s ]} ∗
      persisted {[ ℓ := MaxNat t]} ⎤ -∗
    post_crash (λ hGD',
      ∃ s' t' CV,
        ⌜ s ⊑ s' ⌝ ∗
        ⌜ t ≤ t' ⌝ ∗
        ⌜ CV !! ℓ = Some (MaxNat t') ⌝ ∗
        ⎡ own_preorder_loc (hGD := hGD') ℓ abs_state_relation ∗
          know_frag_history_loc ℓ {[ 0 := s' ]} ∗
          crashed_at CV ∗
          persisted {[ ℓ := MaxNat 0 ]} ⎤
    ).
  Proof.
    iStartProof (dProp _).
    iIntros "(order & hist & pers)".
    iCrash.
    iDestruct "pers" as "[pers (%CV & %t' & [%cvLook %le] & crash)]".
    iDestruct "order" as (CV') "[crash' [order | %cvLook']]";
      iDestruct (crashed_at_agree with "crash crash'") as %<-; last congruence.
    iClear "crash'".
    iDestruct "hist" as (CV') "[crash' [hist | %cvLook']]";
      iDestruct (crashed_at_agree with "crash crash'") as %<-; last congruence.
    iClear "crash'".
    iDestruct "hist" as (s' ? cvLook' impl) "fragHist".
    simplify_eq.
    iExists s', t', CV.
    iFrame "∗%".
    naive_solver.
  Qed.

  Lemma post_crash_know_global_per_lower_bound (ℓ : loc) (s : ST) :
    know_global_per_lower_bound ℓ s -∗
    post_crash (λ hG,
      know_global_per_lower_bound ℓ s ∗
      know_persist_lower_bound ℓ s). (* ∗ know_store_lower_bound ℓ s). *)
  Proof.
    iStartProof (dProp _).
    iIntros "H".
    iDestruct "H" as (t s') "(%incl & #order & pers & hist)".
    iDestruct (post_crash_know_frag_history_loc with "[$pers $hist $order]") as "HI".
    iApply (post_crash_mono with "HI").
    iIntros (hG').
    iDestruct 1 as
        (s'' t' CV) "(%incl' & %le & %cvLook & #ord & #hist & #crash & #pers)".
    rewrite /know_global_per_lower_bound.
    assert (s ⊑ s'') by (etrans; done).
    (* We show the global persist lower bound. *)
    iSplit.
    { iExists 0, s''. iFrame "#%". }
    (* We show the local persist lower bound. *)
    iApply know_persist_lower_bound_at_zero; done.
    (* iSplit. *)
    (* { iApply know_persist_lower_bound_at_zero; done. } *)
    (* iApply know_store_lower_bound_at_zero; done. *)
  Qed.

  Lemma post_crash_mapsto_ex `{AbstractState ST} ℓ ss1 ss2 ϕ ψ :
    (* FIXME: ψ *)
    ℓ ↦ ss1; ss2 | ϕ -∗
    post_crash (λ hG',
      (∃ s, ⌜s ∈ (ss1 ++ ss2)⌝ ∗ ℓ ↦ []; [s] | ψ) ∨
      (∀ t, ⎡¬ (crashed_at {[ ℓ := MaxNat t ]})⎤)
    ).
   Proof.
     rewrite /mapsto_ex.
     iNamed 1.
     (* iCrash. *)
   Abort.

End post_crash_derived.

(*
Program Definition post_crash_consistent_cut `{hG : !nvmFixedG Σ, nvmDeltaG Σ} (P : nvmFixedG Σ, nvmDeltaG Σ → dProp Σ) :=
  MonPred (λ TV,
    ⎡ persisted (persist_view TV) ⎤ -∗ post_crash (λ hG', P hG')
  )%I _.
Next Obligation. intros ??????. solve_proper. Qed.
*)
(* Definition post_crash_consistent_cut `{nvmFixedG Σ, nvmDeltaG Σ} *)
(*         (P : nvmDeltaG Σ → dProp Σ) : dProp Σ := *)
(*     <PC> (λ (hGD' : nvmDeltaG Σ), P hGD'). *)
Definition post_crash_consistent_cut `{nvmFixedG Σ, nvmDeltaG Σ}
        (P : nvmDeltaG Σ → dProp Σ) : dProp Σ :=
  (∀ TV, monPred_in TV -∗
    <PC> (hGD' : nvmDeltaG Σ),
      ∃ (CV : view),
        ⌜persist_view TV ⊑ CV⌝ -∗
        ⎡crashed_at CV⎤ -∗
        P hGD')%I.
(* Next Obligation. intros ??????. apply post_crash_mono. solve_proper. Qed. *)

(*
Program Definition post_crash_consistent_cut `{hG : !nvmFixedG Σ, nvmDeltaG Σ}
        (P : nvmFixedG Σ, nvmDeltaG Σ → dProp Σ) : dProp Σ :=
  MonPred (λ TV,
    (post_crash (λ hG', ∃ CV, ⌜persist_view TV ⊑ CV⌝ ∗ ⎡crashed_at CV⎤ -∗ P hG')) TV
  )%I _.
Next Obligation. intros ??????. apply post_crash_mono. solve_proper. Qed.
*)

Notation "'<PCCC>' P" :=
  (post_crash_consistent_cut P) (at level 20, right associativity) : bi_scope.

Section post_crash_persisted.
  Context `{hG: !nvmFixedG Σ, nvmDeltaG Σ}.

  Lemma post_crash_persisted_know_persist_lower_bound `{AbstractState ST}
        (ℓ : loc) (s : ST) :
    know_persist_lower_bound ℓ s -∗
    post_crash (λ hG,
      know_global_per_lower_bound ℓ s ∗
      know_persist_lower_bound ℓ s ∗
      know_store_lower_bound ℓ s).
  Proof.
    iStartProof (iProp _).
    iIntros (TV) "H".
    iDestruct "H" as (t s' incl le) "(pers & hist)".
    iDestruct (post_crash_know_frag_history_loc with "[$pers $hist]") as "HI".
  Abort.
  (*   iApply (post_crash_mono with "HI"). *)
  (*   iIntros (hG'). *)
  (*   iDestruct 1 as *)
  (*       (s'' t' CV) "(%incl' & %le & %cvLook & #ord & #hist & #crash & #pers)". *)
  (*   rewrite /know_global_per_lower_bound. *)
  (*   assert (s ⊑ s'') by (etrans; done). *)
  (*   (* We show the global persist lower bound. *) *)
  (*   iSplit. *)
  (*   { iExists 0, s''. iFrame "#%". } *)
  (*   (* We show the local persist lower bound. *) *)
  (*   iSplit. *)
  (*   { iApply know_persist_lower_bound_at_zero; done. } *)
  (*   iApply know_store_lower_bound_at_zero; done. *)
  (*   iStartProof (iProp _). *)
  (* Qed. *)


End post_crash_persisted.
