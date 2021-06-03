From iris.algebra Require Import auth.
From iris.base_logic Require Import ghost_map.
From iris.proofmode Require Import reduction monpred tactics.

From Perennial.Helpers Require Import ipm NamedProps.

From self.base Require Import primitive_laws.
From self.base Require post_crash_modality.
From self.high Require Import dprop resources crash_weakestpre weakestpre.

Set Default Proof Using "Type".

Notation base_post_crash := post_crash_modality.post_crash.

Definition know_history_post_crash {Σ}
            (hG : nvmG Σ) ℓ (hist : gmap time positive) : iProp Σ :=
  (∃ t state,
    ⌜hist !! t = Some state⌝ ∗
    know_full_encoded_history_loc ℓ ({[ 0 := state ]}) ∗
    recovered {[ ℓ := MaxNat t ]}) ∨
  (∀ t, ¬ (recovered {[ ℓ := MaxNat t ]})).

Definition post_crash_impl {Σ} (hG hG' : nvmG Σ) : iProp Σ :=
  □ ∀ ST `{AbstractState ST} ℓ (t : nat) (s : ST),
    own_preorder_loc (hG := hG) ℓ abs_state_relation -∗
    know_frag_history_loc (hG := hG) ℓ {[ t := s ]} -∗
    persisted (hG := @nvmG_baseG _ hG) {[ ℓ := MaxNat t]} -∗
    ∃ (s' : ST), ⌜s ⊑ s'⌝ ∗
      own_preorder_loc (hG := hG') ℓ abs_state_relation ∗
      know_frag_history_loc (hG := hG') ℓ {[ 0 := s' ]}.

(** This map is used to exchange [know_full_history_loc] valid prior to a crash
into a version valid after the crash. *)
Definition post_crash_map {Σ} (hh : gmap loc (gmap time positive)) (hG hG' : nvmG Σ) : iProp Σ :=
  (* Used to conclude that the locations owned are included in the heap in question. *)
  (∀ ℓ hist, (know_full_encoded_history_loc (hG := hG) ℓ hist) -∗ ⌜hh !! ℓ = Some hist⌝) ∗
  (* The map used to perform the the exchange. *)
  [∗ map] ℓ ↦ hist ∈ hh,
    (know_full_encoded_history_loc (hG := hG) ℓ hist) ∨ (know_history_post_crash hG' ℓ hist).

Definition post_crash_resource {Σ} (h : gmap loc (gmap time positive)) (hG hG' : nvmG Σ) : iProp Σ :=
  "#post_crash_impl" ∷ post_crash_impl hG hG' ∗
  "post_crash_map" ∷ post_crash_map h hG hG'.

Program Definition post_crash {Σ} (P : nvmG Σ → dProp Σ) `{hG : !nvmG Σ} : dProp Σ :=
  MonPred (λ TV,
    ∀ (hhG' : nvmHighG Σ) hh,
      base_post_crash (λ hG',
        (post_crash_resource hh hG (NvmG _ hG' hhG')) -∗
          P (NvmG _ hG' hhG') (∅, ∅, ∅) ∗ (post_crash_resource hh hG (NvmG _ hG' hhG'))))%I
    _.
(* Next Obligation. solve_proper. Qed. *)

Section post_crash_prop.
  Context `{hG: !nvmG Σ}.

  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types efs : list thread_state.
  Implicit Types σ : mem_config.

  Global Instance post_crash_objective P : Objective (post_crash P).
  Proof. done. Qed.

  (** Tiny shortcut for introducing the assumption for a [post_crash]. *)
  Ltac iIntrosPostCrash := iIntros (hG' hh).

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

  Lemma post_crash_mono P Q:
    (∀ hG, P hG -∗ Q hG) →
    post_crash P -∗ post_crash Q.
  Proof.
    iStartProof (iProp _). iIntros (Hmono TV') "HP".
    iIntrosPostCrash.
    iDestruct ("HP" $! hG') as "P".
    iApply (post_crash_modality.post_crash_mono with "P").
    iIntros (hG2).
    rewrite /post_crash_impl.
    iIntros "P M".
    iDestruct ("P" with "M") as "[P $]".
    iDestruct (Hmono with "P") as "H".
    done.
  Qed.

  Lemma post_crash_sep P Q:
    post_crash P ∗ post_crash Q -∗ post_crash (λ hG, P hG ∗ Q hG).
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

  Lemma post_crash_pure (P: Prop) :
    P → ⊢ post_crash (λ _, ⌜ P ⌝).
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
    ⎡ P ⎤ -∗ post_crash (λ _, ⎡ P ⎤).
  Proof.
    iStartProof (iProp _). iIntros (TV') "P".
    iIntrosPostCrash.
    iApply post_crash_modality.post_crash_for_all.
    iIntros (hG0) "$".
    iApply monPred_at_embed.
    iFrame.
  Qed.

  Lemma post_crash_named P name:
    named name (post_crash (λ hG, P hG)) -∗
    post_crash (λ hG, named name (P hG)).
  Proof. rewrite //=. Qed.

  (** ** The rules for the "special" assertions *)

  Lemma post_crash_know_full_history_loc `{Countable ST} ℓ (abs_hist : abs_history ST) :
    ⎡know_full_history_loc ℓ abs_hist⎤ -∗
    post_crash (λ hG',
      (∃ (t : time) (state : ST),
        ⌜abs_hist !! t = Some state⌝ ∗
        ⎡recovered {[ ℓ := MaxNat t ]}⎤ ∗
        ⎡know_full_history_loc ℓ {[ 0 := state ]}⎤) ∨
      (∀ t, ⎡¬ (recovered {[ ℓ := MaxNat t ]})⎤)).
  Proof.
    iStartProof (iProp _). iIntros (TV') "HP".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP".
    post_crash_modality.iCrash.
    iNamed 1.
    iFrame "post_crash_impl".
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
      (* iDestruct (own_valid_2 with "HP H") as %V. *)
      (* rewrite -auth_frag_op in V. *)
      (* apply auth_frag_valid_1 in V. *)
      (* rewrite singleton_op in V. *)
      (* apply singleton_valid in V. *)
      (* apply auth_auth_op_valid in V. *)
      (* done. } *)
    iDestruct ("reIns" with "[$HP]") as "$".
    iFrame "in".
    iDestruct "H" as "[H|H]"; [iLeft|iRight; iFrame].
    iDestruct "H" as (t estate) "(%look & hist & rec)".
    apply lookup_fmap_Some in look as [st [eq yo]].
    iExists t, st.
    iFrame "rec".
    iSplit; first done.
    rewrite know_full_equiv.
    rewrite -eq.
    rewrite map_fmap_singleton.
    iFrame.
  Qed.

  Lemma post_crash_know_frag_history_loc `{AbstractState ST} ℓ t (s : ST) :
    ⎡ own_preorder_loc ℓ (⊑@{ST}) ∗
      know_frag_history_loc ℓ {[ t := s ]} ∗
      persisted {[ ℓ := MaxNat t]} ⎤ -∗
    post_crash (λ hG',
      ∃ s',
        ⌜ s ⊑ s' ⌝ ∗
        ⎡ own_preorder_loc (hG := hG') ℓ abs_state_relation ∗
          know_frag_history_loc ℓ {[ 0 := s' ]} ∗ persisted {[ ℓ := MaxNat 0 ]} ⎤
    ).
  Proof.
    iStartProof (iProp _). iIntros (TV').
    rewrite (bi.persistent_sep_dup (persisted _)).
    iIntros "(order & hist & pers & pers')".
    iIntrosPostCrash.
    iDestruct (post_crash_modality.post_crash_nodep with "pers") as "pers".
    iDestruct (post_crash_modality.post_crash_nodep with "order") as "order".
    iDestruct (post_crash_modality.post_crash_nodep with "hist") as "hist".
    post_crash_modality.iCrash.
    iDestruct "pers'" as "[pers' _]".
    iNamed 1.
    rewrite /sqsubseteq /abstract_state_sqsubseteq.
    iDestruct ("post_crash_impl" with "order hist pers") as (s') "(%rel & ho & hist)".
    iFrame "∗#".
    iExists s'.
    iFrame "∗%".
  Qed.

  Lemma post_crash_know_global_per_lower_bound `{AbstractState ST}
        (ℓ : loc) (s : ST) :
    know_global_per_lower_bound ℓ s -∗
    post_crash (λ hG,
      know_global_per_lower_bound ℓ s ∗
      know_persist_lower_bound ℓ s ∗
      know_store_lower_bound ℓ s).
  Proof.
    iStartProof (dProp _).
    (* iIntros (TV') "H". *)
    iIntros "H".
    iDestruct "H" as (t s') "(%incl & #order & pers & hist)".
    (* iIntrosPostCrash. *)
    iDestruct (post_crash_know_frag_history_loc with "[$pers $hist $order]") as "HI".
    (* iApply post_crash_mono. *)
    iApply (post_crash_mono with "HI").
    (* iDestruct (post_crash_modality.post_crash_nodep with "HP") as "HP". *)
    (* iDestruct (post_crash_modality.post_crash_nodep with "hist") as "hist". *)
    (* post_crash_modality.iCrash. *)
    iIntros (hG'). iDestruct 1 as (s'') "(%incl' & #order & #hist & #pers)".
    rewrite /know_global_per_lower_bound.
    iSplit.
    { iExists 0, s''. iFrame "#". admit. }
  Abort.


End post_crash_prop.

Class IntoCrash {Σ} `{!nvmG Σ} (P: dProp Σ) (Q: nvmG Σ → dProp Σ) :=
  into_crash : P -∗ post_crash (Σ := Σ) (λ hG', Q hG').

Section IntoCrash.

  Context `{hG: !nvmG Σ}.

  Global Instance pure_into_crash (P: Prop) :
    IntoCrash (⌜ P ⌝%I) (λ _, ⌜ P ⌝%I).
  Proof. rewrite /IntoCrash. iIntros "%". by iApply post_crash_pure. Qed.

  Global Instance embed_into_crash P :
    IntoCrash (⎡ P ⎤%I) (λ _, ⎡ P ⎤%I).
  Proof.
    rewrite /IntoCrash.
    iIntros "P".
    by iApply post_crash_embed_nodep.
  Qed.

End IntoCrash.

Lemma modus_ponens {Σ} (P Q: dProp Σ)  : P -∗ (P -∗ Q) -∗ Q.
Proof. iIntros "HP Hwand". by iApply "Hwand". Qed.

Ltac crash_env Γ :=
  match Γ with
    | environments.Enil => idtac
    | environments.Esnoc ?Γ' ?id (post_crash _) => crash_env Γ'
    | environments.Esnoc ?Γ' ?id ?A => first [ iEval (rewrite (@into_crash _ _ A) ) in id || iClear id ] ; crash_env Γ'
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
  Context `{hG: !nvmG Σ}.

  Context `{Hi1: !IntoCrash P P'}.
  Context `{Hi2: !IntoCrash Q Q'}.

  Lemma post_crash_mapsto_ex `{AbstractState ST} ℓ ss1 ss2 ϕ :
    (* FIXME: ψ *)
    ℓ ↦ ss1; ss2 | ϕ -∗
    post_crash (λ hG',
      (∃ s, ⌜s ∈ (ss1 ++ ss2)⌝ ∗ ℓ ↦ []; [s] | ψ) ∨
      (∀ t, ⎡¬ (recovered {[ ℓ := MaxNat t ]})⎤)
    ).
   Proof.
     iDestruct 1 as (?????)
       "(pts & preds & ? & ? & ? & ? & ? & ? & ?)".
     iCrash.
   Abort.

End post_crash_derived.
