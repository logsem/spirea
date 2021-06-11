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

Record nvm_high_names := {
  name_abs_history : gname;
  name_know_abs_history : gname;
  name_predicates : gname;
  name_recovery_predicates : gname;
  name_preorders : gname;
  name_shared_locs : gname;
  name_exclusive_locs : gname;
}.

Definition nvm_high_get_names Σ (hG : nvmHighG Σ) : nvm_high_names := {|
  name_abs_history := abs_history_name;
  name_know_abs_history := know_abs_history_name;
  name_predicates := predicates_name;
  name_preorders := preorders_name;
  name_recovery_predicates := preorders_name;
  name_shared_locs := shared_locs_name;
  name_exclusive_locs := exclusive_locs_name;
|}.

Record nvm_names := {
  name_base_names : nvm_base_names; (* Names used by the base logic. *)
  name_high_names : nvm_high_names; (* Names used by the high-level logic. *)
}.

Canonical Structure nvm_namesO := leibnizO nvm_names.

Class nvm_functors Σ := {
  nvm_functors_base : nvmBaseFixedG Σ;
  nvm_functors_high : nvmHighPreG Σ;
}.

Definition nvm_base_insert_names {Σ} (hPG : nvmBaseFixedG Σ)
           (names : nvm_base_names) : nvmBaseG Σ :=
  {|
    nvm_base_inG := hPG;
    store_view_name := names.(name_store_view);
    persist_view_name := names.(name_persist_view);
    crashed_at_view_name := names.(name_crashed_at_view);
  |}.

Definition nvm_high_update_names {Σ} (hG : nvmHighG Σ)
           (names : nvm_high_names) :=
  {|
     nvm_high_inG := hG.(@nvm_high_inG _);
     (* Ghost names *)
     abs_history_name := names.(name_abs_history);
     know_abs_history_name := names.(name_know_abs_history);
     predicates_name := names.(name_predicates);
     recovery_predicates_name := names.(name_recovery_predicates);
     preorders_name := names.(name_preorders);
     shared_locs_name := names.(name_shared_locs);
     exclusive_locs_name := names.(name_exclusive_locs);
  |}.

Instance mk_nmvG {Σ}
         (f : nvm_functors Σ) (b : pbundleG nvm_namesO Σ) : nvmG Σ :=
  let bundle := b.(@pbundleT _ _) in
  let base := bundle.(name_base_names) in
  let high := bundle.(name_high_names) in {|
    nvmG_baseG := {|
      nvm_base_inG := f.(@nvm_functors_base _);
      store_view_name := base.(name_store_view);
      persist_view_name := base.(name_persist_view);
      crashed_at_view_name := base.(name_crashed_at_view)
    |};
    nvmG_highG := {|
      nvm_high_inG := f.(@nvm_functors_high _);
      (* "Global" ghost names *)
      abs_history_name := high.(name_abs_history);
      know_abs_history_name := high.(name_know_abs_history);
      predicates_name := high.(name_predicates);
      recovery_predicates_name := high.(name_recovery_predicates);
      preorders_name := high.(name_preorders);
      shared_locs_name := high.(name_shared_locs);
      exclusive_locs_name := high.(name_exclusive_locs);
    |}
  |}.

(*
Instance mk_nvmG {Σ} (hG : nvmG Σ) (b : pbundleG nvm_namesO Σ) : nvmG Σ | 0 := {|
  (* nvmG_baseG := nvm_base_update_names (@nvmG_baseG _ hG) b.(name_base_names); *)
  (* nvmG_highG := nvm_high_update_names (hG.(@nvmG_highG _)) b.(name_high_names); *)
  nvmG_baseG := nvm_base_update_names (hG.(@nvmG_baseG _))
                                      base;
  nvmG_highG := nvm_high_update_names (hG.(@nvmG_highG _))
                                      high;
|}.
*)

Section test.
  Context `{hG : nvm_functors Σ}.
  Context `{b : pbundleG nvm_namesO Σ}.

  (* Definition foo := crashed_at (∅). *)
  Definition foo := λ (b' : pbundleG nvm_namesO Σ), crashed_at (∅).
  (* Definition foo := let hG' := (@mk_nvmG _ _ _) in crashed_at (∅). *)

  Set Printing All.
  Print foo.
  Unset Printing All.
End test.

(** We defined the post crash modality. *)

Definition know_history_post_crash {Σ}
            (hG : nvmG Σ) ℓ (hist : gmap time positive) : iProp Σ :=
  (∃ t state CV,
    ⌜hist !! t = Some state⌝ ∗
    know_full_encoded_history_loc ℓ ({[ 0 := state ]}) ∗
    crashed_at CV ∗
    ⌜CV !! ℓ = Some (MaxNat t)⌝) ∨
  (∀ CV, crashed_at CV -∗ ⌜CV !! ℓ = None⌝).

Definition post_crash_history_impl {Σ} (hG hG' : nvmG Σ) : iProp Σ :=
  □ ∀ ST `{AbstractState ST} ℓ (t : nat) (s : ST),
    know_frag_history_loc (hG := hG) ℓ {[ t := s ]} -∗
    (∃ CV, crashed_at (hG := @nvmG_baseG _ hG') CV ∗
      ((∃ (s' : ST) t',
           ⌜CV !! ℓ = Some (MaxNat t')⌝ ∗
           ⌜t ≤ t' ↔ s ⊑ s'⌝ ∗
           know_frag_history_loc (hG := hG') ℓ {[ 0 := s' ]})
      ∨
      (⌜CV !! ℓ = None⌝))).

Definition post_crash_preorder_impl {Σ} (hG hG' : nvmG Σ) : iProp Σ :=
  □ ∀ ST `{AbstractState ST} ℓ,
    own_preorder_loc (hG := hG) ℓ abs_state_relation -∗
    (∃ CV,
      crashed_at (hG := @nvmG_baseG _ hG') CV ∗
      (own_preorder_loc (hG := hG') ℓ abs_state_relation ∨
       ⌜CV !! ℓ = None⌝)).

(** This map is used to exchange [know_full_history_loc] valid prior to a crash
into a version valid after the crash. *)
Definition post_crash_map {Σ} (hh : gmap loc (gmap time positive)) (hG hG' : nvmG Σ) : iProp Σ :=
  (* Used to conclude that the locations owned are included in the heap in question. *)
  (∀ ℓ hist, (know_full_encoded_history_loc (hG := hG) ℓ hist) -∗ ⌜hh !! ℓ = Some hist⌝) ∗
  (* The map used to perform the the exchange. *)
  [∗ map] ℓ ↦ hist ∈ hh,
    (know_full_encoded_history_loc (hG := hG) ℓ hist) ∨ (know_history_post_crash hG' ℓ hist).

Definition post_crash_resource {Σ} (h : gmap loc (gmap time positive)) (hG hG' : nvmG Σ) : iProp Σ :=
  "#post_crash_history_impl" ∷ post_crash_history_impl hG hG' ∗
  "#post_crash_preorder_impl" ∷ post_crash_preorder_impl hG hG' ∗
  "post_crash_map" ∷ post_crash_map h hG hG'.

Program Definition post_crash {Σ} (P : nvmG Σ → dProp Σ) `{hG : !nvmG Σ} : dProp Σ :=
  MonPred (λ TV,
    ∀ (hhG' : nvmHighG Σ) hh,
      base_post_crash (λ hG',
        (post_crash_resource hh hG (NvmG _ hG' hhG')) -∗
          P (NvmG _ hG' hhG') (∅, ∅, ∅) ∗ (post_crash_resource hh hG (NvmG _ hG' hhG'))))%I
    _.
(* Next Obligation. solve_proper. Qed. *)

Notation "'<PC>' P" := (post_crash P) (at level 20, right associativity) : bi_scope.

(* We next define the post crash consistent cut modality. *)

(*
Definition persist_view_crashed_at `{hG : !nvmG Σ} :=
  MonPred (λ (TV : thread_view), ∃ (CV : view), ⌜persist_view TV ⊑ CV⌝ ∗ crashed_at CV)%I _.

Definition post_crash_persisted `{hG : !nvmG Σ} P :=
  persist_view_crashed_at -∗ <PC> P.
*)

(** Tiny shortcut for introducing the assumption for a [post_crash]. *)
Ltac iIntrosPostCrash := iIntros (hG' hh).

Section post_crash_prop.
  Context `{hG: !nvmG Σ}.

  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types efs : list thread_state.
  Implicit Types σ : mem_config.

  Global Instance post_crash_objective P : Objective (<PC> P).
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

  Lemma post_crash_mono P Q:
    (∀ hG, P hG -∗ Q hG) → <PC> P -∗ <PC> Q.
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

  Lemma post_crash_sep P Q:
    <PC> P ∗ <PC> Q -∗ <PC> (λ hG, P hG ∗ Q hG).
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
    P → ⊢ <PC> (λ _, ⌜ P ⌝).
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
    ⎡ P ⎤ -∗ <PC> (λ _, ⎡ P ⎤).
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
      (∃ (t : time) (state : ST) CV,
        ⌜abs_hist !! t = Some state⌝ ∗
        ⌜CV !! ℓ = Some (MaxNat t)⌝ ∗
        ⎡crashed_at CV⎤ ∗
        ⎡know_full_history_loc ℓ {[ 0 := state ]}⎤) ∨
      (∀ CV, ⎡crashed_at CV⎤ -∗ ⌜CV !! ℓ = None⌝)).
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
      (* iDestruct (own_valid_2 with "HP H") as %V. *)
      (* rewrite -auth_frag_op in V. *)
      (* apply auth_frag_valid_1 in V. *)
      (* rewrite singleton_op in V. *)
      (* apply singleton_valid in V. *)
      (* apply auth_auth_op_valid in V. *)
      (* done. } *)
    iDestruct ("reIns" with "[$HP]") as "$".
    iFrame "in".
    iFrame "post_crash_history_impl".
    rewrite /know_history_post_crash.
    iDestruct "H" as "[H|H]"; [iLeft|iRight].
    2: { iIntros (?? _). monPred_simpl. iApply "H". }
    iDestruct "H" as (t estate CV) "(%look & hist & crash & %cvLook)".
    apply lookup_fmap_Some in look as [st [eq yo]].
    iExists t, st, CV.
    iFrame "crash %".
    rewrite know_full_equiv.
    rewrite -eq.
    rewrite map_fmap_singleton.
    iFrame.
  Qed.

  Lemma post_crash_preorder `{AbstractState ST} ℓ :
    ⎡ own_preorder_loc ℓ abs_state_relation ⎤ -∗
    post_crash (λ hG',
      (∃ CV, ⎡crashed_at CV⎤ ∗
        (⎡own_preorder_loc ℓ abs_state_relation⎤ ∨
        ⌜CV !! ℓ = None⌝))).
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

  Lemma post_crash_frag_history `{AbstractState ST} ℓ t (s : ST) :
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

End post_crash_prop.

Class IntoCrash {Σ} `{!nvmG Σ} (P: dProp Σ) (Q: nvmG Σ → dProp Σ) :=
  into_crash : P -∗ post_crash (Σ := Σ) (λ hG', Q hG').

Section IntoCrash.

  Context `{hG: !nvmG Σ}.

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
    (λ hG',
      (∃ CV, ⎡crashed_at CV⎤ ∗
        (⎡own_preorder_loc ℓ abs_state_relation⎤ ∨
        ⌜CV !! ℓ = None⌝)))%I.
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

Lemma modus_ponens {Σ} (P Q: dProp Σ)  : P -∗ (P -∗ Q) -∗ Q.
Proof. iIntros "HP Hwand". by iApply "Hwand". Qed.

Ltac crash_env Γ :=
  match Γ with
    | environments.Enil => idtac
    | environments.Esnoc ?Γ' ?id (post_crash _) => crash_env Γ'
    | environments.Esnoc ?Γ' ?id ?A =>
      first [ iEval (rewrite (@into_crash _ _ A) ) in id || iClear id ] ; crash_env Γ'
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

  Lemma post_crash_know_frag_history_loc `{AbstractState ST} ℓ t (s : ST) :
    ⎡ own_preorder_loc ℓ (⊑@{ST}) ∗
      know_frag_history_loc ℓ {[ t := s ]} ∗
      persisted {[ ℓ := MaxNat t]} ⎤ -∗
    post_crash (λ hG',
      ∃ s' t' CV,
        ⌜ s ⊑ s' ⌝ ∗
        ⌜ t ≤ t' ⌝ ∗
        ⌜ CV !! ℓ = Some (MaxNat t') ⌝ ∗
        ⎡ own_preorder_loc (hG := hG') ℓ abs_state_relation ∗
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

  Lemma post_crash_know_global_per_lower_bound `{AbstractState ST}
        (ℓ : loc) (s : ST) :
    know_global_per_lower_bound ℓ s -∗
    post_crash (λ hG,
      know_global_per_lower_bound ℓ s ∗
      know_persist_lower_bound ℓ s ∗
      know_store_lower_bound ℓ s).
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
    iSplit.
    { iApply know_persist_lower_bound_at_zero; done. }
    iApply know_store_lower_bound_at_zero; done.
  Qed.

  Lemma post_crash_mapsto_ex `{AbstractState ST} ℓ ss1 ss2 ϕ ψ :
    (* FIXME: ψ *)
    ℓ ↦ ss1; ss2 | ϕ -∗
    post_crash (λ hG',
      (∃ s, ⌜s ∈ (ss1 ++ ss2)⌝ ∗ ℓ ↦ []; [s] | ψ) ∨
      (∀ t, ⎡¬ (crashed_at {[ ℓ := MaxNat t ]})⎤)
    ).
   Proof.
     iDestruct 1 as (?????)
       "(pts & preds & ? & ? & ? & ? & ? & ? & ?)".
     (* iCrash. *)
   Abort.

End post_crash_derived.

(*
Program Definition post_crash_consistent_cut `{hG : !nvmG Σ} (P : nvmG Σ → dProp Σ) :=
  MonPred (λ TV,
    ⎡ persisted (persist_view TV) ⎤ -∗ post_crash (λ hG', P hG')
  )%I _.
Next Obligation. intros ??????. solve_proper. Qed.
*)
Program Definition post_crash_consistent_cut `{hG : !nvmG Σ}
        (P : nvmG Σ → dProp Σ) : dProp Σ :=
  (∀ TV, monPred_in TV -∗
    <PC> (λ hG', ∃ CV, ⌜persist_view TV ⊑ CV⌝ ∗ ⎡crashed_at CV⎤ -∗ P hG'))%I.
(* Next Obligation. intros ??????. apply post_crash_mono. solve_proper. Qed. *)

(*
Program Definition post_crash_consistent_cut `{hG : !nvmG Σ}
        (P : nvmG Σ → dProp Σ) : dProp Σ :=
  MonPred (λ TV,
    (post_crash (λ hG', ∃ CV, ⌜persist_view TV ⊑ CV⌝ ∗ ⎡crashed_at CV⎤ -∗ P hG')) TV
  )%I _.
Next Obligation. intros ??????. apply post_crash_mono. solve_proper. Qed.
*)

Notation "'<PCCC>' P" :=
  (post_crash_consistent_cut P) (at level 20, right associativity) : bi_scope.

Section post_crash_persisted.
  Context `{hG: !nvmG Σ}.

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
