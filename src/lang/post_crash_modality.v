(* In this file we define the post crash modality for the base logic. *)
From iris.proofmode Require Import reduction monpred tactics.

From Perennial.program_logic Require Export crash_lang.

From self.lang Require Import lang primitive_laws.

Set Default Proof Using "Type".

Definition mapsto_post_crash {Σ} (hG : nvmG Σ) ℓ (hist : history) : iProp Σ :=
  (∃ t msg, ⌜hist !! t = Some msg⌝ ∗
            ℓ ↦h ({[ 0 := discard_store_view msg]}) ∗
            recovered {[ ℓ := MaxNat t ]}) ∨
  (∀ t, ¬ (recovered {[ ℓ := MaxNat t ]})).

Definition post_crash_map {Σ} (σ__old : store) (hG hG' : nvmG Σ) : iProp Σ :=
  [∗ map] ℓ ↦ hist ∈ σ__old, (let hG := hG in ℓ ↦h hist) ∨ (mapsto_post_crash hG' ℓ hist).

(* Note: The [let]s above are to manipulate the type class instance search. *)

                            (* ([∗ map] msg ∈ (discard_store_views $ cut_history t hist), recovered msg.(msg_persist_view)) *)
(** If [σ] is the state before a crah and [σ'] the state after a crash, and [hG]
and [hG'] the corresponding ghost state, then following property is true.*)
(* FIXME: Is this [ghost_crash_rel] used at all? *)
Definition ghost_crash_rel {Σ}
           (σ : mem_config) (hG : nvmG Σ) (σ' : mem_config) (hG' : nvmG Σ) : iProp Σ :=
  (* ⌜hG.(@persist_view_name _) = hG'.(@persist_view_name _)⌝ ∗ *)
  ⌜hG.(@view_inG _) = hG'.(@view_inG _)⌝.

(* Recall that [crash_step] is the state interpretation for our language. *)
(* Definition post_crash {Σ} (P : nvmG Σ → iProp Σ) `{hG : !nvmG Σ} : iProp Σ := *)
(*   (∀ σ σ' (hG' : nvmG Σ), *)
(*       ⌜crash_step σ σ'⌝ -∗ nvm_heap_ctx (hG := hG) σ -∗ nvm_heap_ctx (hG := hG') σ' -∗ *)
(*       (nvm_heap_ctx (hG := hG) σ ∗ nvm_heap_ctx (hG := hG') σ' ∗ P hG')). *)

Definition persisted_impl {Σ} hG hG' : iProp Σ :=
  □ ∀ V, persisted (hG := hG) V -∗ persisted (hG := hG') V ∗
                                   ∃ RV, ⌜V ⊑ RV⌝ ∗ recovered (hG := hG') RV.

Definition post_crash {Σ} (P: nvmG Σ → iProp Σ) `{hG: !nvmG Σ}  : iProp Σ :=
  (∀ σ σ' hG',
    ghost_crash_rel σ hG σ' hG' -∗
    post_crash_map σ.1 hG hG' -∗
    persisted_impl hG hG' -∗
    gen_heap_interp (hG := @nvmG_gen_heapG _ hG) σ.1 -∗
    nvm_heap_ctx (hG := hG') σ' -∗ (* Note: This is not used yet. Remove it if it turns out not to be needed. *)
    ( post_crash_map σ.1 hG hG' ∗
      gen_heap_interp (hG := @nvmG_gen_heapG _ hG) σ.1 ∗
      nvm_heap_ctx (hG := hG') σ' ∗
      P hG')).

Class IntoCrash {Σ} `{!nvmG Σ} (P: iProp Σ) (Q: nvmG Σ → iProp Σ) :=
  into_crash : P -∗ post_crash (Σ := Σ) (λ hG', Q hG').

Section post_crash_prop.
  Context `{hG: !nvmG Σ}.
  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types efs : list thread_state.
  Implicit Types σ : mem_config.
  Implicit Types v : thread_val.

  (** Tiny shortcut for introducing the assumption for a [post_crash]. *)
  Ltac iIntrosPostCrash := iIntros (σ σ' hG') "%rel map #perToRec heap ctxPost".

  Lemma post_crash_intro Q:
    (⊢ Q) →
    (⊢ post_crash (λ _, Q)).
  Proof. iIntros (Hmono). iIntrosPostCrash. iFrame "∗". iApply Hmono. Qed.

  Lemma post_crash_mono P Q:
    (∀ hG, P hG -∗ Q hG) →
    post_crash P -∗ post_crash Q.
  Proof.
    iIntros (Hmono) "HP".
    iIntrosPostCrash.
    iDestruct ("HP" $! σ σ' hG' rel with "[$] [$] [$] [$]") as "($ & $ & $ & P)".
    by iApply Hmono.
  Qed.

  (* Lemma post_crash_pers P Q: *)
  (*   (P -∗ post_crash Q) → *)
  (*   □ P -∗ post_crash (λ hG, □ Q hG). *)
  (* Proof. *)
  (*   iIntros (Hmono) "#HP". iIntros (???) "#Hrel". *)
  (*   iModIntro. iApply Hmono; eauto. *)
  (* Qed. *)

  Lemma post_crash_sep P Q:
    post_crash P ∗ post_crash Q -∗ post_crash (λ hG, P hG ∗ Q hG).
  Proof.
    iIntros "(HP & HQ)".
    iIntrosPostCrash.
    iDestruct ("HP" $! σ σ' hG' rel with "[$] [$] [$] [$]") as "(map & ctxPre & ctxPost & $)".
    iDestruct ("HQ" $! σ σ' hG' rel with "[$] [$] [$] [$]") as "$".
  Qed.

  (* Lemma post_crash_or P Q: *)
  (*   post_crash P ∨ post_crash Q -∗ post_crash (λ hG, P hG ∨ Q hG). *)
  (* Proof. *)
  (*   iIntros "[HP|HQ]"; iIntros (???) "#Hrel". *)
  (*   - iLeft. by iApply "HP". *)
  (*   - iRight. by iApply "HQ". *)
  (* Qed. *)

  (* Lemma post_crash_and P Q: *)
  (*   post_crash P ∧ post_crash Q -∗ post_crash (λ hG, P hG ∧ Q hG). *)
  (* Proof. *)
  (*   iIntros "HPQ"; iIntros (???) "#Hrel". *)
  (*   iSplit. *)
  (*   - iDestruct "HPQ" as "(HP&_)". by iApply "HP". *)
  (*   - iDestruct "HPQ" as "(_&HQ)". by iApply "HQ". *)
  (* Qed. *)

  (* Lemma post_crash_pure (P: Prop) : *)
  (*   P → ⊢ post_crash (λ _, ⌜ P ⌝). *)
  (* Proof. *)
  (*   iIntros (????); eauto. *)
  (* Qed. *)

  (* Lemma post_crash_nodep (P: iProp Σ) : *)
  (*   P -∗ post_crash (λ _, P). *)
  (* Proof. iIntros "HP". iIntros (???); eauto. Qed. *)

  (* Lemma post_crash_exists {A} P Q: *)
  (*   (∀ (x: A), P hG x -∗ post_crash (λ hG, Q hG x)) -∗ *)
  (*   (∃ x, P hG x) -∗ post_crash (λ hG, ∃ x, Q hG x). *)
  (* Proof. *)
  (*   iIntros "Hall HP". iIntros (???) "#Hrel". *)
  (*   iDestruct "HP" as (x) "HP". *)
  (*   iExists x. iApply ("Hall" with "[$] [$]"). *)
  (* Qed. *)

  (* Lemma post_crash_forall {A} P Q: *)
  (*   (∀ (x: A), P hG x -∗ post_crash (λ hG, Q hG x)) -∗ *)
  (*   (∀ x, P hG x) -∗ post_crash (λ hG, ∀ x, Q hG x). *)
  (* Proof. *)
  (*   iIntros "Hall HP". iIntros (???) "#Hrel". *)
  (*   iIntros (?). iApply ("Hall" with "[HP] [$]"). iApply "HP". *)
  (* Qed. *)

  (* Lemma post_crash_exists_intro {A} P (x: A): *)
  (*   (∀ (x: A), P hG x -∗ post_crash (λ hG, P hG x)) -∗ *)
  (*   P hG x -∗ post_crash (λ hG, ∃ x, P hG x). *)
  (* Proof. *)
  (*   iIntros "Hall HP". iIntros (???) "#Hrel". *)
  (*   iExists x. iApply ("Hall" with "[$] [$]"). *)
  (* Qed. *)

  (* Global Instance from_exist_post_crash {A} (Φ: nvmG Σ → iProp Σ) (Ψ: nvmG Σ → A → iProp Σ) *)
  (*   {Himpl: ∀ hG, FromExist (Φ hG) (λ x, Ψ hG x)} : *)
  (*   FromExist (post_crash (λ hG, Φ hG)) (λ x, post_crash (λ hG, Ψ hG x)). *)
  (* Proof. *)
  (*   hnf; iIntros "H". *)
  (*   iDestruct "H" as (x) "H". *)
  (*   rewrite /post_crash. *)
  (*   iIntros (σ σ' hG') "Hrel". *)
  (*   iSpecialize ("H" with "Hrel"). *)
  (*   iExists x; iFrame. *)
  (* Qed. *)

  (* Lemma post_crash_named P name: *)
  (*   named name (post_crash (λ hG, P hG)) -∗ *)
  (*   post_crash (λ hG, named name (P hG)). *)
  (* Proof. rewrite //=. Qed. *)

  Lemma post_crash_persisted V :
    persisted V -∗
      post_crash (λ hG', persisted (hG := hG') V ∗ ∃ RV, ⌜V ⊑ RV⌝ ∗ recovered (hG := hG') RV).
  Proof.
    iIntros "pers".
    iIntrosPostCrash.
    iFrame.
    iDestruct ("perToRec" with "pers") as "[$ $]".
  Qed.

  Lemma post_crash_persisted_persiste V :
    persisted V -∗ post_crash (λ hG', persisted V).
  Proof.
    iIntros "pers".
    iDestruct (post_crash_persisted with "pers") as "p".
    iApply (post_crash_mono with "p").
    iIntros (?) "[??]". iFrame.
  Qed.

  Lemma post_crash_persisted_recovered V :
    persisted V -∗ post_crash (λ hG', ∃ RV, ⌜V ⊑ RV⌝ ∗ recovered (hG := hG') RV).
  Proof.
    iIntros "pers".
    iDestruct (post_crash_persisted with "pers") as "p".
    iApply (post_crash_mono with "p").
    iIntros (?) "[??]". iFrame.
  Qed.

  Lemma post_crash_mapsto ℓ hist :
    ℓ ↦h hist -∗ post_crash (λ hG', mapsto_post_crash hG' ℓ hist).
  Proof.
    iIntros "pts".
    iIntrosPostCrash.
    iAssert (⌜σ.1 !! ℓ = Some hist⌝)%I as %elemof.
    { iApply (gen_heap_valid with "heap pts"). }
    iDestruct (big_sepM_lookup_acc with "map") as "[[pts' | newPts] reIns]"; first done.
    { iDestruct (mapsto_ne with "pts pts'") as %hi. done. }
    (* We reinsert. *)
    iDestruct ("reIns" with "[$pts]") as "map".
    iFrame.
  Qed.

End post_crash_prop.

(* Section IntoCrash. *)

(*   Context `{hG: !nvmG Σ}. *)
(*   Global Instance sep_into_crash P P' Q Q': *)
(*     IntoCrash P P' → *)
(*     IntoCrash Q Q' → *)
(*     IntoCrash (P ∗ Q)%I (λ hG, P' hG ∗ Q' hG)%I. *)
(*   Proof. *)
(*     iIntros (H1 H2). rewrite /IntoCrash. *)
(*     rewrite (@into_crash _ _ P). *)
(*     rewrite (@into_crash _ _ Q). *)
(*     rewrite post_crash_sep //. *)
(*   Qed. *)

(*   Global Instance or_into_crash P P' Q Q': *)
(*     IntoCrash P P' → *)
(*     IntoCrash Q Q' → *)
(*     IntoCrash (P ∨ Q)%I (λ hG, P' hG ∨ Q' hG)%I. *)
(*   Proof. *)
(*     iIntros (H1 H2). rewrite /IntoCrash. *)
(*     rewrite (@into_crash _ _ P). *)
(*     rewrite (@into_crash _ _ Q). *)
(*     rewrite post_crash_or //. *)
(*   Qed. *)

(*   Global Instance and_into_crash P P' Q Q': *)
(*     IntoCrash P P' → *)
(*     IntoCrash Q Q' → *)
(*     IntoCrash (P ∧ Q)%I (λ hG, P' hG ∧ Q' hG)%I. *)
(*   Proof. *)
(*     iIntros (H1 H2). rewrite /IntoCrash. *)
(*     rewrite (@into_crash _ _ P). *)
(*     rewrite (@into_crash _ _ Q). *)
(*     rewrite post_crash_and //. *)
(*   Qed. *)

(*   (* XXX: probably should rephrase in terms of IntoPure *) *)
(*   Global Instance pure_into_crash (P: Prop) : *)
(*     IntoCrash (⌜ P ⌝%I) (λ _, ⌜ P ⌝%I). *)
(*   Proof. rewrite /IntoCrash. iIntros "%". by iApply post_crash_pure. Qed. *)

(*   Global Instance exist_into_crash {A} Φ Ψ: *)
(*     (∀ x : A, IntoCrash (Φ x) (λ hG, Ψ hG x)) → *)
(*     IntoCrash (∃ x, Φ x)%I (λ hG, (∃ x, Ψ hG x)%I). *)
(*   Proof. *)
(*     rewrite /IntoCrash. *)
(*     iIntros (?) "H". iDestruct "H" as (?) "HΦ". iPoseProof (H with "[$]") as "HΦ". *)
(*     iApply (post_crash_mono with "HΦ"). eauto. *)
(*   Qed. *)

(*   Global Instance forall_into_crash {A} Φ Ψ: *)
(*     (∀ x : A, IntoCrash (Φ x) (λ hG, Ψ hG x)) → *)
(*     IntoCrash (∀ x, Φ x)%I (λ hG, (∀ x, Ψ hG x)%I). *)
(*   Proof. *)
(*     rewrite /IntoCrash. *)
(*     iIntros (?) "H". iApply post_crash_forall; last eauto. iIntros (?). iApply H. *)
(*   Qed. *)

(*   (* *)
(*   Global Instance post_crash_into_crash P: *)
(*     IntoCrash (post_crash P) P. *)
(*   Proof. rewrite /IntoCrash. by iApply post_crash_mono. Qed. *)
(*    *) *)

(*   Lemma into_crash_proper P P' Q Q': *)
(*     IntoCrash P Q → *)
(*     (P ⊣⊢ P') → *)
(*     (∀ hG, Q hG ⊣⊢ Q' hG) → *)
(*     IntoCrash P' Q'. *)
(*   Proof. *)
(*     rewrite /IntoCrash. *)
(*     iIntros (HD Hwand1 Hwand2) "HP". *)
(*     iApply post_crash_mono; last first. *)
(*     { iApply HD. iApply Hwand1. eauto. } *)
(*     intros. simpl. by rewrite Hwand2. *)
(*   Qed. *)

(*   Global Instance big_sepL_into_crash: *)
(*     ∀ (A : Type) Φ (Ψ : nvmG Σ → nat → A → iProp Σ) (l : list A), *)
(*     (∀ (k : nat) (x : A), IntoCrash (Φ k x) (λ hG, Ψ hG k x)) → *)
(*     IntoCrash ([∗ list] k↦x ∈ l, Φ k x)%I (λ hG, [∗ list] k↦x ∈ l, Ψ hG k x)%I. *)
(*   Proof. *)
(*     intros. *)
(*     cut (∀ n, IntoCrash ([∗ list] k↦x ∈ l, Φ (n + k)%nat x)%I *)
(*                         (λ hG, [∗ list] k↦x ∈ l, Ψ hG (n + k)%nat x)%I). *)
(*     { intros Hres. specialize (Hres O). eauto. } *)
(*     induction l => n. *)
(*     - rewrite //=. apply _. *)
(*     - rewrite //=. apply sep_into_crash; eauto. *)
(*       eapply into_crash_proper; first eapply (IHl (S n)). *)
(*       * intros. setoid_rewrite Nat.add_succ_r. setoid_rewrite <-Nat.add_succ_l. eauto. *)
(*       * intros. setoid_rewrite Nat.add_succ_r. setoid_rewrite <-Nat.add_succ_l. eauto. *)
(*   Qed. *)

(*   Global Instance big_sepM_into_crash `{Countable K} : *)
(*     ∀ (A : Type) Φ (Ψ : nvmG Σ → K → A → iProp Σ) (m : gmap K A), *)
(*     (∀ (k : K) (x : A), IntoCrash (Φ k x) (λ hG, Ψ hG k x)) → *)
(*     IntoCrash ([∗ map] k↦x ∈ m, Φ k x)%I (λ hG, [∗ map] k↦x ∈ m, Ψ hG k x)%I. *)
(*   Proof. *)
(*     intros. induction m using map_ind. *)
(*     - eapply (into_crash_proper True%I _ (λ _, True%I)). *)
(*       { apply _. } *)
(*       * rewrite big_sepM_empty; eauto. *)
(*       * intros. rewrite big_sepM_empty; eauto. *)
(*     - eapply (into_crash_proper (Φ i x ∗ [∗ map] k↦x0 ∈ m, Φ k x0) _ *)
(*                                 (λ _, (Ψ _ i x ∗ [∗ map] k↦x0 ∈ m, Ψ _ k x0)%I)). *)
(*       { apply _. } *)
(*       * rewrite big_sepM_insert //=. *)
(*       * intros. rewrite big_sepM_insert //=. *)
(*   Qed. *)

(*   Global Instance big_sepS_into_crash `{Countable K} : *)
(*     ∀ Φ (Ψ : nvmG Σ → K → iProp Σ) (m : gset K), *)
(*     (∀ (k : K), IntoCrash (Φ k) (λ hG, Ψ hG k)) → *)
(*     IntoCrash ([∗ set] k ∈ m, Φ k)%I (λ hG, [∗ set] k ∈ m, Ψ hG k)%I. *)
(*   Proof. *)
(*     intros. induction m as [|i m ? IH] using set_ind_L => //=. *)
(*     - eapply (into_crash_proper True%I _ (λ _, True%I)). *)
(*       { apply _. } *)
(*       * rewrite big_sepS_empty; eauto. *)
(*       * intros. rewrite big_sepS_empty; eauto. *)
(*     - eapply (into_crash_proper (Φ i ∗ [∗ set] k ∈ m, Φ k) _ *)
(*                                 (λ _, (Ψ _ i ∗ [∗ set] k ∈ m, Ψ _ k)%I)). *)
(*       { apply _. } *)
(*       * rewrite big_sepS_insert //=. *)
(*       * intros. rewrite big_sepS_insert //=. *)
(*   Qed. *)

(*   Lemma into_crash_post_crash_frame_l P P' `{!IntoCrash P P'} Q: *)
(*     P -∗ post_crash Q -∗ post_crash (λ hG', P' hG' ∗ Q hG'). *)
(*   Proof. iIntros "HP HQ". rewrite (@into_crash _ _ P). iApply post_crash_sep. iFrame. Qed. *)

(*   Lemma into_crash_post_crash_frame_r P P' `{!IntoCrash P P'} Q: *)
(*     post_crash Q -∗ P  -∗ post_crash (λ hG', Q hG' ∗ P' hG'). *)
(*   Proof. iIntros "HP HQ". rewrite (@into_crash _ _ P). iApply post_crash_sep. iFrame. Qed. *)

(* End IntoCrash. *)
(* End goose_lang. *)

(* Lemma modus_ponens {Σ} (P Q: iProp Σ)  : P -∗ (P -∗ Q) -∗ Q. *)
(* Proof. iIntros "HP Hwand". by iApply "Hwand". Qed. *)

(* Ltac crash_env Γ := *)
(*   match Γ with *)
(*     | environments.Enil => idtac *)
(*     | environments.Esnoc ?Γ' ?id (post_crash _) => crash_env Γ' *)
(*     | environments.Esnoc ?Γ' ?id ?A => first [ iEval (rewrite (@into_crash _ _ _ _ _ A) )in id || iClear id ] ; crash_env Γ' *)
(*   end. *)

(* Ltac crash_ctx := *)
(*   match goal with *)
(*   | [ |- environments.envs_entails ?Γ _] => *)
(*     let spatial := pm_eval (environments.env_spatial Γ) in *)
(*     let intuit := pm_eval (environments.env_intuitionistic Γ) in *)
(*     crash_env spatial; crash_env intuit *)
(*   end. *)

(* Ltac iCrash := *)
(*   crash_ctx; *)
(*   iApply (modus_ponens with "[-]"); [ iNamedAccu | ]; *)
(*   rewrite ?post_crash_named ?post_crash_sep; iApply post_crash_mono; *)
(*   intros; simpl; *)
(*   let H := iFresh in iIntros H; iNamed H. *)

(* Section goose_lang. *)
(* Context `{ffi_semantics: ext_semantics}. *)
(* Context `{!ffi_interp ffi}. *)
(* Context {Σ: gFunctors}. *)
(* Section modality_alt. *)
(*   Context `{hG: !nvmG Σ}. *)
(*   Context `{Hi1: !IntoCrash P P'}. *)
(*   Context `{Hi2: !IntoCrash Q Q'}. *)
(*   Lemma test R : *)
(*     P -∗ Q -∗ R -∗ post_crash (λ hG', P' hG' ∗ Q' hG'). *)
(*   Proof using All. *)
(*     iIntros "HP HQ HR". iCrash. iFrame. *)
(*   Qed. *)

(* End modality_alt. *)
