From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map.
(* From Perennial.goose_lang Require Import proofmode notation. *)
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
(* From Perennial.goose_lang Require Import crash_modality typing adequacy lang. *)

From self.lang Require Import lang primitive_laws post_crash_modality.

Set Default Proof Using "Type".

Record nvm_heap_names := {
  name_gen_heap : gname;
  name_gen_meta : gname;
}.

Definition nvm_get_heap_names {V Σ} (hG : gen_heapG loc V Σ) : nvm_heap_names :=
  {| name_gen_heap := gen_heap_name hG ;
     name_gen_meta := gen_meta_name hG |}.

Definition nvm_heap_update {Σ} (h : gen_heapG loc history Σ) (names : nvm_heap_names) :=
  {| gen_heap_inG := gen_heap_inG;
     gen_heap_name := names.(name_gen_heap);
     gen_meta_name := names.(name_gen_meta) |}.

(** A record of all the ghost names useb by [nvmG] that needs to change after a
crash. *)
Record nvm_names := {
  name_heap_names : nvm_heap_names;   (* Names used by [gen_heap]. *)
  name_store_view : gname; (* Name used by the store view. *)
  (* Note that the persist view does not need to change. *)
}.

Canonical Structure nvm_namesO := leibnizO nvm_names.

(** Given an [hG : nvmG Σ], update the fields per the information in the rest of
the arguments. In particular, all the gnames in [names] replaces the
corresponding gnames in [hG]. *)
Definition nvm_update Σ (hG : nvmG Σ) (Hinv : invG Σ) (Hcrash : crashG Σ) (names : nvm_names) :=
  {| nvmG_invG := Hinv;
     nvmG_crashG := Hcrash;
     nvmG_gen_heapG := nvm_heap_update hG.(@nvmG_gen_heapG _) names.(name_heap_names);
     view_inG := hG.(@view_inG _);
     store_view_name := names.(name_store_view);
     persist_view_name := hG.(@persist_view_name _) |}.

Definition nvm_get_names Σ (hG : nvmG Σ) : nvm_names :=
  {| name_heap_names := nvm_get_heap_names nvmG_gen_heapG;
     name_store_view := store_view_name; |}.

(* Lemma heap_update_eq {Σ} heapG' (heapG : gen_heapG loc history Σ) : *)
(*   (@nvm_heap_update Σ heapG' (@nvm_get_heap_names (@gmap nat nat_eq_dec nat_countable message) Σ heapG)) *)
(*     = *)
(*   heapG. *)
(* Proof. *)
(*   destruct heapG'. *)
(*   destruct heapG. *)
(*   rewrite /nvm_get_heap_names. simpl. *)
(*   rewrite /nvm_heap_update. simpl. *)
(*   f_equal. *)
(* Abort. *)
(* (*   gen_heapPreG *) *)
(* (*   auto. *) *)
(* (* Qed. *) *)

Lemma nvm_update_id Σ hG :
  nvm_update Σ hG (iris_invG) (iris_crashG) (nvm_get_names _ hG) = hG.
Proof. destruct hG as [? ? []]. auto. Qed.

Program Global Instance nvmG_perennialG `{!nvmG Σ} : perennialG nvm_lang nvm_crash_lang nvm_namesO Σ := {
  perennial_irisG := λ Hcrash hnames,
                     @nvmG_irisG _ (nvm_update _ _ _ Hcrash (@pbundleT _ _ hnames));
  perennial_crashG := λ _ _, eq_refl;
  perennial_num_laters_per_step := λ n, n
}.
Next Obligation. eauto. Qed.

Lemma nvm_update_update Σ hG Hinv Hcrash names Hinv' Hcrash' names' :
  nvm_update Σ (nvm_update Σ hG Hinv' Hcrash' names') Hinv Hcrash names =
    nvm_update Σ hG Hinv Hcrash names.
Proof. auto. Qed.

Definition wpr `{hG : !nvmG Σ} `{hC : !crashG Σ} (s : stuckness) (k : nat) (E : coPset)
  (e : thread_state) (recv : thread_state) (Φ : thread_val → iProp Σ) (Φinv : nvmG Σ → iProp Σ) (Φr : nvmG Σ → thread_val → iProp Σ) :=
  wpr s k hC ({| pbundleT := nvm_get_names Σ _ |}) E e recv
              Φ
              (λ Hc names, Φinv (nvm_update _ _ _ Hc (@pbundleT _ _ names)))
              (λ Hc names v, Φr (nvm_update _ _ _ Hc (@pbundleT _ _ names)) v).

Section wpr.
  Context `{hG : !nvmG Σ}.
  (* Context {Σ : functorG}. *)
  Implicit Types s : stuckness.
  Implicit Types k : nat.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types Φc : iProp Σ.
  Implicit Types v : thread_val.
  Implicit Types e : thread_state.

  Lemma wpr_strong_mono s k E e rec Φ Ψ Φinv Ψinv Φr Ψr :
    wpr s k E e rec Φ Φinv Φr -∗
    (∀ v, Φ v ==∗ Ψ v) ∧ <bdisc> ((∀ hG, Φinv hG -∗ Ψinv hG) ∧ (∀ hG v, Φr hG v ==∗ Ψr hG v)) -∗
    wpr s k E e rec Ψ Ψinv Ψr.
  Proof.
    rewrite /wpr. iIntros "Hwpr Himpl".
    iApply (wpr_strong_mono with "Hwpr [Himpl]").
    repeat iSplit.
    - by iDestruct "Himpl" as "($&_)".
    - iIntros.
      iDestruct "Himpl" as "(_&H)".
      iModIntro.
      iSplit.
      * iIntros. by iApply "H".
      * iIntros. by iApply "H".
  Qed.

  Lemma nvm_heap_reinit (hG' : nvmG Σ) σ σ' (Hinv : invG Σ) (Hcrash : crashG Σ) :
    crash_step σ σ' →
    ⊢ nvm_heap_ctx (hG := hG') σ ==∗
        ∃ names : nvm_names,
          ghost_crash_rel σ hG' σ' (nvm_update Σ hG' Hinv Hcrash names) ∗
          nvm_heap_ctx (hG := nvm_update Σ hG' Hinv Hcrash names) σ'.
  Proof.
    iIntros ([store p p' pIncl]) "(? & ? & ? & pers)".
    rewrite /nvm_heap_ctx. simpl.
    (* Allocate a new heap at a _new_ ghost name. *)
    iMod (gen_heap_init_names (cut_history p' store)) as (γh γm) "[heap RSE]".
    (* Update the persisted view _in place_. *)
    iMod (auth_auth_view_grow_incl with "pers") as "pers".
    { apply pIncl. }
    (* Allocate the store view at a _new_ ghost name. *)
    iMod (own_alloc (● lub_view (cut_history p' store))) as (storeG) "store".
    { apply auth_auth_valid. apply view_valid. }
    iModIntro.
    iExists {| name_heap_names := Build_nvm_heap_names γh γm;
               name_store_view := storeG |}.
    iFrame.
    (* We show the ghost crash relation. *)
    iSplit. { done. }
  Admitted.

  Lemma idempotence_wpr `{!ffi_interp_adequacy} s k E1 e rec Φx Φinv Φrx Φcx :
    ⊢ WPC e @ s ; k ; E1 {{ Φx }} {{ Φcx hG }} -∗
    (□ ∀ (hG1 : nvmG Σ) (Hpf : @nvmG_invG Σ hG = @nvmG_invG Σ hG1) σ σ'
          (HC : crash_prim_step (nvm_crash_lang) σ σ'),
          Φcx hG1 -∗ ▷ post_crash (λ hG2, (Φinv hG2 ∧ WPC rec @ s ; k; E1 {{ Φrx hG2 }} {{ Φcx hG2 }}))) -∗
      wpr s k E1 e rec Φx Φinv Φrx.
  Proof.
    iIntros "Hwpc #Hidemp".
    iApply (idempotence_wpr s k E1 e rec _ _ _
                            (λ Hc names, Φcx (nvm_update _ _ _ Hc (@pbundleT _ _ names)))
                                                      with "[Hwpc] [Hidemp]"); first auto.
    { simpl. rewrite nvm_update_id. iAssumption. }
    { iModIntro. iIntros (? t σ_pre_crash g σ_post_crash Hcrash ns κs ?) "H".
      iSpecialize ("Hidemp" $! (nvm_update _ _ _ _ _) with "[//] [//] H").
      iIntros "interp Hg".
      (* Build new ghost state. *)
      iMod (nvm_heap_reinit _ _ _ _ Hc with "interp") as (hnames) "[%rel interp']"; first apply Hcrash.
      iModIntro.
      iNext. iIntros (Hc' ?) "HNC".
      set (hG' := (nvm_update _ _ _ Hc' hnames)).
      rewrite /post_crash.
      iDestruct ("Hidemp" $! σ_pre_crash σ_post_crash hG' rel) as "P".
      iExists ({| pbundleT := hnames |}).
      iModIntro.
      rewrite /state_interp//=.
      rewrite nvm_update_update.
      iFrame. }
  Qed.

End wpr.
