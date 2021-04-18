From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map.
(* From Perennial.goose_lang Require Import proofmode notation. *)
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
(* From Perennial.goose_lang Require Import crash_modality typing adequacy lang. *)

From self Require Import extra.
From self.lang Require Import lang.
From self.base Require Import primitive_laws post_crash_modality.

Set Default Proof Using "Type".

(** Names for the heap that should be changed after a crash. *)
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
  name_heap_names : nvm_heap_names; (* Names used by [gen_heap]. *)
  name_store_view : gname;          (* Name used by the store view. *)
  name_persist_view : gname;        (* Name used by the persist view. *)
  name_recovered_view : gname;      (* Name used by the recover view. *)
}.

Definition nvm_get_names Σ (hG : nvmG Σ) : nvm_names :=
  {| name_heap_names := nvm_get_heap_names nvmG_gen_heapG;
     name_store_view := store_view_name;
     name_persist_view := persist_view_name;
     name_recovered_view := recovered_view_name |}.

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
     persist_view_name := names.(name_persist_view);
     recovered_view_name := names.(name_recovered_view) |}.

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

  Lemma store_inv_cut store p :
    store_inv store -∗ store_inv (slice_of_store p store).
  Proof.
  Admitted.

  (* Lemma store_inv_cut store p : *)
  (*   store_inv store -∗ store_inv (cut_store p store). *)
  (* Proof. *)
  (*   rewrite /store_inv. *)
  (*   (* rewrite /cut_store. *) *)
  (*   rewrite big_sepM_imap. *)
  (*   iIntros "m". *)
  (*   iApply (big_sepM_impl with "m"). *)
  (*   iModIntro. iIntros (ℓ hist eq) "[%iss m]". *)
  (*   destruct iss as [x eq']. *)
  (*   rewrite /discard_store_views. *)
  (*   iSplit. *)
  (*   { iPureIntro. eexists (Msg _ _ _). *)
  (*     rewrite /cut_history. *)
  (*     apply lookup_fmap_Some. *)
  (*     exists x. *)
  (*     split; first done. *)
  (*     apply map_filter_lookup_Some_2; [done|lia]. } *)
  (*   rewrite big_sepM_fmap. *)
  (*   rewrite big_sepM_filter. *)
  (*   iApply (big_sepM_impl with "m"). *)
  (*   iModIntro. iPureIntro. intros t msg eq2 incl le. *)
  (*   simpl. *)
  (*   apply view_empty_least. *)
  (* Qed. *)

  Definition persist_auth {hG : nvmG Σ} (σ : mem_config) := own persist_view_name (● σ.2).

  Instance tt (p : view) : CoreId (●□ p).
  Proof. do 2 constructor; simpl; auto. apply: core_id_core. Qed.

  Lemma nvm_heap_reinit (hG' : nvmG Σ) σ σ' (Hinv : invG Σ) (Hcrash : crashG Σ) :
    crash_step σ σ' →
    ⊢ gen_heap_interp (hG := @nvmG_gen_heapG _ hG') σ.1 -∗
      store_inv (hG := hG') σ.1 -∗
      persist_auth (hG := hG') σ
      ==∗
      ∃ names : nvm_names,
        (* ghost_crash_rel σ hG' σ' (nvm_update Σ hG' Hinv Hcrash names) ∗ *)
        post_crash_map σ.1 hG' (nvm_update Σ hG' Hinv Hcrash names) ∗
        nvm_heap_ctx (hG := nvm_update Σ hG' Hinv Hcrash names) σ' ∗
        persisted_impl hG' (nvm_update Σ hG' Hinv Hcrash names).
  Proof using hG Σ.
    iIntros ([store p p' pIncl]) "heapIntrp invs pers".
    rewrite /nvm_heap_ctx. simpl.
    (* Allocate a new heap at a _new_ ghost name. *)
    iMod (gen_heap_init_names (slice_of_store p' store)) as (γh γm) "(heapNew & ptsMap & _)".
    (* We persist/freeze the old persist view. *)
    iMod (own_update with "pers") as "pers".
    { apply auth_update_auth_persist. }
    iDestruct "pers" as "#oldPers".
    (* Allocate a new persist view. *)
    iMod (own_alloc (● p' ⋅ ◯ p')) as (persistG) "[pers #persFrag]".
    { apply auth_both_valid_2; [apply view_valid|done]. }
    (* Allocate the store view at a _new_ ghost name. *)
    iMod (own_alloc (● lub_view (slice_of_store p' store))) as (storeG) "store".
    { apply auth_auth_valid. apply view_valid. }
    (* Allocate the recovered view at a _new_ ghost name. *)
    iMod (own_alloc (to_agree p' : agreeR viewO)) as (recoveredG) "#recovered".
    { done. }
    (* iMod (own_update with "recovered") as "recovered". *)
    (* { apply auth_update_auth_persist. } *)
    (* iDestruct "recovered" as "#recovered". *)
    iModIntro.
    iExists {| name_heap_names := Build_nvm_heap_names γh γm;
               name_store_view := storeG;
               name_persist_view := persistG;
               name_recovered_view := recoveredG |}.
    iFrame.
    (* We show the ghost crash relation. *)
    (* iSplit. { done. } *)
    iSplitL "ptsMap heapIntrp".
    { iSplitL "heapIntrp".
      { iIntros (??) "pts".
        iApply (gen_heap_valid with "heapIntrp pts"). }
      rewrite /post_crash_map. rewrite /slice_of_store. simpl.
      rewrite /mapsto_post_crash. rewrite /recovered.

      iEval (rewrite -(map_union_filter (λ '(ℓ, _), is_Some(p' !! ℓ)) store)).
      rewrite big_sepM_union.
      2: { apply map_disjoint_filter. }
      iSplitR "recovered"; last first.
      { rewrite big_sepM_filter.
        iApply big_sepM_intuitionistically_forall.
        iModIntro. iIntros (ℓ hist look not).
        iRight.
        iRight.
        iIntros (t) "own". admit. }
        (* iDestruct (own_valid_2 with "recovered own") as %[_ [incl _]]%auth_both_dfrac_valid_discrete. *)
        (* iPureIntro. *)
        (* apply not. *)
        (* (* rewrite look in not. *) *)
        (* apply singleton_included_l in incl. *)
        (* destruct incl as [y [eq%leibniz_equiv _]]. *)
        (* exists y. done. } *)
      (* FIXME: This seems a bit difficult due to a lack of suitable lemmas. *)
      iApply (big_sepM_impl' with "ptsMap").
      * admit.
      * iModIntro. iIntros (ℓ hist hist').
        (* rewrite map_lookup_zip_with. *)
        (* rewrite lookup_map_zip_with. *)
        simpl.
        iIntros (look1 look2) "pts".
        iRight.
        admit. }
    iSplit.
    * iDestruct (store_inv_cut with "invs") as "$".
      iExists p'. iFrame "recovered".
    * iModIntro.
      iIntros (V) "pers".
      iAssert (⌜V ⊑ p⌝)%I as %incl.
      { iDestruct (own_valid_2 with "oldPers pers") as %[_ [incl _]]%auth_both_dfrac_valid_discrete.
        iPureIntro.
        apply incl. }
      iAssert (⌜V ⊑ p'⌝)%I as %incl'.
      { iPureIntro. etrans; done. }
      (* iDestrut (auth_both_valid_1). *)
      iSplit.
      - admit.
      - iExists p'. iFrame "%". iExists p'. iFrame "#".
        iPureIntro.
        apply map_Forall_lookup_2.
        done.
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
      iIntros "(heap & authStor & inv & pers & recov) Hg".
      (* Build new ghost state. *)
      iMod (nvm_heap_reinit _ _ _ _ Hc with "heap inv pers") as (hnames) "(map & interp' & persImpl)"; first apply Hcrash.
      iModIntro.
      iNext. iIntros (Hc' ?) "HNC".
      set (hG' := (nvm_update _ _ _ Hc' hnames)).
      rewrite /post_crash.
      iDestruct ("Hidemp" $! σ_pre_crash σ_post_crash hG' with "persImpl map") as "(? & ?)".
      iExists ({| pbundleT := hnames |}).
      iModIntro.
      rewrite /state_interp//=.
      iFrame. }
  Qed.

End wpr.
