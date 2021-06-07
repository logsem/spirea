From stdpp Require Import numbers.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth dfrac.
From Perennial.base_logic.lib Require Import proph_map.
From Perennial.algebra Require Import proph_map.
(* From Perennial.goose_lang Require Import proofmode notation. *)
From Perennial.program_logic Require Import recovery_weakestpre recovery_adequacy.
(* From Perennial.goose_lang Require Import crash_modality typing adequacy lang. *)

From self Require Import extra.
From self.lang Require Import lang.
From self.base Require Import primitive_laws post_crash_modality.

Set Default Proof Using "Type".

(** Names for the heap that needs to change after a crash. *)
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

(** A record of all the ghost names useb by [nvmBaseG] that needs to change
after a crash. *)
Record nvm_base_names := {
  name_heap_names : nvm_heap_names; (* Names used by [gen_heap]. *)
  name_store_view : gname;          (* Name used by the store view. *)
  name_persist_view : gname;        (* Name used by the persist view. *)
  name_crashed_at_view : gname;      (* Name used by the crashed at view. *)
}.

Definition nvm_base_get_names Σ (hG : nvmBaseG Σ) : nvm_base_names :=
  {| name_heap_names := nvm_get_heap_names nvmBaseG_gen_heapG;
     name_store_view := store_view_name;
     name_persist_view := persist_view_name;
     name_crashed_at_view := crashed_at_view_name |}.

Canonical Structure nvm_base_namesO := leibnizO nvm_base_names.

(** Given an [hG : nvmBaseG Σ], update the fields per the information in the
rest of the arguments. In particular, all the gnames in [names] replaces the
corresponding gnames in [hG]. *)
Definition nvm_base_update Σ (hG : nvmBaseG Σ) (Hinv : invG Σ)
           (Hcrash : crashG Σ) (names : nvm_base_names) :=
  {| nvmBaseG_invG := Hinv;
     nvmBaseG_crashG := Hcrash;
     nvmBaseG_gen_heapG :=
       nvm_heap_update hG.(@nvmBaseG_gen_heapG _) names.(name_heap_names);
     view_inG := hG.(@view_inG _);
     store_view_name := names.(name_store_view);
     persist_view_name := names.(name_persist_view);
     crashed_at_view_name := names.(name_crashed_at_view) |}.

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

Lemma nvm_base_update_id Σ hG :
  nvm_base_update Σ hG (iris_invG) (iris_crashG) (nvm_base_get_names _ hG) = hG.
Proof. destruct hG as [? ? []]. auto. Qed.

Program Global Instance nvmBaseG_perennialG `{!nvmBaseG Σ} : perennialG nvm_lang nvm_crash_lang nvm_base_namesO Σ := {
  perennial_irisG := λ Hcrash hnames,
                     @nvmBaseG_irisG _ (nvm_base_update _ _ _ Hcrash (@pbundleT _ _ hnames));
  perennial_crashG := λ _ _, eq_refl;
  perennial_num_laters_per_step := λ n, n
}.
Next Obligation. eauto. Qed.
Next Obligation. eauto. Qed.

Lemma nvm_base_update_update Σ hG Hinv Hcrash names Hinv' Hcrash' names' :
  nvm_base_update Σ (nvm_base_update Σ hG Hinv' Hcrash' names') Hinv Hcrash names =
    nvm_base_update Σ hG Hinv Hcrash names.
Proof. auto. Qed.

Definition wpr `{hG : !nvmBaseG Σ} `{hC : !crashG Σ} (s : stuckness) (k : nat) (E : coPset)
  (e : thread_state) (recv : thread_state) (Φ : thread_val → iProp Σ) (Φinv : nvmBaseG Σ → iProp Σ) (Φr : nvmBaseG Σ → thread_val → iProp Σ) :=
  wpr s k hC ({| pbundleT := nvm_base_get_names Σ _ |}) E e recv
              Φ
              (λ Hc names, Φinv (nvm_base_update _ _ _ Hc (@pbundleT _ _ names)))
              (λ Hc names v, Φr (nvm_base_update _ _ _ Hc (@pbundleT _ _ names)) v).

Section wpr.
  Context `{hG : !nvmBaseG Σ}.
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
    consistent_cut p store →
    store_inv store -∗ store_inv (slice_of_store p store).
  Proof.
    rewrite /store_inv.
    iIntros (cut) "H".
    iApply (big_sepM_impl_sub with "H").
    { rewrite /slice_of_store. apply map_zip_with_dom_snd. }
    rewrite /hist_inv.
    iIntros "!>" (ℓ h h' look look') "[%some H]".
    rewrite /slice_of_store in look'.
    apply map_lookup_zip_with_Some in look'.
    destruct look' as ([t] & ? & ? & pLook & ?).
    iSplit.
    - iPureIntro.
      (* Extract info from consistent cut. *)
      rewrite /consistent_cut in cut.
      setoid_rewrite map_Forall_lookup in cut.
      pose proof (cut ℓ (MaxNat t) pLook) as (? & ? & ? & eq & ?).
      simplify_eq.
      rewrite eq.
      naive_solver.
    - destruct (x !! t); last naive_solver.
      simplify_eq.
      rewrite big_sepM_singleton.
      iPureIntro. apply view_empty_least.
  Qed.

  Definition persist_auth {hG : nvmBaseG Σ} (σ : mem_config) := own persist_view_name (● σ.2).

  Instance tt (p : view) : CoreId (●□ p).
  Proof. do 2 constructor; simpl; auto. apply: core_id_core. Qed.

  Lemma nvm_heap_reinit (hG' : nvmBaseG Σ) σ p p' (Hinv : invG Σ) (Hcrash : crashG Σ) :
    (* The first two assumptions are the content of [crash_step σ σ'] *)
    p ⊑ p' →
    consistent_cut p' σ →
    ⊢ gen_heap_interp (hG := @nvmBaseG_gen_heapG _ hG') σ -∗
      store_inv (hG := hG') σ -∗
      persist_auth (hG := hG') (σ, p)
      ==∗
      ∃ names : nvm_base_names,
        (* ghost_crash_rel σ hG' σ' (nvm_base_update Σ hG' Hinv Hcrash names) ∗ *)
        post_crash_map σ hG' (nvm_base_update Σ hG' Hinv Hcrash names) ∗
        nvm_heap_ctx (hG := nvm_base_update Σ hG' Hinv Hcrash names) (slice_of_store p' σ, view_to_zero p') ∗
        persisted_impl hG' (nvm_base_update Σ hG' Hinv Hcrash names) ∗
        own (@crashed_at_view_name _ (nvm_base_update Σ hG' Hinv Hcrash names)) (to_agree p' : agreeR viewO).
  Proof using hG Σ.
    iIntros (pIncl cut). iIntros  "heapIntrp invs pers".
    rewrite /nvm_heap_ctx. simpl.
    (* Allocate a new heap at a _new_ ghost name. *)
    iMod (gen_heap_init_names (slice_of_store p' σ)) as (γh γm) "(heapNew & ptsMap & _)".
    (* We persist/freeze the old persist view. *)
    iMod (own_update with "pers") as "pers".
    { apply auth_update_auth_persist. }
    iDestruct "pers" as "#oldPers".
    (* Allocate a new persist view. *)
    (* set newPersisted := ((λ _, MaxNat 0) <$> p). *)
    iMod (own_alloc (● (view_to_zero p') ⋅ ◯ (view_to_zero p'))) as (persistG) "[pers #persFrag]".
    { apply auth_both_valid_2; [apply view_valid|done]. }
    (* Allocate the store view at a _new_ ghost name. *)
    iMod (own_alloc (● lub_view (slice_of_store p' σ))) as (storeG) "store".
    { apply auth_auth_valid. apply view_valid. }
    (* Allocate the crashed at view at a _new_ ghost name. *)
    iMod (own_alloc (to_agree p' : agreeR viewO)) as (crashedAtG) "#crashed".
    { done. }
    iModIntro.
    iExists {| name_heap_names := Build_nvm_heap_names γh γm;
               name_store_view := storeG;
               name_persist_view := persistG;
               name_crashed_at_view := crashedAtG |}.
    rewrite /name_crashed_at_view. simpl.
    iFrame.
    iFrame "crashed".
    (* We show the ghost crash relation. *)
    iSplitL "ptsMap heapIntrp".
    { rewrite /post_crash_map.
      iSplitL "heapIntrp".
      { iIntros (???) "pts".
        iApply (gen_heap_valid with "heapIntrp pts"). }
      iApply (big_sepM_impl_2 with "ptsMap").
      iModIntro.
      iIntros (ℓ hist look) "disj".
      (* Note: The first value below is just a fancy way of writing [0]. *)
      iExists (Qcanon.Q2Qc (QArith_base.Qmake Z0 xH)), 1%Qc.
      rewrite if_non_zero_1. simpl. rewrite if_non_zero_0. simpl.
      iSplit; first done. iSplit; last done.
      iDestruct "disj" as "[(%hist' & %look' & pts)|%look']"; last first.
      * iRight.
        iIntros (CV') "crashed'".
        iDestruct (crashed_at_agree with "crashed' crashed") as %->.
        iPureIntro.
        eapply consistent_cut_lookup_slice; done.
      * iLeft.
        rewrite /slice_of_store in look'.
        apply map_lookup_zip_with_Some in look'.
        destruct look' as ([t] & ? & ? & p'Look & ?).
        rewrite /consistent_cut in cut.
        pose proof (map_Forall_lookup_1 _ _ _ _ cut p'Look) as (? & ? & ? & ? & map).
        simplify_eq.
        iExists _, _.
        iSplit; first done.
        rewrite H2.
        iFrame "pts".

        iExists _. iFrame "crashed %".
        iPureIntro.
        eapply (map_Forall_lookup_1 _ _ _ _ map).
        rewrite /cut_history.
        apply map_filter_lookup_Some_2; [done| reflexivity]. }
    iSplit.
    * simpl. iDestruct (store_inv_cut with "invs") as "$"; first done. simpl.
      iExists p'. iFrame "crashed".
    * iModIntro.
      iIntros (V) "pers".
      iDestruct (persisted_auth_included with "oldPers pers") as %incl.
      assert (V ⊑ p') as incl'. { etrans; done. }
      iSplit.
      { edestruct (view_to_zero_mono) as [? ->]; first apply incl'.
        iDestruct "persFrag" as "[$ _]". }
      iExists p'. iFrame "#%".
  Qed.

  Lemma nvm_heap_reinit_alt (hG' : nvmBaseG Σ) σ σ' (Hinv : invG Σ) (Hcrash : crashG Σ) Pg :
    crash_step σ σ' →
    ⊢ nvm_heap_ctx σ -∗
      post_crash Pg ==∗
      ∃ names : nvm_base_names,
        post_crash_map σ.1 hG' (nvm_base_update Σ hG' Hinv Hcrash names) ∗
        nvm_heap_ctx (hG := nvm_base_update Σ hG' Hinv Hcrash names) σ' ∗
        Pg (nvm_base_update Σ hG' Hinv Hcrash names).
  Proof using hG.
    iIntros ([store p p' pIncl cut]).
    iIntros "(heap & authStor & inv & pers & recov) Pg".
    iMod (nvm_heap_reinit _ _ _ _ _ Hcrash with "heap inv pers") as (hnames) "(map & interp' & #persImpl & rec)"; try done.
    rewrite /post_crash.
    iDestruct ("Pg" with "persImpl map") as "(map & Pg)".
    iExists _. iFrame.
    done.
  Qed.

  Lemma idempotence_wpr `{!ffi_interp_adequacy} s k E1 e rec Φx Φinv Φrx Φcx :
    ⊢ WPC e @ s ; k ; E1 {{ Φx }} {{ Φcx hG }} -∗
    (□ ∀ (hG1 : nvmBaseG Σ) (Hpf : @nvmBaseG_invG Σ hG = @nvmBaseG_invG Σ hG1) σ σ'
          (HC : crash_prim_step (nvm_crash_lang) σ σ'),
          Φcx hG1 -∗ ▷ post_crash (λ hG2, (Φinv hG2 ∧ WPC rec @ s ; k; E1 {{ Φrx hG2 }} {{ Φcx hG2 }}))) -∗
      wpr s k E1 e rec Φx Φinv Φrx.
  Proof.
    iIntros "Hwpc #Hidemp".
    iApply (idempotence_wpr s k E1 e rec _ _ _
                            (λ Hc names, Φcx (nvm_base_update _ _ _ Hc (@pbundleT _ _ names)))
                                                      with "[Hwpc] [Hidemp]"); first auto.
    { simpl. rewrite nvm_base_update_id. iAssumption. }
    { iModIntro. iIntros (? t σ_pre_crash g σ_post_crash Hcrash ns κs ?) "H".
      iSpecialize ("Hidemp" $! (nvm_base_update _ _ _ _ _) with "[//] [//] H").
      iIntros "interp _ !> !>".
      iIntros (Hc' ?) "HNC".
      iMod (nvm_heap_reinit_alt _ _ _ _ Hc' _ Hcrash with "interp Hidemp") as (hnames) "(map & interp' & idemp)".
      rewrite nvm_base_update_update.
      iExists {| pbundleT := hnames |}, (reflexivity _), (reflexivity _).
      iModIntro.
      rewrite /state_interp //=.
      rewrite /nvm_heap_ctx.
      iFrame. }
  Qed.

End wpr.
