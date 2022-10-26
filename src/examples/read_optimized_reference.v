From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import tactics.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances.
From self.high Require Import proofmode wpc_proofmode if_rec.
From self.high Require Import dprop abstract_state_instances modalities
     resources crash_weakestpre weakestpre weakestpre_na weakestpre_at
     recovery_weakestpre lifted_modalities protocol protocols no_buffer
     mapsto_na_flushed.
From self.high.modalities Require Import fence.

(* Implementation. *)

Definition RR_init : expr :=
  λ: "v",
    let: "per" := ref_NA "v" in
    Flush "per" ;;
    FenceSync ;;
    let: "vol" := ref_NA "v" in
    ("per", "vol").

Definition RR_read : expr :=
  λ: "rr", !_NA (Snd "rr").

Definition RR_write : expr :=
  λ: "rr" "v",
    let: "per" := Fst "rr" in
    let: "vol" := Snd "rr" in
    "per" <-_NA "v" ;;
    Flush "per" ;;
    FenceSync ;;
    "vol" <-_NA "v".

Definition RR_recover : expr :=
  λ: "rr",
    let: "per" := Fst "rr" in
    let: "vol" := ref_NA (!_NA "per") in
    ("per", "vol").

Section spec.
  Context `{nvmG Σ}.
  Context `{!stagedG Σ}.

  Program Definition rr_prot : LocationProtocol (numbered val) :=
    {| p_inv := λ '(mk_numbered t v) v', ⌜ v = v' ⌝%I;
       p_bumper v := v |}.

  Global Instance rr_prot_conditions : ProtocolConditions rr_prot.
  Proof.
    split; try apply _.
    - destruct s. simpl. apply _.
    - iIntros ([?] ?) "? /=". iModIntro. done.
  Qed.

  Definition is_RR (vrr : val) v : dProp Σ :=
    ∃ (ℓp ℓv : loc) n ss,
      "->" ∷ ⌜ vrr = (#ℓp, #ℓv)%V ⌝ ∗
      "pPts" ∷ ℓp ↦_{rr_prot} [mk_numbered n v] ∗
      "perLb" ∷ persist_lb ℓp rr_prot (mk_numbered n v) ∗
      "vPts" ∷ ℓv ↦_{rr_prot} (ss ++ [mk_numbered n v]).

  Definition is_recoverable_RR (vrr : val) v : dProp Σ :=
    ∃ (ℓp ℓv : loc) n,
      "->" ∷ ⌜ vrr = (#ℓp, #ℓv)%V ⌝ ∗
      "pPts" ∷ ℓp ↦_{rr_prot} [mk_numbered n v] ∗
      "perLb" ∷ persist_lb ℓp rr_prot (mk_numbered n v).

  Lemma crash_condition_impl' n v ℓp (ℓv : loc) :
    ℓp ↦_{rr_prot} [mk_numbered n v] -∗
    persist_lb ℓp rr_prot (mk_numbered n v) -∗
    <PC> is_recoverable_RR (#ℓp, #ℓv) v.
  Proof.
    iIntros "pPts perLb".
    iModIntro.
    iDestruct "perLb" as "(per & Hh)".
    iDestruct "Hh" as (sRec incl) "#crashedIn".
    iDestruct (crashed_in_if_rec with "crashedIn pPts")
      as (??) "(%prefix & crashedIn2 & pPts)".
    apply prefix_app_singleton in prefix as [-> ->].
    simpl.
    iExists ℓp, ℓv, n.
    iSplitPure; first done.
    simpl.
    iFrame "pPts".
    iFrame "per".
  Qed.

  Lemma is_RR_post_crash vrr v :
    is_RR vrr v ⊢ <PC> is_recoverable_RR vrr v.
  Proof.
    iNamed 1.
    iApply (crash_condition_impl' with "pPts perLb").
  Qed.

  Lemma RR_init_spec (v : val) s E :
    ⊢ WPC RR_init v @ s; E {{ rv, is_RR rv v }} {{ True }}%I.
  Proof.
    rewrite /RR_init.
    iApply wp_wpc.
    wp_pures.
    wp_apply (wp_alloc_na v (mk_numbered 0 v) rr_prot); simpl; first done.
    iIntros (ℓp) "pPts".
    wp_pures.
    wp_apply (wp_flush_na _ _ _ _ [] with "pPts").
    iIntros "(pPts & _ & perLb)".
    wp_pures.
    wp_apply wp_fence_sync. iModIntro.
    wp_pures.
    wp_apply (wp_alloc_na v (mk_numbered 0 v) rr_prot); simpl; first done.
    iIntros (ℓv) "vPts".
    wp_pures.
    iModIntro. iExists _, _, _, [].
    iSplitPure; first done. iFrameF "pPts". iFrame "vPts perLb".
  Qed.

  Lemma crash_condition_impl n v ℓp (ℓv : loc) :
    ℓp ↦_{rr_prot} [mk_numbered n v] -∗
    ℓv ↦_{rr_prot} [mk_numbered n v] -∗
    persist_lb ℓp rr_prot (mk_numbered n v) -∗
    <PC> is_recoverable_RR (#ℓp, #ℓv) v.
  Proof.
    iIntros "pPts vPts perLb".
    iApply is_RR_post_crash.
    iExists ℓp, ℓv, n, [].
    iSplitPure; first done.
    iFrame.
  Qed.

  Lemma prefix_of_2 {A} (xs : list A) x1 x2 :
    xs `prefix_of` [x1; x2] →
    xs = [] ∨ xs = [x1] ∨ xs = [x1; x2].
  Proof.
    destruct xs as [|x1' xs]. { naive_solver. }
    intros [-> pre]%prefix_cons_inv.
    destruct xs as [|x2' xs]. { naive_solver. }
    apply prefix_cons_inv in pre as [-> pre].
    apply prefix_nil_inv in pre as ->.
    naive_solver.
  Qed.

  Lemma crash_condition_impl_2 n v w ℓp (ℓv : loc) :
    ℓp ↦_{rr_prot} [mk_numbered n v; mk_numbered (n + 1) w] -∗
    persist_lb ℓp rr_prot (mk_numbered n v) -∗
    <PC> ∃ u, is_recoverable_RR (#ℓp, #ℓv) u ∗ ⌜ u = v ∨ u = w ⌝.
  Proof.
    iIntros "pPts perLb".
    iCrashIntro.
    iDestruct "perLb" as "[per (% & hi & crashedIn)]".
    iDestruct (crashed_in_if_rec with "crashedIn pPts")
      as (??) "(%pre & crashedIn2 & pPts)".
    apply prefix_of_2 in pre as [eq | [eq | eq]].
    { destruct ss'; inversion eq. }
    - destruct ss'; inversion eq.
      2: { destruct ss'; inversion eq. }
      iExists v.
      iSplit; last naive_solver.
      repeat iExists _.
      iSplitPure; first done.
      iFrameF "pPts".
      simpl.
      iFrame "per".
    - destruct ss'; inversion eq.
      destruct ss'; inversion eq.
      2: { simpl in eq. destruct ss'; inversion eq. }
      iExists w.
      iSplit; last naive_solver.
      iExists _, _, (n + 1).
      iSplitPure; first done.
      iDestruct (crashed_in_persist_lb with "crashedIn2") as "#per2".
      simpl.
      iFrame "per2".
      iDestruct (mapsto_na_persist_lb with "pPts per2") as "HII".
      { intros [?|?]; lia. }
      iFrame "HII".
  Qed.

  Lemma RR_read_spec rv (v : val) s E :
    is_RR rv v -∗
    WPC RR_read rv @ s; E {{ w, ⌜ v = w ⌝ ∗ is_RR rv v }}
                          {{ <PC> is_recoverable_RR rv v }}%I.
  Proof.
    iNamed 1.
    rewrite /RR_read.
    wpc_pures.
    { iApply (crash_condition_impl' with "pPts perLb"). }
    iApply wpc_atomic_no_mask.
    iSplit.
    { iApply (crash_condition_impl' with "pPts perLb"). }
    wp_apply (wp_load_na with "[$vPts]").
    { apply last_snoc. }
    { iModIntro. simpl.
      iIntros (?) "#H". iFrame "H". rewrite right_id. iApply "H". }
    iIntros (?) "(vPts & <-)".
    iSplit.
    { iModIntro.
      iApply (crash_condition_impl' with "pPts perLb"). }
    iModIntro. iSplitPure; first reflexivity.
    repeat iExists _.
    iFrame "pPts vPts perLb".
    done.
  Qed.

  Lemma RR_write_spec rv (v w : val) s E :
    is_RR rv v -∗
    WPC RR_write rv w @ s; E
      {{ _, is_RR rv w }}
      {{ <PC> ∃ u, is_recoverable_RR rv u ∗ ⌜ u = v ∨ u = w ⌝}}%I.
  Proof.
    iNamed 1.
    rewrite /RR_write.
    wpc_pures.
    { iApply post_crash_mono;
        last iApply (crash_condition_impl' with "pPts perLb").
      iIntros "H". iExists _. iFrame "H". naive_solver. }

    wpc_bind (_ <-_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit.
    { iApply post_crash_mono;
        last iApply (crash_condition_impl' with "pPts perLb").
      iIntros "H". iExists _. iFrame "H". naive_solver. }
    iApply (wp_store_na _ rr_prot _ _ _ (mk_numbered (n + 1) w) with "[$pPts]").
    { done. }
    { apply numbered_le. lia. }
    { simpl. done. }
    iIntros "!> pPts".
    iSplit.
    { iApply (crash_condition_impl_2 with "pPts perLb"). }
    iModIntro.
    wpc_pures.
    { iApply (crash_condition_impl_2 with "pPts perLb"). }

    wpc_bind (Flush _)%E.
    iApply wpc_atomic_no_mask.
    iSplit.
    { iApply (crash_condition_impl_2 with "pPts perLb"). }
    iApply (wp_flush_na with "pPts").
    iNext.
    iIntros "(pPts & ? & pLb)".
    iSplit.
    { iModIntro. iApply (crash_condition_impl_2 with "pPts perLb"). }
    iModIntro.
    wpc_pures.
    { iApply (crash_condition_impl_2 with "pPts perLb"). }

    (* The fence. *)
    wpc_bind (FenceSync)%E.
    iApply wpc_atomic_no_mask.
    iSplit. { iApply (crash_condition_impl_2 with "pPts perLb"). }
    iApply wp_fence_sync. do 2 iModIntro.
    iSplit. { iApply (crash_condition_impl_2 with "pPts perLb"). }
    iModIntro.
    iDestruct "pLb" as "#pLb".
    wpc_pures.
    { iApply (crash_condition_impl_2 with "pPts perLb"). }

    iDestruct (mapsto_na_persist_lb with "pPts pLb") as "pPts".
    { intros [?|?]; lia. }

    iApply wpc_atomic_no_mask.
    iSplit. {
      iApply post_crash_mono;
        last iApply (crash_condition_impl' with "pPts pLb").
      iIntros "H". iExists _. iFrame "H". naive_solver. }

    iApply (wp_store_na _ rr_prot _ _ _ (mk_numbered (n + 1) w) with "[$vPts]").
    { apply last_snoc. }
    { apply numbered_le. lia. }
    { simpl. done. }
    iIntros "!> vPts".
    iSplit. {
      iApply post_crash_mono;
        last iApply (crash_condition_impl' with "pPts pLb").
      iIntros "H". iExists _. iFrame "H". naive_solver. }
    iModIntro.
    repeat iExists _.
    iSplitPure; first done.
    iFrameF "pPts".
    iFrameF "pLb".
    iFrame "vPts".
  Qed.

  Lemma RR_recover_spec rv (v w : val) s E :
    is_recoverable_RR rv v -∗
    WPC RR_recover rv @ s; E
      {{ rv2, is_RR rv2 v }}
      {{ <PC> is_recoverable_RR rv v }}%I.
  Proof.
    iNamed 1.
    rewrite /RR_recover.
    wpc_pures.
    { iApply (crash_condition_impl' with "pPts perLb"). }

    wpc_bind (!_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit.
    { iApply (crash_condition_impl' with "pPts perLb"). }
    wp_apply (wp_load_na with "[$pPts]").
    { done. }
    { iModIntro. simpl.
      iIntros (?) "#H". iFrame "H". rewrite right_id. iApply "H". }
    iIntros (?) "(pPts & <-)".
    iSplit.
    { iModIntro.
      iApply (crash_condition_impl' with "pPts perLb"). }
    iModIntro.

    wpc_bind (ref_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit. { iApply (crash_condition_impl' with "pPts perLb"). }
    wp_apply (wp_alloc_na v (mk_numbered n v) rr_prot); simpl; first done.
    iIntros (ℓv') "vPts".
    iSplit.
    { iModIntro.
      iApply (crash_condition_impl' with "pPts perLb"). }
    iModIntro.

    wpc_pures.
    { iApply (crash_condition_impl' with "pPts perLb"). }
    iModIntro.
    iExists _, _, _, [].
    iSplitPure; first done.
    iFrameF "pPts".
    iFrameF "perLb".
    iFrame "vPts".
  Qed.

End spec.
