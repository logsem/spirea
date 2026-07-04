From iris_named_props Require Import named_props.
From iris.algebra Require Import excl.

From self.high.lib Require Import abstract_state abstract_state_instances.
From self.high Require Import protocol wpc_proofmode.
From self.high Require Import recovery_weakestpre adequacy.

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
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ}.

  Definition rr_prot : LocationProtocol (numbered val) :=
    {| p_full := λ '(mk_numbered t v) v', ⌜ v = v' ⌝%I;
       p_read := λ '(mk_numbered t v) v', ⌜ v = v' ⌝%I;
       p_pers := λ '(mk_numbered t v) v', ⌜ v = v' ⌝%I;
       p_bumper v := v |}.

  Global Instance rr_prot_conditions ℓ : ProtocolConditions ℓ rr_prot.
  Proof.
    split.
    - intros ?? ?. done.
    - intros [t v] v'. apply _.
    - intros [t v] v'. apply _.
    - intros [t v] v'. apply _.
    - intros [t v] v'. rewrite /rr_prot /=.
      iSplit; first naive_solver.
      iIntros "[$ _]".
    - iIntros "_" (σ_p v_p σ_f v_f) "% Hpers Hfull".
      destruct σ_f as [tf vf].
      iDestruct "Hfull" as %<-.
      iSplit.
      + iModIntro. iModIntro. iIntros "_". by iSplit.
      + iIntros (σ_c v_c) "!> Hread % %".
        destruct σ_c as [tc vc].
        iDestruct "Hread" as %<-.
        iModIntro. iModIntro. iIntros "_". by iSplit.
    - iIntros ([t v] v') "->". by iModIntro.
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
    <NG> is_recoverable_RR (#ℓp, #ℓv) v.
  Proof.
    iIntros "pPts #perLb".
    iModIntro.
    iDestruct "perLb" as "[per (%sRec & %incl & #crashedIn)]".
    iDestruct (crashed_in_if_rec with "crashedIn pPts")
      as "(%σs' & %σ' & %pre & #crashedIn2 & pPts)".
    iDestruct (crashed_in_agree with "crashedIn crashedIn2") as %->.
    apply prefix_app_singleton in pre as [-> ->].
    iDestruct (crashed_in_persist_lb with "crashedIn") as "#per2".
    simpl.
    iExists ℓp, ℓv, n.
    iSplitPure; first done.
    iFrame "pPts per2".
  Qed.

  Lemma is_RR_post_crash vrr v :
    is_RR vrr v ⊢ <NG> is_recoverable_RR vrr v.
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
    <NG> is_recoverable_RR (#ℓp, #ℓv) v.
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
    <NG> ∃ u, is_recoverable_RR (#ℓp, #ℓv) u ∗ ⌜ u = v ∨ u = w ⌝.
  Proof.
    iIntros "pPts #perLb".
    iModIntro.
    iDestruct "perLb" as "[per (%sRec & %incl & #crashedIn)]".
    iDestruct (crashed_in_if_rec with "crashedIn pPts")
      as "(%σs' & %σ' & %pre & #crashedIn2 & pPts)".
    iDestruct (crashed_in_agree with "crashedIn crashedIn2") as %->.
    apply prefix_of_2 in pre as [eq | [eq | eq]].
    { destruct σs'; inversion eq. }
    - destruct σs'; inversion eq.
      2: { destruct σs'; inversion eq. }
      subst σ'.
      iExists v.
      iSplit; last naive_solver.
      iExists _, _, n.
      iSplitPure; first done.
      iDestruct (crashed_in_persist_lb with "crashedIn") as "#per2".
      simpl.
      iFrame "pPts per2".
    - destruct σs' as [|? σs']; inversion eq.
      destruct σs'; inversion eq.
      2: { simpl in eq. destruct σs'; inversion eq. }
      subst σ'.
      iExists w.
      iSplit; last naive_solver.
      iExists _, _, (n + 1).
      iSplitPure; first done.
      iDestruct (crashed_in_persist_lb with "crashedIn") as "#per2".
      simpl.
      iFrame "per2".
      iDestruct (mapsto_na_persist_lb with "pPts per2") as "HII".
      { intros [?|?]; lia. }
      iFrame "HII".
  Qed.

  Lemma RR_read_spec rv (v : val) s E :
    is_RR rv v -∗
    WPC RR_read rv @ s; E {{ w, ⌜ v = w ⌝ ∗ is_RR rv v }}
                          {{ <NG> is_recoverable_RR rv v }}%I.
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
      {{ <NG> ∃ u, is_recoverable_RR rv u ∗ ⌜ u = v ∨ u = w ⌝}}%I.
  Proof.
    iNamed 1.
    rewrite /RR_write.
    wpc_pures.
    { iApply nextgen.nextgen_mono;
        last iApply (crash_condition_impl' with "pPts perLb").
      iIntros "H". iExists _. iFrame "H". naive_solver. }

    wpc_bind (_ <-_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit.
    { iApply nextgen.nextgen_mono;
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
      iApply nextgen.nextgen_mono;
        last iApply (crash_condition_impl' with "pPts pLb").
      iIntros "H". iExists _. iFrame "H". naive_solver. }

    iApply (wp_store_na _ rr_prot _ _ _ (mk_numbered (n + 1) w) with "[$vPts]").
    { apply last_snoc. }
    { apply numbered_le. lia. }
    { simpl. done. }
    iIntros "!> vPts".
    iSplit. {
      iApply nextgen.nextgen_mono;
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
      {{ <NG> is_recoverable_RR rv v }}%I.
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
    wp_apply (wp_alloc_na v (mk_numbered n v) rr_prot with "[]").
    { simpl. by iSplit. }
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
