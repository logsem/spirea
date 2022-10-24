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
    "vol" <-_NA "v" ;;
    #().

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
    ∃ (ℓp ℓv : loc) ss n,
      "%lastEq" ∷ ⌜ last ss = Some (mk_numbered n v) ⌝ ∗
      "->" ∷ ⌜ vrr = (#ℓp, #ℓv)%V ⌝ ∗
      "pPts" ∷ ℓp ↦_{rr_prot} ss ∗
      "perLb" ∷ persist_lb ℓp rr_prot (mk_numbered n v) ∗
      "vPts" ∷ ℓv ↦_{rr_prot} ss.

  Definition is_recoverable_RR (vrr : val) v : dProp Σ :=
    ∃ (ℓp ℓv : loc) ss n,
      ⌜ last ss = Some (mk_numbered n v) ⌝ ∗
      ⌜ vrr = (#ℓp, #ℓv)%V ⌝ ∗
      ℓp ↦_{rr_prot} ss ∗ persist_lb ℓp rr_prot (mk_numbered n v).

  Lemma is_RR_post_crash vrr v :
    is_RR vrr v ⊢ <PC> is_recoverable_RR vrr v.
  Proof.
    iDestruct 1 as (ℓp ℓv ss n) "(%lastEq & vrrEq & pPts & flushLb & isRR)".
    iDestruct (mapsto_na_increasing_list with "pPts") as %incr.
    apply last_Some in lastEq as (ss', ->).
    iModIntro.
    iDestruct "flushLb" as "(per & Hh)".
    iDestruct "Hh" as (sRec incl) "#crashedIn".
    iDestruct (crashed_in_if_rec with "crashedIn pPts")
      as (??) "(%prefix & crashedIn2 & pPts)".
    iDestruct (crashed_in_agree with "crashedIn crashedIn2") as %<-.
    assert (sRec = (mk_numbered n v)) as ->.
    { apply (anti_symm (⊑@{numbered val})); last done.
      apply: prefix_increasing_list_snoc; try done. }
    simpl.
    iExists ℓp, ℓv, _, n.
    iSplitPure; first apply last_snoc.
    iFrame "vrrEq pPts".
    iFrame "per".
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
    iModIntro. repeat iExists _. iFrame "pPts vPts perLb". done.
  Qed.

  Lemma crash_condition_impl n v ss ℓp ℓv :
    ⌜ last ss = Some (mk_numbered n v) ⌝ -∗
    ℓp ↦_{rr_prot} ss -∗
    persist_lb ℓp rr_prot (mk_numbered n v) -∗
    ℓv ↦_{rr_prot} ss -∗
    <PC> is_recoverable_RR (#ℓp, #ℓv) v.
  Proof.
    iIntros (?) "pPts perLb vPts".
    iApply is_RR_post_crash.
    repeat iExists _.
    iSplitPure; first eassumption.
    iSplitPure; first reflexivity.
    iFrame.
  Qed.

  Lemma RR_read_spec rv (v : val) s E :
    is_RR rv v -∗
    WPC RR_read rv @ s; E {{ w, ⌜ v = w ⌝ ∗ is_RR rv v }}
                          {{ <PC> is_recoverable_RR rv v }}%I.
  Proof.
    iNamed 1.
    rewrite /RR_read.
    wpc_pures.
    { iApply (crash_condition_impl with "[//] pPts perLb vPts"). }
    iApply wpc_atomic_no_mask.
    iSplit.
    { iApply (crash_condition_impl with "[//] pPts perLb vPts"). }
    wp_apply (wp_load_na with "[$vPts]"); first eassumption.
    { iModIntro. simpl.
      iIntros (?) "#H". iFrame "H". rewrite right_id. iApply "H". }
    iIntros (?) "(vPts & <-)".
    iSplit.
    { iModIntro.
      iApply (crash_condition_impl with "[//] pPts perLb vPts"). }
    iModIntro. iSplitPure; first reflexivity.
    repeat iExists _.
    iFrame "pPts vPts perLb".
    done.
  Qed.

  Lemma RR_write_spec rv (v w : val) s E :
    is_RR rv v -∗
    WPC RR_write rv w @ s; E {{ _, is_RR rv w }} {{ True }}%I.
  Proof.
  Admitted.

  Lemma RR_recover_spec rv (v w : val) s E :
    is_recoverable_RR rv v -∗
    WPC RR_recover rv @ s; E {{ rv2, is_RR rv2 v }} {{ True }}%I.
  Proof.
  Admitted.

End spec.
