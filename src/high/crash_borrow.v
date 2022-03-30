From Perennial.program_logic Require Import staged_invariant.
(* From Perennial.goose_lang Require Import crash_borrow. *)

From self.base Require Import crash_borrow.
From self.high Require Import proofmode wpc_proofmode.
From self.lang Require Import lang.
From self.high Require Import crash_weakestpre.

Section crash_borrow_high.
  Context `{nvmFixedG Σ, nvmDeltaG}.
  Context `{!stagedG Σ}.

  Program Definition crash_borrow (Ps : dProp Σ) (Pc : dProp Σ) `{!Objective Pc} : dProp Σ :=
    MonPred (λ TV,
              (□ (Ps -∗ Pc)) TV ∗
              (* □ (∀ TV', TV ⊑ TV') ∗ *)
              crash_borrow (Ps TV) (Pc ⊥)
            )%I _.
  Next Obligation.
    intros Ps Pc ?. intros TV1 TV2 incl.
    rewrite 2!monPred_at_intuitionistically.
    iIntros "[#impl cb]".
    iSplitR. { naive_solver. }
    iApply (crash_borrow_conseq with "[] [] [] cb").
    - iIntros "!> H".
      iSpecialize ("impl" with "H").
      by iApply objective_at.
    - naive_solver.
    - naive_solver.
  Qed.

  (*
  (* Kripke-style crash borrow. Will it work? Who knows ¯\_(ツ)_/¯. *)
  Program Definition crash_borrow (Ps : dProp Σ) (Pc : dProp Σ) `{!Objective Pc} : dProp Σ :=
    MonPred (λ TV, ∀ TV', ⌜ TV ⊑ TV' ⌝ -∗
              crash_borrow (Ps TV') (Pc ⊥)
            )%I _.
  Next Obligation.
    intros Ps Pc ?. intros TV1 TV2 incl. iIntros "cb" (TV' incl').
    iApply "cb".
    iPureIntro. etrans; done.
  Qed.
  *)

  Lemma crash_borrow_crash_wand P Pc `{!Objective Pc}:
    crash_borrow P Pc -∗ □ (P -∗ Pc).
  Proof.
    iStartProof (iProp _). iIntros (?).
    iDestruct 1 as "(H & _)". iApply "H".
  Qed.

  Lemma wpc_crash_borrow_inits s (e : expr) (Φ : _ → dProp Σ) Φc (P : dProp Σ)
        Pc `{!Objective Pc} :
    ⎡ pre_borrow ⎤ -∗
    P -∗
    □ (P -∗ Pc) -∗
    (crash_borrow P Pc -∗ WPC e @ s; ⊤ {{ Φ }} {{ Pc -∗ Φc }}) -∗
    WPC e @ s; ⊤ {{ Φ }} {{ Φc }}.
  Proof.
    iStartProof (iProp _). iIntros (?).
    monPred_simpl. iIntros "H" (? ?) "P".
    monPred_simpl. iIntros (? ?) "#wand".
    monPred_simpl. iIntros (? ?).
    monPred_simpl.
    iIntros "wpc".
    rewrite wpc_eq /wpc_def. simpl.
    iIntros (? ?) "#val".
    iApply (wpc_crash_borrow_inits with "H [P]"); last first.
    { iIntros "cb".
      iSpecialize ("wpc" $! j1 with "[] [$cb]").
      { done. }
      { iModIntro. monPred_simpl. iIntros (? ?). iApply "wand".
        iPureIntro. etrans; done. }
      iSpecialize ("wpc" $! TV with "[//] [$]").
      iApply (program_logic.crash_weakestpre.wpc_mono with "wpc").
      { naive_solver. }
      { iDestruct 1 as "H". monPred_simpl. iApply "H". done. }
    }
    { iIntros "!> P". iApply objective_at. iApply ("wand" with "[//] P"). }
    { iApply (monPred_mono with "P"). etrans; done. }
  Qed.

  Lemma wpc_crash_borrow_open_modify E1 e Φ Φc P Pc `{!Objective Φc, !Objective Pc} :
    to_val e = None →
    crash_borrow P Pc -∗
    (Φc ∧
      (P -∗ WPC e @ E1
                  {{λ v, ∃ P', P' ∗ □ (P' -∗ Pc) ∗ (crash_borrow P' Pc -∗ (Φc ∧ Φ v))}}
                  {{ Φc ∗ Pc }})) -∗
    WPC e @ E1 {{ Φ }} {{ Φc }}.
  Proof.
    iStartProof (iProp _). iIntros (Hnv).
    iIntros (?) "cb".
    monPred_simpl. iIntros (? ?) "wp".
    rewrite wpc_eq /wpc_def. simpl.
    iIntros (??) "#val".
    iApply (wpc_crash_borrow_open_modify with "[cb]").
    { simpl. rewrite /thread_to_val. rewrite Hnv. done. }
    { iDestruct "cb" as "[_ $]". }
    iSplit.
    { iApply objective_at. iDestruct "wp" as "[$ _]". }
    iIntros "P".
    iDestruct "wp" as "[_ wp]".
    monPred_simpl.
    iSpecialize ("wp" with "[%] [P] [] val").
    { reflexivity. }
    { iFrame "P". }
    { done. }
    monPred_simpl.
    iApply (program_logic.crash_weakestpre.wpc_mono with "wp"); last done.
    iIntros ([v vTV]) "(% & Hi & (%P' & ? & #impl & H))".
    iExists (P' vTV).
    iFrame.
    iSplitL "impl".
    { iIntros "!> P'".
      iApply objective_at.
      iApply "impl"; done. }
    iIntros "Hip".
    iEval (monPred_simpl) in "H".
    iSpecialize ("H" $! vTV with "[//] [Hip]").
    { simpl. iFrame.
      rewrite monPred_at_intuitionistically. iModIntro. iApply "impl". }
    iSplit.
    - iApply objective_at. iDestruct "H" as "[$ _]".
    - iDestruct "H" as "[_ $]". done.
  Qed.

  Lemma wpc_crash_borrow_open E1 e Φ Φc P Pc `{!Objective Φc, !Objective Pc} :
    to_val e = None →
    crash_borrow P Pc -∗
    (Φc ∧ (P -∗ WPC e @ E1
                      {{λ v, P ∗ (crash_borrow P Pc -∗ (Φc ∧ Φ v))}}
                      {{ Φc ∗ Pc }})) -∗
    WPC e @ E1 {{ Φ }} {{ Φc }}.
  Proof.
    iIntros (Hnv) "H1 Hwp".
    iDestruct (crash_borrow_crash_wand with "[$]") as "#Hw".
    iApply (wpc_crash_borrow_open_modify with "[$] [Hwp]"); auto.
    iSplit; first by iDestruct "Hwp" as "($&_)".
    iIntros "HP".
    iDestruct "Hwp" as "(_&Hwp)".
    iSpecialize ("Hwp" with "[$]").
    iApply (wpc_strong_mono with "Hwp"); auto.
    { iSplit; last first.
      { iIntros "[$ $]". eauto. }
      iIntros (?) "(HP&H)". iModIntro.
      iExists P. iFrame. eauto. }
  Qed.

End crash_borrow_high.
