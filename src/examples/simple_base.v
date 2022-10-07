From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Import crash_weakestpre.
From self.base Require Export primitive_laws class_instances post_crash_modality.
From self.algebra Require Import view.
From self.base Require Import proofmode wpc_proofmode wpr_lifting.
From self.lang Require Import lang.

Definition assignment_prog (ℓ : loc) : expr :=
  #ℓ <-_NA #1.

Definition init_hist : history := {[ 0 := Msg #0 ∅ ∅ ∅ ]}.

Section simple_assignment.
  Context `{!nvmBaseFixedG Σ, extraStateInterp Σ, nvmBaseDeltaG}.

  Lemma wpc_assignment ℓ st E :
    {{{ validV ∅ ∗
          persisted_loc ℓ 0 ∗
          ℓ ↦h init_hist
    }}}
      assignment_prog ℓ `at` (∅, ∅, ∅) @ st; E
    {{{ v t TV, RET ThreadVal v TV;
      ℓ ↦h {[ t := Msg #1 ∅ ∅ ∅; 0 := Msg #0 ∅ ∅ ∅ ]}
    }}}
    {{{ <PC> _,
      (ℓ ↦h {[ 0 := Msg #0 ∅ ∅ ∅ ]} ∨
      (ℓ ↦h {[ 0 := Msg #1 ∅ ∅ ∅ ]}))
    }}}.
  Proof.
    iIntros (Φ Φc) "(#val & #per & pts) post".
    rewrite /assignment_prog /init_hist.
    iApply wpc_atomic_no_mask.
    iSplit.
    { crash_case.
      iDestruct (post_crash_mapsto with "pts") as "pts".
      iDestruct "per" as "-#per".
      iCrash.
      iDestruct "per" as "(per & (%CV & %t & (%look & %le) & crashed))".
      rewrite /mapsto_post_crash.
      iDestruct "pts" as (CV') "[crashed' [H | %]]";
        iDestruct (crashed_at_agree with "crashed crashed'") as %<-.
      2: { congruence. }
      iDestruct "H" as (??? histLook ?) "pts".
      apply lookup_singleton_Some in histLook as [<- <-].
      iLeft. iFrame. }
    iApply (wp_store with "[$pts $val]").
    iNext. iIntros (t) "(%hlook & %gtT & val2 & pts)".
    iSplit.
    { iModIntro. crash_case.
      iDestruct (post_crash_mapsto with "pts") as "pts".
      iDestruct "per" as "-#per".
      iCrash.
      iDestruct "per" as "(per & (%CV & % & (%look & %le) & crashed))".
      rewrite /mapsto_post_crash.
      iDestruct "pts" as (CV') "[crashed' [H | %]]";
        iDestruct (crashed_at_agree with "crashed crashed'") as %<-.
      2: { congruence. }
      iDestruct "H" as (tn ?? histLook ?) "pts".
      destruct (decide (tn = t)) as [->|neq].
      - rewrite lookup_insert in histLook.
        inversion histLook.
        simpl.
        iRight. iFrame.
      - rewrite lookup_insert_ne in histLook; last done.
        apply lookup_singleton_Some in histLook as [? <-].
        iLeft. iFrame. }
    iModIntro.
    iApply "post".
    iFrame "pts".
  Qed.

End simple_assignment.

Section simple_increment.
  Context `{!nvmBaseFixedG Σ, extraStateInterp Σ, nvmBaseDeltaG}.

  Definition pure : expr :=
    let: "a" := #1 in
    let: "b" := #7 in
    "a" + "b".

  Lemma wp_with_let TV :
    {{{ True }}} pure `at` TV {{{ RET ThreadVal (#8) TV; True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    rewrite /pure.
    wp_pures.
    iModIntro.
    by iApply "Post".
  Qed.

  Lemma wpc_with_let TV E1 :
    {{{ True }}} pure `at` TV @ E1 {{{ RET ThreadVal (#8) TV; True }}}{{{ True }}}.
  Proof.
    iIntros (Φ Φc) "_ Post".
    rewrite /pure.
    iCache with "Post".
    { iLeft in "Post". by iApply "Post". }
    wpc_pures.
    iCache with "Post".
    { iLeft in "Post". by iApply "Post". }
    wpc_pures. rewrite /thread_fill_item. simpl.
    wpc_pures.
    by iApply "Post".
  Qed.

  Definition alloc_load : expr :=
    let: "ℓ" := ref_NA #4
    in !_NA "ℓ".

  Lemma wp_load_store SV PV :
    {{{ validV SV }}} alloc_load `at` (SV, PV, ∅) {{{ TV', RET ThreadVal (#4) TV'; True }}}.
  Proof.
    iIntros (Φ) "#val Post".
    rewrite /alloc_load.
    wp_apply (wp_alloc with "val"). iIntros (ℓ ?) "(_ & _ & _ & pts)".
    wp_pures.
    wp_pures.
    iApply (wp_load with "[$pts $val]").
    iNext. iIntros (t msg) "(pts & %look & gt)".
    move: look.
    rewrite /initial_history.
    intros [<- <-]%lookup_singleton_Some.
    iApply "Post".
    done.
  Qed.

  Definition incr_both (ℓ1 ℓ2 : loc) : expr :=
    #ℓ1 <-_NA #1 ;;
    Flush #ℓ1 ;;
    Fence ;;
    #ℓ2 <-_NA #1.

  Definition incr_both_recover (ℓ1 ℓ2 : loc) : expr :=
    let: "x" := !_NA #ℓ1 in
    let: "y" := !_NA #ℓ2 in
    if: "y" ≤ "x"
    then #() #()
    else #().

  Lemma wpc_incr ℓ1 ℓ2 st E1 :
    {{{ validV ∅ ∗
        ℓ1 ↦h init_hist ∗
        ℓ2 ↦h init_hist }}}
      ThreadState (incr_both ℓ1 ℓ2) (∅, ∅, ∅) @ st; E1
    {{{ v t1 t2 TV, RET ThreadVal v TV;
      ℓ1 ↦h {[ t1 := Msg #1 ∅ ∅ ∅; 0 := Msg #0 ∅ ∅ ∅ ]} ∗
      ℓ2 ↦h {[ t2 := Msg #1 ∅ ∅ {[ ℓ1 := MaxNat t1 ]}; 0 := Msg #0 ∅ ∅ ∅ ]}
    }}}
    {{{ True }}}.
  Proof.
    iIntros (Φ Φc) "(val & ℓ1pts & ℓ2pts) Φpost".
    rewrite /incr_both.
    iDestruct (mapsto_ne with "ℓ1pts ℓ2pts") as "%ℓne".
    wpc_bind (_ <-_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit.
    { crash_case. done. }
    iApply (wp_store with "[$ℓ1pts $val]").
    iNext. iIntros (t) "(%hlook & %gtT & val & ℓ1pts)".
    iSplit.
    { iDestruct "Φpost" as "[Φpost _]". iModIntro. by iApply "Φpost". }
    iModIntro.
    iCache with "Φpost".
    { iDestruct "Φpost" as "[Φpost _]". by iApply "Φpost". }
    simpl.
    wpc_pures. rewrite /thread_fill_item. simpl.
    wpc_pures.

    (* Flush *)
    wpc_bind (Flush _)%E.
    iApply wpc_atomic_no_mask.
    iSplit. { iFromCache. }
    iApply (wp_flush with "ℓ1pts").
    iNext. iIntros "ℓ1pts".
    iSplit.
    { iDestruct "Φpost" as "[Φpost _]". iModIntro. by iApply "Φpost". }
    iModIntro.
    simpl.
    wpc_pures. rewrite /thread_fill_item. simpl.
    wpc_pures.

    (* Fence *)
    wpc_bind Fence.
    iApply wpc_atomic_no_mask.
    iSplit. { iFromCache. }
    iApply (wp_fence with "[//]").
    iIntros "!> _".
    iSplit.
    { iDestruct "Φpost" as "[Φpost _]". iModIntro. by iApply "Φpost". }
    iModIntro.
    simpl.
    wpc_pures. rewrite /thread_fill_item. simpl.
    wpc_pures.

    (* Store *)
    wpc_bind (_ <-_NA _)%E.
    iApply wpc_atomic_no_mask.
    iSplit.
    { crash_case. done. }
    iApply (wp_store with "[$ℓ2pts $val]").
    iNext. iIntros (t') "(%hlook' & %gt & val' & ℓ2pts)".
    iSplit.
    { iDestruct "Φpost" as "[Φpost _]". iModIntro. by iApply "Φpost". }
    iModIntro.

    iApply "Φpost".
    rewrite /init_hist. simpl.
    iFrame "ℓ1pts".
    simpl.
    autorewrite with view_simpl in gt.
    autorewrite with view_simpl.
    rewrite lookup_zero_singleton.
    iFrame "ℓ2pts".
  Qed.

  (* Lemma wpr_incr ℓ1 ℓ2 s E : *)
  (*   validV ∅ -∗ *)
  (*   ℓ1 ↦h init_hist -∗ *)
  (*   ℓ2 ↦h init_hist -∗ *)
  (*   wpr s E *)
  (*       (incr_both ℓ1 ℓ2 `at` (∅, ∅, ∅)) *)
  (*       (incr_both_recover ℓ1 ℓ2 `at` (∅, ∅, ∅)) (λ _, True)%I (λ _, True)%I (λ _ _, True)%I. *)
  (* Proof. *)
  (*   iIntros "#val pts1 pts2". *)
  (*   iApply (idempotence_wpr with "[pts1 pts2]"). *)
  (*   - iApply (wpc_incr with "[$val $pts1 $pts2]"). *)
  (*     iSplit. { iIntros "$". } *)
  (* Qed. *)

End simple_increment.
