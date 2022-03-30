From iris.proofmode Require Import tactics.
From Perennial.program_logic Require Import crash_weakestpre.
From self.base Require Export primitive_laws class_instances.
From self.algebra Require Import view.
From self.base Require Import proofmode wpc_proofmode.
From self.lang Require Import lang.

Section simple_increment.
  Context `{!nvmBaseFixedG Σ, extraStateInterp Σ, nvmBaseDeltaG}.

  Definition pure : expr :=
    let: "a" := #1 in
    let: "b" := #7 in
    "a" + "b".

  Lemma wp_with_let TV :
    {{{ True }}} ThreadState pure TV {{{ RET ThreadVal (#8) TV; True }}}.
  Proof.
    iIntros (Φ) "_ Post".
    rewrite /pure.
    wp_pures.
    iModIntro.
    by iApply "Post".
  Qed.

  Lemma wpc_with_let TV E1 :
    {{{ True }}} ThreadState pure TV @ E1 {{{ RET ThreadVal (#8) TV; True }}}{{{ True }}}.
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
    {{{ validV SV }}} ThreadState alloc_load (SV, PV, ∅) {{{ TV', RET ThreadVal (#4) TV'; True }}}.
  Proof.
    iIntros (Φ) "#val Post".
    rewrite /alloc_load.
    wp_apply (wp_alloc with "[$]"). iIntros (ℓ ?) "(_ & _ & _ & pts)".
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

  Definition incr_both_recover ℓ1 ℓ2 : expr :=
    let: "x" := !_NA ℓ1 in
    let: "y" := !_NA ℓ2 in
    if: "y" ≤ "x"
    then #() #()
    else #().

  Definition init_hist : history := {[ 0 := Msg #0 ∅ ∅ ∅ ]}.

  Lemma wpc_incr ℓ1 ℓ2 k E1 :
    {{{ validV ∅ ∗
        ℓ1 ↦h init_hist ∗
        ℓ2 ↦h init_hist }}}
      ThreadState (incr_both ℓ1 ℓ2) (∅, ∅, ∅) @ k; E1
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
  
End simple_increment.
