(* This in an implementation of a durable variant of the fine-grained concurrent
Michael-Scott queue. *)

From iris.bi Require Import lib.fractional.
From iris.proofmode Require Import tactics.
From iris.bi.lib Require Export fixpoint.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Import notation lang.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances.
From self.high Require Import proofmode wpc_proofmode if_rec.
From self.high Require Import dprop abstract_state_instances modalities
     resources crash_weakestpre weakestpre weakestpre_na weakestpre_at
     recovery_weakestpre lifted_modalities protocol protocols no_buffer mapsto_na_flushed.
From self.high.modalities Require Import fence.

(* Implementation. *)

Section implementation.

  Notation NONE := (InjL #()).

  Definition MS_nilv := NONEV.
  Definition MS_consv x nOut : val := SOMEV ((SOMEV x), nOut).

  Definition MS_nil := NONE.
  Definition MS_cons x nOut := SOME ((SOME x), nOut).

  Definition getValue : val :=
    λ: "x", match: "x" with
              NONE => assert #false (* rec: "spin" <> := "spin" #() *)
            | SOME "v" => "v"
            end.

  Definition mk_MS_queue : expr :=
    λ: <>,
      let: "nilNode" := ref_AT NONE in
      Flush "nilNode" ;;
      Fence ;;
      let: "toNil" := ref_AT "nilNode" in
      Flush "toNil" ;;
      Fence ;;
      let: "node" := ref_AT (SOME (NONE, "toNil")) in
      Flush "node" ;;
      Fence ;;
      let: "toSent" := ref_AT "node" in
      let: "toTail" := ref_AT "node" in
      Flush "toSent" ;;
      Flush "toTail" ;;
      Fence ;;
      ("toSent", "toTail").

  Definition MS_dequeue : expr :=
    rec: "try" "queue" :=
      let: "toSent" := Fst "queue" in
      let: "sent" := !_AT "toSent" in
      let: "cont" := getValue (!_AT "sent") in
      match: !_AT (!_AT (Snd "cont")) with
        NONE => NONE
      | SOME "n'" =>
          Fence ;;
          if: (CAS "toSent" "sent" (!_AT (Snd "cont")))
          then SOME (getValue (Fst ("n'")))
          else "try" "queue"
      end.

  Definition MS_enqueue : val :=
    λ: "queue" "x",
      let: "toTail" := Snd "queue" in
      let: "nilNode" := ref_AT MS_nil in
      Flush "nilNode" ;;
      Fence ;;
      let: "toNil" := ref_AT "nilNode" in
      Flush "toNil" ;;
      Fence ;;
      let: "node" := ref_AT (MS_cons "x" "toNil") in
      let: "tail" := !_AT "toTail" in
      (rec: "try" "c" :=
        let: "t" := !_AT  "c" in
        match: !_AT  "t" with
          NONE =>
            (* The tail is nil, we can try to insert *)
            if: (CAS "c" "t" "node")
            then (* Insertion succeeded, update to tail pointer *)
              CAS "toTail" "tail" "node" ;; #()
            else (* Insertion failed, we try again*)
              "try" "c"
        | SOME "c'" => "try" (Snd "c'")
        end
      ) (Snd (getValue !_AT "tail")).

End implementation.

Section definitions.
  Implicit Types (ℓ : loc).
  Context `{nvmG Σ}.

  (* We assume a per-element predicate. *)
  Context (R : val → dProp Σ).

  (* The per-element predicate must be stable under the <PCF> modality and not
  use anything from the buffer. *)
  Context `{∀ a, IntoCrashFlush (R a) (R a),
            ∀ a, BufferFree (R a)}.

  (* A nil node is never mutated so we use a constant protocol to represent
  it. *)
  Definition nil_node_prot := constant_prot (InjLV #()).

  Definition loc_predO `{nvmG Σ} ST := ST -d> val -d> dPropO Σ.

  (* Left injection means pointer to a nil node, and right means pointer to a
  cons node. Due to the use of [discreteState] the location can only be updated
  a single time. *)
  Definition toNext_state : Type := discreteState loc + discreteState loc.

  Lemma toNext_state_inr ℓnext (s : toNext_state) :
    inr {| get_discrete := ℓnext |} ⊑ s →
    s = inr {| get_discrete := ℓnext |}.
  Proof. destruct s; inversion 1. done. Qed.

  (* The invariant for the location out of a node. *)
  Definition toNext_prot_inv (next_inv : loc_predO bool) :
      loc_predO toNext_state :=
    λ ml v,
      match ml with
        inl (mk_discrete ℓ) =>
          ⌜ v = #(ℓ : loc) ⌝ ∗
          ℓ ↦_AT^{nil_node_prot} [()] ∗
          flush_lb ℓ (nil_node_prot) ()
      | inr (mk_discrete ℓ) =>
          ⌜ v = #ℓ ⌝ ∗
          ℓ ↦_AT^{MkProt next_inv id} [true] ∗
          flush_lb ℓ (MkProt next_inv id) true
      end%I.

  Global Instance toNext_prot_inv_ne :
    NonExpansive toNext_prot_inv.
  Proof.
    rewrite /toNext_prot_inv.
    intros ???? [|[ℓ]] ?; first solve_proper.
    f_equiv.
    f_equiv.
    - rewrite /mapsto_at.
      f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
      f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
      f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
      rewrite /know_protocol.
      f_equiv; last done.
      simpl.
      f_equiv.
      rewrite /know_pred_d.
      f_equiv.
      intros ?? ->.
      f_equiv.
      assumption.
    - rewrite /flush_lb.
      f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
      rewrite /lb_base.
      f_equiv.
      rewrite /know_protocol.
      f_equiv.
      f_equiv; last done.
      f_equiv.
      rewrite /know_pred_d.
      f_equiv.
      intros ?? ->.
      f_equiv.
      simpl.
      assumption.
  Qed.

  Definition toNext_prot (next_inv : loc_pred bool) :=
    MkProt (toNext_prot_inv next_inv) id.

  (* The invariant for the location into a node. *)
  Definition pre_node_prot_inv :
     (loc_predO bool) -d> loc_predO bool :=
    λ self b v,
      (∃ (ℓtoNext : loc) mx state,
        ⌜ v = (InjRV (mx, #ℓtoNext)) ⌝ ∗
        match b with
          (* Is initial sentinel. *)
          false => True
          (* Is not a sentinel node. *)
        | true => ∃ x, ⌜ mx = SOMEV x ⌝ ∗ R x
        end ∗
        ℓtoNext ↦_AT^{toNext_prot self} [state] ∗
        flush_lb ℓtoNext (toNext_prot self) state)%I.

  Global Instance pre_node_prot_inv_contractive :
    Contractive pre_node_prot_inv.
  Proof.
    intros ??????.
    rewrite /pre_node_prot_inv.
    simpl.
    f_equiv.
    f_equiv.
    f_equiv.
    f_equiv.
    f_equiv.
    f_equiv.
    f_equiv.
    f_equiv.
    f_equiv.
    - rewrite /mapsto_at.
      f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
      f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
      f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
      rewrite /know_protocol.
      f_equiv; last done.
      simpl.
      f_equiv.
      rewrite /know_pred_d.
      f_equiv.
      intros ?? ->.
      f_contractive.
      f_equiv.
      assumption.
    - rewrite /flush_lb.
      f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
      rewrite /lb_base.
      f_equiv.
      rewrite /know_protocol.
      f_equiv.
      f_equiv; last done.
      f_equiv.
      rewrite /know_pred_d.
      f_equiv.
      intros ?? ->.
      f_contractive.
      simpl.
      f_equiv.
      assumption.
  Qed.

  Definition node_prot_inv := fixpoint pre_node_prot_inv.

  Lemma node_prot_inv_unfold :
    node_prot_inv ≡ pre_node_prot_inv (node_prot_inv).
  Proof. rewrite /node_prot_inv. apply fixpoint_unfold. Qed.

  Instance if_else_persistent {PROP : bi} (b : bool) (P Q : PROP) :
    Persistent P →
    Persistent Q →
    Persistent (if b then P else Q).
  Proof. intros ??. destruct b; done. Qed.

  Global Instance node_prot_inv_persistent `{∀ v, Persistent (R v)} s v :
    Persistent (node_prot_inv s v).
  Proof.
    rewrite /Persistent.
    (* iLöb as "IH" forall (ℓtoNext s v). *)
    rewrite /node_prot_inv.
    rewrite (fixpoint_unfold (pre_node_prot_inv) s v).
    iDestruct 1 as (???) "(-> & #HR & #prot & #lb)".
    iModIntro.
    repeat iExists _.
    iSplitPure; first done.
    iFrame "#".
  Qed.

  Global Instance toNext_prot_inv_persistent s v :
    Persistent (toNext_prot_inv (node_prot_inv) s v).
  Proof. destruct s as [[?]|[?]]; apply _. Qed.

  Definition cons_node_prot : LocationProtocol bool :=
    {| p_inv := node_prot_inv;
       p_bumper := id |}.

  Global Instance cons_node_prot_conditions :
    ProtocolConditions cons_node_prot.
  Proof.
    split; try apply _.
    - intros ??. simpl.
      rewrite /node_prot_inv (fixpoint_unfold (pre_node_prot_inv) s v).
      apply _.
    - iLöb as "IH".
      iIntros (??) "nodeProt".
      simpl.
      rewrite /node_prot_inv.
      rewrite (fixpoint_unfold (pre_node_prot_inv) s v).
      iDestruct "nodeProt" as (???) "(-> & HR & prot & lb)".
      iModIntro.
      simpl.
      iDestruct "lb" as "(persLb & (%state' & #incl & #crashedIn))".
      iExists _, mx, state'.
      iSplitPure; first done.
      iFrameF "HR".
      iDestruct (crashed_in_if_rec with "crashedIn prot")
        as (?) "(crashedIn2 & toNextPts)".
      iDestruct (crashed_in_agree with "crashedIn crashedIn2") as %<-.
      iFrame "toNextPts".
      iApply persist_lb_to_flush_lb.
      iApply (crashed_in_persist_lb with "crashedIn").
  Qed.

  Global Instance toNext_prot_conditions :
    ProtocolConditions (toNext_prot node_prot_inv).
  Proof.
    split; try apply _.
    - intros [[?]|[?]] ?; apply _.
    - iIntros ([[?]|[?]] ?) "(-> & B & C) /=";
          iCrashIntro.
      * iSplitPure; first done.
        iDestruct "C" as "[? (% & le & #crashedIn)]".
        iDestruct (crashed_in_if_rec with "crashedIn B") as ([]) "[crashedIn2 pts]".
        iFrame "pts".
        iApply persist_lb_to_flush_lb.
        iFrame.
      * iSplitPure; first done.
        iDestruct "C" as "[? (% & %le & #crashedIn)]".
        inversion le.
        iDestruct (crashed_in_if_rec with "crashedIn B") as (b) "[crashedIn2 pts]".
        iDestruct (crashed_in_agree with "crashedIn crashedIn2") as %<-.
        iFrame "pts".
        iApply persist_lb_to_flush_lb.
        iFrame.
  Qed.

  Definition toSent_prot :=
    {| p_inv := λ (_ : unit) v, (∃ (ℓsent : loc) sb,
        ⌜ v = #ℓsent ⌝ ∗
        ℓsent ↦_AT^{cons_node_prot} [sb] ∗
        flush_lb ℓsent (cons_node_prot) sb)%I;
       p_bumper v := v |}.

  Global Instance toSent_prot_conditions :
    ProtocolConditions toSent_prot.
  Proof.
    split; try apply _.
    iIntros (??).
    iDestruct 1 as (??) "(A & B & C)".
    iModIntro.
    iDestruct "C" as "(HI & (% & % & #crashedIn1))".
    iDestruct (crashed_in_if_rec with "crashedIn1 B") as (?) "(crashedIn2 & sentPts)".
    iDestruct (crashed_in_agree with "crashedIn1 crashedIn2") as %<-.
    iExists _, s__pc.
    iFrameF "A".
    simpl.
    iFrameF "sentPts".
    iApply persist_lb_to_flush_lb.
    iApply (crashed_in_persist_lb with "crashedIn1").
  Qed.

  (* The tail pointer might point to the sentinel, so in general what it points
  to satisfies the exact same invariant as the sentinel pointer. *)
  Definition toTail_prot := toSent_prot.

  (* The representation predicate for the MS queue. *)
  Definition is_queue (queue : val) : dProp Σ :=
    ∃ (ℓtoS ℓtoT : loc),
      ⌜ queue = (#ℓtoS, #ℓtoT)%V ⌝ ∗
      (* ℓtoS *)
      ℓtoS ↦_AT^{toSent_prot} [()] ∗
      flush_lb ℓtoS toSent_prot () ∗
      (* ℓtoT *)
      ℓtoT ↦_AT^{toTail_prot} [()] ∗
      flush_lb ℓtoS toSent_prot ().

End definitions.

Section specification.
  Context `{nvmG Σ}.

  (* We assume a per-element predicate. *)
  Context (R : val → dProp Σ).

  (* The per-element predicate must be stable under the <PCF> modality and not
{ use anything from the buffer. *)
  Context `{∀ a, IntoCrashFlush (R a) (R a),
           ∀ a, BufferFree (R a),
           ∀ a, Persistent (R a)}.

  Lemma wp_mk_queue s E :
    {{{ True }}}
      mk_MS_queue #() @ s ; E
    {{{ qv, RET qv; is_queue R qv }}}.
  Proof.
    iIntros (Φ) "_ Φpost".
    rewrite /mk_MS_queue.
    wp_pures.

    (* Allocate nil node. *)
    wp_apply (wp_alloc_at _ () nil_node_prot); first done.
    iIntros (ℓnil) "#nilPts".
    wp_pures.
    wp_apply (wp_flush_at _ _ [] with "nilPts"). simpl.
    iIntros "(_ & #nilFlushLb & _)".
    wp_pures.
    wp_apply wp_fence.
    do 2 iModIntro.
    wp_pures.

    (* Allocate next pointer to nil node. *)
    wp_apply (wp_alloc_at _ (inl (mk_discrete ℓnil))
                (toNext_prot (node_prot_inv R))).
    { iSplitPure; first done.
      iFrame "nilPts nilFlushLb". }
    iIntros (ℓtoNext) "#toNextPts".
    wp_pures.
    wp_apply (wp_flush_at _ _ [] with "toNextPts"). simpl.
    iIntros "(_ & #toNextFlushLb & _)".
    wp_pures.
    wp_apply wp_fence.
    do 2 iModIntro.
    wp_pures.

    wp_apply (wp_alloc_at _ false (cons_node_prot R)).
    { rewrite /= (node_prot_inv_unfold _ _ _).
      repeat iExists _.
      iSplitPure; first done.
      rewrite left_id.
      iFrame "toNextPts".
      iFrame "toNextFlushLb". }
    iIntros (ℓsent) "#sentPts".
    wp_pures.
    wp_apply (wp_flush_at _ _ [] with "sentPts"). simpl.
    iIntros "(_ & #sentFlushLb & _)".
    wp_pures.
    wp_apply wp_fence.
    do 2 iModIntro.
    wp_pures.

    wp_apply (wp_alloc_at _ () (toSent_prot R)).
    { repeat iExists _. iFrame "#". done. }
    iIntros (ℓtoS) "#toSPts".
    wp_pures.
    wp_apply (wp_alloc_at _ () (toTail_prot R)).
    { repeat iExists _. iFrame "#". done. }
    iIntros (ℓtoT) "#toTPts".
    wp_pures.

    wp_apply (wp_flush_at _ _ [] with "toSPts").
    iIntros "(_ & #toSFlushLb & _)".
    wp_pures.
    wp_apply (wp_flush_at _ _ [] with "toTPts").
    iIntros "(_ & #toTFlushLb & _)".
    wp_pures.
    wp_apply wp_fence.
    do 2 iModIntro.
    wp_pures.
    iModIntro.
    iApply "Φpost".
    repeat iExists _.
    iSplitPure; first done.
    iFrame "toSPts toTPts #".
  Qed.

  Lemma wp_dequeue queue s E :
    {{{ is_queue R queue }}}
      MS_dequeue queue @ s ; E
    {{{ v, RET v;
      (⌜ v = NONEV ⌝) ∨ (∃ x, ⌜ v = InjRV x ⌝ ∗ R x) }}}.
  Proof.
    iIntros (Φ) "(%ℓtoS & %_ & -> & toSPts & _) Φpost".
    rewrite /MS_dequeue.
    wp_pure1.
    iLöb as "IH".
    (* iClear "IH". (* For now to reduce clutter. *) *)
    wp_pures.

    (* Load of sentinel pointer. *)
    wp_apply (wp_load_at_simple_pers with "toSPts").
    iIntros ([] v) "(_ & #toSPts & inv)".
    iDestruct "inv" as (ℓsent sb) "(>-> & >sentPts & sentFlushLb)".
    wp_pures.

    (* Load of the pointer into the sentinel's content. *)
    wp_apply (wp_load_at_simple_pers with "sentPts").
    iIntros (?sb ?v) "(_ & sentPts & nodeInv)".
    simpl. rewrite (node_prot_inv_unfold _ _ _).
    iDestruct "nodeInv" as (??? ->) "(_ & >toNextPts & nodeInv)".

    rewrite {6}/getValue.
    wp_pures.

    (* Load the pointer out of the sentinel. *)
    wp_apply (wp_load_at_simple_pers with "toNextPts").
    iIntros (??) "(_ & toNextPts & toNextInv)".
    rewrite /= /toNext_prot_inv.

    destruct sL as [[ℓnext] | [ℓnext]].
    - (* nil node *)
      iDestruct "toNextInv" as "(>-> & >nextPts & flushLb)".
      wp_apply (wp_load_at_simple_pers with "nextPts").
      iIntros ([] ?) "(? & nextPts & ><-) /=".
      wp_pures.
      iModIntro.
      iApply "Φpost".
      iLeft. done.
    - (* cons node *)
      iDestruct "toNextInv" as "(>-> & >nextPts & flushLb)".

      wp_apply (wp_load_at_simple_pers with "nextPts").
      iIntros (??) "(%le & nextPts & nextInv) /=".
      inversion le.
      rewrite (node_prot_inv_unfold R _ _).
      rewrite /pre_node_prot_inv.
      iDestruct "nextInv" as (? mx' ?) "(>-> & HR & >toNextPts' & ?)".

      wp_pures.
      wp_apply wp_fence.
      do 2 iModIntro.
      wp_pures.

      wp_apply (wp_load_at_simple_pers with "toNextPts").
      iIntros (sL2 ?) "(%le2 & toNextPts & toNextInv)".
      apply toNext_state_inr in le2 as ->.
      iDestruct "toNextInv" as "(>-> & notneeded)".

      wp_apply
        (wp_cas_at (λ _, True)%I (λ _, True)%I True _ (toSent_prot R) []
                          _ _ _ (λ _, True)%I with "[-HR Φpost]").
      { iFrameF "toSPts".
        iIntros ([] ? ?).
        rewrite 3!right_id.
        iSplitL "".
        { iIntros "_". iLeft. done. }
        iSplit; last first.
        { iModIntro. iIntros "$". }
        iSplitPure; first done.
        iSplitL ""; first naive_solver.
        iSplitL "". { iModIntro. iIntros "$". }
        iIntros "_".
        repeat iExists _.
        iSplitPure; first done.
        iFrameF "nextPts".
        iFrame "flushLb". }
      iIntros (? []) "[(-> & H)|(-> & H)]".
      * wp_pures.
        iDestruct "HR" as (? ->) "R".
        rewrite /getValue.
        wp_pures.
        iModIntro.
        iApply "Φpost".
        iRight.
        iExists _. iFrame "R". done.
      * wp_pure1.
        iApply ("IH" with "toSPts").
        iApply "Φpost".
  Qed.

  Lemma wpc_enqueue queue x s E :
    {{{ is_queue R queue ∗ R x }}}
      MS_enqueue queue x @ s ; E
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "[(%_ & %ℓtoT & -> & _ & _ & toTPts & lb) HR] Φpost".
    rewrite /MS_enqueue.
    wp_pures.

    (* Allocate nil node. *)
    wp_apply (wp_alloc_at _ () nil_node_prot); first done.
    iIntros (ℓnil) "#nilPts".
    wp_pures.
    wp_apply (wp_flush_at _ _ [] with "nilPts"). simpl.
    iIntros "(_ & #nilFlushLb & _)".
    wp_pures.
    wp_apply wp_fence.
    do 2 iModIntro.
    wp_pures.

    (* Allocate next pointer to nil node. *)
    wp_apply (wp_alloc_at _ (inl (mk_discrete ℓnil))
                (toNext_prot (node_prot_inv R))).
    { iSplitPure; first done.
      iFrame "nilPts nilFlushLb". }
    iIntros (ℓtoNext) "#toNextPts".
    wp_pures.
    wp_apply (wp_flush_at _ _ [] with "toNextPts"). simpl.
    iIntros "(_ & #toNextFlushLb & _)".
    wp_pures.
    wp_apply wp_fence.
    do 2 iModIntro.
    wp_pures.

    wp_apply (wp_alloc_at _ true (cons_node_prot R) with "[HR]").
    { rewrite /= (node_prot_inv_unfold _ _ _).
      repeat iExists _.
      iSplitPure; first done.
      iSplitL "HR". { iExists x. iFrame "HR". done. }
      iFrame "toNextPts".
      iFrame "toNextFlushLb". }
    iIntros (ℓnode) "#nodePts".
    wp_pures.

    wp_apply (wp_load_at_simple_pers with "toTPts").
    iIntros ([] v) "(_ & #toTPts & inv)".
    iDestruct "inv" as (ℓtail sb) "(>-> & >tailPts & tailFlushLb)".
    wp_pures.

    wp_apply (wp_load_at_simple_pers with "tailPts").
    iIntros (? ?) "(le & tailPts & inv)".
    rewrite /= (node_prot_inv_unfold R _ _).
    iDestruct "inv" as (ℓnext ??) "(>-> & _ & >nextPts & nextFlushLb)".
    rewrite /getValue.
    do 6 wp_pure1.

    iLöb as "IH".
    iClear "IH".

    wp_pures.

    wp_apply (wp_load_at_simple_pers with "nextPts").
    iIntros (nextS ?) "(%le & nextPts & nextInv) /=".
    wp_pures.

    destruct nextS as [[ℓnil2] | [ℓnext2]].
    - (* nil node *)
      simpl.
      iDestruct "nextInv" as "(>-> & >nil2pts & HR)".

      wp_apply (wp_load_at_simple_pers with "nil2pts").
      iIntros ([] ?) "(? & ? & ><-) /=".
      wp_pures.

      wp_apply
        (wp_cas_at (λ _, True)%I (λ _, True)%I True _ _ []
                          _ _ _ (λ _, True)%I with "[-HR Φpost]").
      { iFrameF "nextPts".
        iIntros (?? incl).
        iSplitL "".
        { iIntros "_". iLeft. done. }
        rewrite !right_id.
        iSplit; last first.
        { iModIntro. iIntros "$". }
        iSplitPure; first done.
        iSplitL ""; last naive_solver.
        {
      }

  Qed.

End specification.
