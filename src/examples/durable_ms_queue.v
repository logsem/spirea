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
      let: "toNil" := ref_AT "nilNode" in
      let: "node" := ref_AT (SOME (NONE, "toNil")) in
      Flush "nilNode" ;;
      Flush "toNil" ;;
      Flush "node" ;;
      Fence ;;
      let: "toTail" := ref_AT "node" in
      let: "toSent" := ref_AT "node" in
      ("toSent", "toTail").

  Definition MS_dequeue : expr :=
    rec: "try" "queue" :=
      let: "toSent" := Fst "queue" in
      let: "sent" := !_AT "toSent" in
      Fence ;; (* NOTE: Investigate whether this fence is strictly neccessary. *)
      let: "c" := getValue (!_AT "sent") in
      Fence ;; (* NOTE: Investigate whether this fence is strictly neccessary. *)
      match: !_AT (!_AT (Snd "c")) with
        NONE => NONE
      | SOME "n'" =>
          Fence ;;
          if: (CAS "toSent" "sent" (!_AT (Snd "c")))
          then SOME (getValue (Fst ("n'")))
          else "try" #()
      end.

  Definition MS_enqueue : val :=
    λ: "queue" "x",
      let: "toTail" := Snd "queue" in
      let: "n" := ref_AT (MS_cons "x" (ref_AT (ref_AT MS_nil))) in
      let: "tail" := !_AT "toTail" in
      (rec: "try" "c" :=
        let: "t" := !_AT  "c" in
        match: !_AT  "t" with
          NONE =>
            (* The tail is nil, we can try to insert *)
            if: (CAS "c" "t" "n")
            then (* Insertion succeeded, update tail *)
              CAS "toTail" "tail" "n" ;; #()
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
  Definition pre_node_prot_inv (ℓtoNext : loc) :
     (loc_predO bool) -d> loc_predO bool :=
    λ self b v,
      (∃ mx state,
        ⌜ v = (InjRV (mx, #ℓtoNext)) ⌝ ∗
        match b with
          (* Is initial sentinel. *)
          false => True
          (* Is not a sentinel node. *)
        | true => ∃ x, ⌜ mx = SOMEV x ⌝ ∗ R x
        end ∗
        ℓtoNext ↦_AT^{toNext_prot self} [state] ∗
        flush_lb ℓtoNext (toNext_prot self) state)%I.

  Global Instance pre_node_prot_inv_contractive ℓtoNext :
    Contractive (pre_node_prot_inv ℓtoNext).
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

  Definition node_prot_inv ℓtoNext := fixpoint (pre_node_prot_inv ℓtoNext).

  Lemma node_prot_inv_unfold ℓtoNext :
    node_prot_inv ℓtoNext ≡ pre_node_prot_inv ℓtoNext (node_prot_inv ℓtoNext).
  Proof. rewrite /node_prot_inv. apply fixpoint_unfold. Qed.

  Instance if_else_persistent {PROP : bi} (b : bool) (P Q : PROP) :
    Persistent P →
    Persistent Q →
    Persistent (if b then P else Q).
  Proof. intros ??. destruct b; done. Qed.

  Lemma node_prot_inv_persistent `{∀ v, Persistent (R v)} ℓtoNext s v : Persistent (node_prot_inv ℓtoNext s v).
  Proof.
    rewrite /Persistent.
    (* iLöb as "IH" forall (ℓtoNext s v). *)
    rewrite /node_prot_inv.
    rewrite (fixpoint_unfold (pre_node_prot_inv ℓtoNext) s v).
    iDestruct 1 as (??) "(-> & #HR & #prot & #lb)".
    iModIntro.
    iExists _, _.
    iSplitPure; first done.
    iFrame "#".
  Qed.

  Global Instance toNext_prot_inv_persistent ℓtoNext s v :
    Persistent (toNext_prot_inv (node_prot_inv ℓtoNext) s v).
  Proof. destruct s as [[?]|[?]]; apply _. Qed.

  Definition cons_node_prot (ℓtoNext : loc) : LocationProtocol bool :=
    {| p_inv := (node_prot_inv ℓtoNext);
       p_bumper := id |}.

  Global Instance cons_node_prot_conditions (ℓtoNext : loc) :
    ProtocolConditions (cons_node_prot ℓtoNext).
  Proof.
    split; try apply _.
    - intros ??. simpl.
      rewrite /node_prot_inv (fixpoint_unfold (pre_node_prot_inv _) s v).
      apply _.
    - iLöb as "IH".
      iIntros (??) "nodeProt".
      simpl.
      rewrite /node_prot_inv.
      rewrite (fixpoint_unfold (pre_node_prot_inv ℓtoNext) s v).
      iDestruct "nodeProt" as (??) "(-> & HR & prot & lb)".
      iModIntro.
      simpl.
      iDestruct "lb" as "(persLb & (%state' & #incl & #crashedIn))".
      iExists mx, state'.
      iSplitPure; first done.
      iFrameF "HR".
      iDestruct (crashed_in_if_rec with "crashedIn prot")
        as (?) "(crashedIn2 & toNextPts)".
      iDestruct (crashed_in_agree with "crashedIn crashedIn2") as %<-.
      iFrame "toNextPts".
      iApply persist_lb_to_flush_lb.
      iApply (crashed_in_persist_lb with "crashedIn").
  Qed.

  Definition toSent_prot :=
    {| p_inv := λ (_ : unit) v, (∃ (ℓsent ℓtoNext : loc) sb,
        ⌜ v = #ℓsent ⌝ ∗
        ℓsent ↦_AT^{cons_node_prot ℓtoNext} [sb] ∗
        flush_lb ℓsent (cons_node_prot ℓtoNext) sb)%I;
       p_bumper v := v |}.

  Global Instance toSent_prot_conditions :
    ProtocolConditions toSent_prot.
  Proof.
    split; try apply _.
    iIntros (??).
    iDestruct 1 as (???) "(A & B & C)".
    iModIntro.
    iDestruct "C" as "(HI & (% & % & #crashedIn1))".
    iDestruct (crashed_in_if_rec with "crashedIn1 B") as (?) "(crashedIn2 & sentPts)".
    iDestruct (crashed_in_agree with "crashedIn1 crashedIn2") as %<-.
    iExists _, _, s__pc.
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
  use anything from the buffer. *)
  Context `{∀ a, IntoCrashFlush (R a) (R a),
           ∀ a, BufferFree (R a),
           ∀ a, Persistent (R a)}.

  Lemma wpc_dequeue queue s E :
    {{{ is_queue R queue }}}
      MS_dequeue queue @ s ; E
    {{{ v, RET v;
      (⌜ v = NONEV ⌝) ∨ (∃ x, ⌜ v = InjRV x ⌝ ∗ R x) }}}.
  Proof.
    iIntros (Φ) "(%ℓtoS & %_ & -> & #sentProt & _) Φpost".
    rewrite /MS_dequeue.
    wp_pure1.
    iLöb as "IH".
    iClear "IH". (* For now to reduce clutter. *)
    wp_pures.

    (* Load of sentinel pointer. *)
    wp_apply (wp_load_at_simple _ _
      (λ s v, ((toSent_prot R).(p_inv)) s v) with "[$sentProt]").
    {
      iModIntro. iIntros ([] ? _) "#inv".
      iFrame "inv". }
    iIntros ([] v) "(toSentPts & inv)".
    (* iDestruct (post_fence_extract _ (_) (∃ ℓsent, _) with "inv []") as "[hi ho]". *)
    (* { iDestruct 1 as (??) "(? & ? & lb)". *)
    (*   iSplitL "lb". *)
    (*   { admit. } *)
    wp_pures.
    wp_apply wp_fence.
    do 2 iModIntro.
    wp_pures.
    iDestruct "inv" as (???) "(-> & #sentPts & sentPtsLb)".

    (* Load of the pointer into the sentinel's content. *)
    wp_apply (wp_load_at_simple _ _
      (λ s v, node_prot_inv R ℓtoNext s v) with "[$sentPts]").
      (* (λ _ v, (∃ (ℓsent : loc), ⌜ v = #ℓsent⌝)%I) with "[]"). *)
    { iModIntro.
      simpl.
      iIntros (??) "?".
      epose proof (node_prot_inv_persistent _ _ _ _).
      iIntros "#I".
      iFrame "I". }
    iIntros (?sb ?v) "(? & nodeInv)".

    iDestruct (
        post_fence_extract _ (_) (∃ mx, ⌜v = InjRV (mx, #ℓtoNext)⌝) with "nodeInv []") as "[hi ho]".
    { epose proof (node_prot_inv_persistent _ _ _ _).
      iIntros "#H".
      iSplitL ""; first iApply "H".

      rewrite /node_prot_inv (fixpoint_unfold (pre_node_prot_inv R _) _ _).
      rewrite /pre_node_prot_inv.
      iDestruct "H" as (??) "(eq & _)".
      iClear "sentProt sentPts". (* To speed up the next iModIntro. *)
      iModIntro.
      iExists mx. iFrame "eq". }
    iDestruct "ho" as (mx) "->".

    rewrite /getValue.
    wp_pures.
    wp_apply wp_fence.
    iModIntro.
    rewrite (node_prot_inv_unfold R ℓtoNext _ _).
    iDestruct "hi" as (?? [= <-]) "(? & toNextPts & ?)".
    iModIntro.
    wp_pures.

    wp_apply (wp_load_at_simple _ _
      (λ s v, toNext_prot_inv _ s v) with "[$toNextPts]").
    { iModIntro. iIntros (??) "? #$ /=". }
    iIntros (??) "[toNextPts inv]".
    rewrite /toNext_prot_inv /=.
    simpl.




    destruct sL as [[ℓnext] | [ℓnext]].
    - (* nil node *)
      iDestruct "inv" as "(eq & nextPts & flushLb)".
      iDestruct (post_fence_flush_free with "eq") as %->.
      iClear "eq".
      iDestruct (post_fence_flush_free with "nextPts") as "nextPts".

      wp_apply (wp_load_at_simple _ _
        (λ s v, nil_node_prot.(p_inv) s v) with "[$nextPts]").
      { iModIntro. iIntros (??) "? #$ /=". }
      iIntros ([] ?) "[nextPts eq] /=".
      iDestruct (post_fence_flush_free with "eq") as %<-.
      iClear "eq".

      wp_pures.
      iModIntro.
      iApply "Φpost".
      iLeft. done.
    - (* cons node *)
      iDestruct "inv" as "(eq & nextPts & flushLb)".
      iDestruct (post_fence_flush_free with "eq") as %->.
      iClear "eq".
      iDestruct (post_fence_flush_free with "nextPts") as "nextPts".

      wp_apply (wp_load_at_simple ℓnext true
        (λ s v, ⌜ s = true ⌝ ∗ node_prot_inv R _ s v)%I with "[$nextPts]").
      { iModIntro. iIntros (?? [= ->]). simpl.
        epose proof (node_prot_inv_persistent _ _ _ _).
        iIntros "#$". done. }
      iIntros (??) "(nextPts & eq & nodeInv)".
      iDestruct (post_fence_flush_free with "eq") as %->. iClear "eq".
      rewrite (node_prot_inv_unfold R ℓtoNext _ _).
      rewrite /pre_node_prot_inv.
      iDestruct "nodeInv" as (mx' ?) "(eq & ? & toNextPts' & ?)".
      iDestruct (post_fence_flush_free with "eq") as %->. iClear "eq".

      wp_pures.
      wp_apply wp_fence.
      do 2 iModIntro.
      wp_pures.

      (* Q: How come we have to points-to assertions for ℓtoNext? *)
      wp_apply (wp_load_at_simple ℓtoNext (inr {| get_discrete := ℓnext |})
        (λ s v, toNext_prot_inv (node_prot_inv R ℓtoNext) s v)%I with "[toNextPts]").
      { iFrame "toNextPts".
        iModIntro.
        iIntros (??).

      }


      wp_apply (wp_cas_at (λ _, True)%I (λ _, True)%I _ _ (toSent_prot R) []
                with "[]").

  Qed.

  Lemma wpc_enqueue queue x s E :
    {{{ is_queue R queue ∗ R x }}}
      MS_enqueue queue x @ s ; E
    {{{ RET #(); True }}}.
  Proof.
  Admitted.

End specification.
