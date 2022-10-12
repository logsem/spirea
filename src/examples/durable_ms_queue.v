(* This in an implementation of a durable variant of the fine-grained concurrent
Michael-Scott queue. *)

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
     recovery_weakestpre lifted_modalities protocol protocols no_buffer mapsto_na_flushed.
From self.high.modalities Require Import fence.


(* Implementation. *)

Section implementation.

  Notation NONE := (InjL #()).

  (*
  (* Construct a new empty queue. *)
  Definition mk_queue : expr :=
    λ: <>,
      let: "node" := ref_NA (InjL #()) in
      Flush "node" ;;
      Fence ;;
      let: "toHead" := ref_AT "node" ;;
      let: "toTail" := ref_AT "node" ;;
      ("toHead", "toTail").

  Definition enqueue : expr :=
    λ: "toHead" "val",
      let: "toNext" := ref_NA #() in
      let: "newNode" := ref_NA (InjR ("val", "toNext")) in
      Flush "newNode" ;;
      (rec: "loop" <> :=
        let: "head" := !_AT "toHead" in
        "toNext" <-_NA "head" ;;
        Flush "toNext" ;;
        Fence ;;
        if: CAS "toHead" "head" "newNode"
        then #()
        else "loop" #()
      ) #().

  Definition dequeue : expr :=
    rec: "loop" "q" :=
      let: "toHead" := Fst "q" in
      let: "head" := !_AT "toHead" in
      Fence ;;
      match: !_NA "head" with
        NONE => NONE
      | SOME "pair" =>
          let: "nextNode" := !_NA (Snd "pair") in
          if: CAS "toHead" "head" "nextNode"
          then SOME (Fst "pair")
          else "loop" "toHead"
      end.
  *)

  (* Definition sync : expr := *)
  (*   λ: "toHead", *)
  (*     Flush "toHead" ;; *)
  (*     FenceSync. *)

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
      let: "c" := getValue (!_AT "sent") in
      match: !_AT (!_AT (Snd "c")) with
        NONE => NONE
      | SOME "n'" =>
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

  Definition toNext_prod_inv (pred : loc_pred bool) :
      loc_pred (discreteState loc + discreteState loc) :=
    λ ml v,
      match ml with
        inl (mk_discrete ℓ) =>
          ⌜ v = #(ℓ : loc) ⌝ ∗ know_pred_d ℓ pred
      | inr (mk_discrete ℓ) =>
          ⌜ v = #ℓ ⌝ ∗ know_pred_d ℓ pred
      end%I.

  Definition pre_node_prot_inv (ℓtoNext : loc) :
     (loc_predO bool) -d> loc_predO bool :=
    λ self b v,
      (∃ mx,
        ⌜ v = (InjRV (mx, #ℓtoNext)) ⌝ ∗
        match b with
          (* Is initial sentinel. *)
          false => True
          (* Is not a sentinel node. *)
        | true => ∃ x, ⌜ mx = SOMEV x ⌝ ∗ R x
        end ∗
        ▷ know_pred_d ℓtoNext (toNext_prod_inv self))%I
    .

  Global Instance pre_node_prot_inv_contractive ℓtoNext :
    Contractive (pre_node_prot_inv ℓtoNext).
  Proof.
    intros ???? [|].
    (* solve_contractive. *)
  Admitted.

  Definition node_prot_inv ℓtoNext :=
    fixpoint (pre_node_prot_inv ℓtoNext).

  Program Definition node_prot (ℓtoNext : loc) : LocationProtocol bool :=
    {| pred := (node_prot_inv ℓtoNext);
       bumper := id |}.
  Next Obligation.

  Program Definition cons_node_prot (ℓtoNext : loc) : LocationProtocol bool :=
    {| pred b v := (∃ mx,
        ⌜ v = (InjRV (mx, #ℓtoNext)) ⌝ ∗
        (* no info about [ℓtoNext] *)
        (* ℓtoNext ↦_AT^{toNext_prot} [false] ∗ *)
        match b with
          (* Might be a sentinel node. *)
          false => True
          (* Is not a sentinel node. *)
        | true => ∃ x, ⌜ mx = SOMEV x ⌝ ∗ R x
       end)%I;
       bumper := id
    |}.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

    (* constant_prot (InjRV (x, #ℓtoNext)). *)

  Program Definition toNext_prot :
    LocationProtocol ((discreteState loc) + (discreteState loc)) :=
    {| pred ml v :=
        ⌜ match ml with
          inl (mk_discrete ℓ) => v = #ℓ
        | inr (mk_discrete ℓ) => v = #ℓ
        end ⌝%I;
      bumper := id |}.
  Next Obligation. Admitted.

  (* (* The protocol for the location going _out_ from a node. The protocol can *)
  (* move from [none] (no successor) to [some ℓnext] (a successor) when a new node *)
  (* is enqueued. *) *)
  (* Program Definition toNext_prot : LocationProtocol (option (discreteState loc)) := *)
  (*   {| pred ml v := (∃ (ℓnext : loc), *)
  (*       (* The value pointed to is always a location. *) *)
  (*       ⌜ v = #ℓnext ⌝ ∗ *)
  (*       match ml with *)
  (*         (* False means no successor. *) *)
  (*         None => ℓnext ↦_AT^{nil_node_prot} [()] *)
  (*         (* False means that a successor is present. *) *)
  (*       | Some (mk_discrete ℓnext') => *)
  (*         ⌜ ℓnext = ℓnext' ⌝ ∗ *)
  (*         ∃ ℓtoNext, ℓnext ↦_AT^{cons_node_prot ℓtoNext} [true] *)
  (*       end)%I; *)
  (*      bumper := id |}. *)
  (* Next Obligation. Admitted. *)
  (* Next Obligation. Admitted. *)

  (* [n] is the length of the list. *)
  Fixpoint is_node ℓnode (n : nat) : dProp Σ :=
    match n with
    | 0 => (* ∃ q, *)
      ℓnode ↦_AT^{nil_node_prot} [()] ∗
      flush_lb ℓnode nil_node_prot ()
    | S m => ∃ (ℓtoNext ℓnext : loc),
      (* ℓnode *)
      ℓnode ↦_AT^{cons_node_prot ℓtoNext} [true] ∗
      flush_lb ℓnode (cons_node_prot ℓtoNext) true ∗
      (* ℓtoNext *)
      ℓtoNext ↦_AT^{toNext_prot} [inr (mk_discrete ℓnext)] ∗
      flush_lb ℓtoNext toNext_prot (inr (mk_discrete ℓnext)) ∗
      is_node ℓnext m
  end.

  (* [n] is a lower bound on how many successor nodes [ℓtoNext] points to. *)
  Fixpoint successors ℓtoNext (n : nat) : dProp Σ :=
    ∃ ℓnext,
      match n with
      | 0 => (* ∃ q, *)
        ℓtoNext ↦_AT^{toNext_prot} [inl (mk_discrete ℓnext)] ∗
        flush_lb ℓtoNext toNext_prot (inl (mk_discrete ℓnext)) ∗
        ℓnext ↦_AT^{nil_node_prot} [()] ∗
        flush_lb ℓnext nil_node_prot ()
      | S m => ∃ (ℓnextOut ℓsucc : loc),
        (* ℓnode *)
        (* ℓnode ↦_AT^{cons_node_prot ℓtoNext} [true] ∗ *)
        (* flush_lb ℓnode (cons_node_prot ℓtoNext) true ∗ *)
        (* ℓtoNext *)
        ℓtoNext ↦_AT^{toNext_prot} [inr (mk_discrete ℓnext)] ∗
        flush_lb ℓtoNext toNext_prot (inr (mk_discrete ℓnext)) ∗
        ℓnext ↦_AT^{cons_node_prot ℓnextOut} [true] ∗
        flush_lb ℓnext (cons_node_prot ℓnextOut) true ∗
        successors ℓnextOut m
  end.

  Global Instance successors_persistent ℓtoNext n : Persistent (successors ℓtoNext n).
  Proof.
    generalize dependent ℓtoNext.
    induction n; simpl; try apply _.
  Qed.

  Program Definition toSent_prot :=
    {| pred := λ (_ : unit) v, (∃ (ℓsent ℓtoNext : loc) n,
        ⌜ v = #ℓsent ⌝ ∗
        ℓsent ↦_AT^{cons_node_prot ℓtoNext} [false] ∗
        flush_lb ℓsent (cons_node_prot ℓtoNext) false ∗
        successors ℓtoNext n)%I;
       bumper v := v |}.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

  (* Program Definition toTail_prot := *)
  (*   {| pred := λ (_ : unit) v, ∃ ℓtail ℓtoNext n, *)
  (*     ⌜ v = #ℓtail ⌝ ∗ *)
  (*     ℓtail ↦_AT^{cons_node_prot ℓtoNext} [false] ∗ *)
  (*     flush_lb ℓnode (cons_node_prot ℓtoNext) false ∗ *)
  (*       ; *)
  (*      bumper v := v |}. *)
  Definition toTail_prot := toSent_prot.

  (* The representation predicate for the MS queue. *)
  Definition is_queue (queue : val) : dProp Σ :=
    ∃ (ℓtoS ℓtoT : loc),
      ⌜ queue = (#ℓtoS, #ℓtoT)%V ⌝ ∗ (* R queue *)
      (* ℓtoS *)
      ℓtoS ↦_AT^{toSent_prot} [()] ∗
      (* ℓtoT *)
      ℓtoT ↦_AT^{toTail_prot} [()].

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
    wp_apply (wp_load_at_simple _ _
      (λ s v, ((toSent_prot R).(pred)) s v) with "[]").
      (* (λ _ v, (∃ (ℓsent : loc), ⌜ v = #ℓsent⌝)%I) with "[]"). *)
    { iFrame "sentProt".
      iModIntro. iIntros ([] ? _) "inv".
      simpl.
      iDestruct "inv" as (???) "(-> & #sentPts & #sentF & #s)".
      iSplit;
        (repeat iExists _; iSplitPure; first done; iFrame "#"). }
    iIntros ([] v) "(toSentPts & inv)".
    iDestruct (post_fence_extract with "inv []") as "[hi ho]".
    { iIntros (??) "H".
    wp_pures.

  Admitted.

  Lemma wpc_enqueue queue x s E :
    {{{ is_queue R queue ∗ R x }}}
      MS_enqueue queue x @ s ; E
    {{{ RET #(); True }}}.
  Proof.
  Admitted.

End specification.
