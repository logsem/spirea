(* In this file we define the post crash modality for the base logic. *)
From Coq Require Import QArith Qcanon.
From iris.algebra Require Import agree.
From iris.bi Require Import fractional.
From iris.proofmode Require Import reduction monpred tactics.

From Perennial.program_logic Require Export crash_lang.
From Perennial.Helpers Require Import ipm NamedProps.

From self Require Import extra if_non_zero.
From self.lang Require Import lang.
From self.base Require Import primitive_laws.

Set Default Proof Using "Type".

(** This definition captures the resources and knowledge you gain _after_ a
crash if you own a points-to predicate _prior to_ a crash. *)
Definition mapsto_post_crash `{nvmBaseFixedG Σ}
           (hG : nvmBaseDeltaG) ℓ q (hist : history) : iProp Σ :=
  ∃ CV,
    crashed_at CV ∗
    ((∃ t msg,
      ⌜CV !! ℓ = Some (MaxNat t)⌝ ∗
      ⌜hist !! t = Some msg⌝ ∗
      ⌜msg.(msg_persisted_after_view) ⊑ CV⌝ ∗
      ℓ ↦h{#q} {[ 0 := Msg msg.(msg_val) ∅ ∅ ∅ ]}) ∨
    ⌜CV !! ℓ = None⌝).

Instance fractional_mapsto_post_crash `{nvmBaseFixedG Σ} hG' ℓ hist :
  Fractional (λ p : Qp, mapsto_post_crash (Σ := Σ) hG' ℓ p hist).
Proof.
  rewrite /Fractional.
  iIntros (p q).
  rewrite /mapsto_post_crash.
  iSplit.
  - iIntros "[%CV [#crashed [left|#right]]]"; last first.
    * iSplitR; iExists (CV); iFrame "#"; iRight; iFrame "%".
    * iDestruct "left" as (t msg) "(% & % & % & [ptsA ptsB])".
      iSplitR "ptsB"; iExists (CV); iFrame "#"; iLeft;
        iExists t, msg; iFrame "∗%".
  - iIntros "[one two]".
    iDestruct "one" as (CV) "[crashed [pts | ?]]"; last naive_solver.
    iDestruct "two" as (CV') "[crashed' [pts' | ?]]"; last naive_solver.
    iDestruct (crashed_at_agree with "crashed crashed'") as %<-.
    iClear "crashed'".
    iExists CV. iFrame "crashed".
    iDestruct "pts" as (t msg) "(% & % & % & pts)".
    iDestruct "pts'" as (t' msg') "(% & % & % & pts')".
    simplify_eq.
    iLeft. iExists _, _. iFrame "∗%".
Qed.

(* Note: The odd [let]s below are to manipulate the type class instance
search. *)

(** This map is used to exchange points-to predicates valid prior to a crash
into points-to predicates valid after the crash. *)
Definition post_crash_mapsto_map `{nvmBaseFixedG Σ} (σ__old : store)
           (hG hG' : nvmBaseDeltaG) : iProp Σ :=
  (* Used to conclude that the locations owned are included in the heap in
  question. *)
  (∀ ℓ dq (hist : history),
      (let hG := hG in ℓ ↦h{dq} hist) -∗ ⌜σ__old !! ℓ = Some hist⌝) ∗
  (* The map used to the the exchange. *)
  [∗ map] ℓ ↦ hist ∈ σ__old,
    soft_disj (λ q, let hG := hG in ℓ ↦h{#q} hist)
              (λ p, mapsto_post_crash hG' ℓ p hist).

Definition persisted_impl `{nvmBaseFixedG Σ} hGD hGD' : iProp Σ :=
  □ ∀ V, persisted (hGD := hGD) V -∗
    persisted (hGD := hGD') (view_to_zero V) ∗
     ∃ CV, ⌜V ⊑ CV⌝ ∗ crashed_at (hGD := hGD') CV.

Definition post_crash `{nvmBaseFixedG Σ, hDG : nvmBaseDeltaG}
           (P : nvmBaseDeltaG → iProp Σ) : iProp Σ :=
  (∀ (s : store) hDG',
    persisted_impl hDG hDG' -∗
    post_crash_mapsto_map s hDG hDG' -∗
    (post_crash_mapsto_map s hDG hDG' ∗ P hDG')).

Notation "'<PC>' g , P" := (post_crash (λ g, P))
  (at level 200, g binder, right associativity) : bi_scope.

Lemma post_crash_map_exchange `{nvmBaseFixedG Σ} σ__old
      (hG hG' : nvmBaseDeltaG) ℓ q hist :
  post_crash_mapsto_map σ__old hG hG' -∗
  (let hG := hG in ℓ ↦h{#q} hist) -∗
    post_crash_mapsto_map σ__old hG hG' ∗
    mapsto_post_crash hG' ℓ q hist.
Proof.
  iDestruct 1 as "[look map]".
  iIntros "pts".
  iAssert (⌜σ__old !! ℓ = Some hist⌝)%I as %elemof.
  { iApply "look". iFrame. }
  iDestruct (big_sepM_lookup_acc with "map") as "[elm reIns]"; first done.

  iDestruct (soft_disj_exchange_l with "[] elm pts") as "[elm new]".
  { iModIntro. iIntros (?) "pts".
    setoid_rewrite <- dfrac_valid_own.
    iApply (mapsto_valid with "pts"). }
  iFrame. iApply "reIns". iFrame.
Qed.

Section post_crash_prop.
  Context `{hG : !nvmBaseFixedG Σ, hDG : nvmBaseDeltaG}.
  Implicit Types Φ : thread_val → iProp Σ.
  Implicit Types efs : list thread_state.
  Implicit Types σ : mem_config.
  Implicit Types v : thread_val.

  (** Tiny shortcut for introducing the assumption for a [post_crash]. *)
  Ltac iIntrosPostCrash := iIntros (σ hG') "#perToRec map".

  Lemma post_crash_intro Q :
    (⊢ Q) →
    (⊢ <PC> _, Q).
  Proof. iIntros (Hmono). iIntrosPostCrash. iFrame "∗". iApply Hmono. Qed.

  (* Lemma post_crash_idemp P : post_crash (λ hG, post_crash P) ⊢ post_crash P. *)
  (* Proof. *)
  (*   iIntros "P". *)
  (*   rewrite /post_crash. *)
  (*   iIntrosPostCrash. *)
  (*   iDestruct ("P" $! σ _ with "[$] map") as "[map P]". *)
  (*   iDestruct ("P" $! σ _ with "[] map") as "HIHI". *)
  (* Qed. *)

  Lemma post_crash_mono P Q :
    (∀ hG, P hG -∗ Q hG) →
    post_crash P -∗ post_crash Q.
  Proof.
    iIntros (Hmono) "HP".
    iIntrosPostCrash.
    iDestruct ("HP" $! σ hG' with "[$] [$]") as "($ & P)".
    by iApply Hmono.
  Qed.

  Lemma post_crash_emp :
    emp ⊢ post_crash (λ _, emp).
  Proof. iIntros "emp". iIntrosPostCrash. iFrame. Qed.

  (* This lemma seems to not hold for our post crash modality.. *)
  (* Lemma post_crash_pers P Q : *)
  (*   (P -∗ post_crash Q) → *)
  (*   □ P -∗ post_crash (λ hG, □ Q hG). *)
  (* Proof. *)
  (*   iIntros (Hmono) "#HP". *)
  (*   iIntrosPostCrash. *)
  (*   iDestruct (Hmono with "HP") as "HQ". *)
  (*   iDestruct ("HQ" $! _ _ _ with "perToRec map") as "[$ HQ']". *)
  (*   iModIntro. iFrame. *)
  (* Qed. *)

  Lemma post_crash_sep P Q :
    post_crash P ∗ post_crash Q ⊢ <PC> hG, P hG ∗ Q hG.
  Proof.
    iIntros "(HP & HQ)".
    iIntrosPostCrash.
    iDestruct ("HP" $! σ hG' with "[$] [$]") as "(map & $)".
    iDestruct ("HQ" $! σ hG' with "[$] [$]") as "$".
  Qed.

  (* Lemma post_crash_or P Q : *)
  (*   post_crash P ∨ post_crash Q -∗ post_crash (λ hG, P hG ∨ Q hG). *)
  (* Proof. *)
  (*   iIntros "[HP|HQ]"; iIntros (???) "#Hrel". *)
  (*   - iLeft. by iApply "HP". *)
  (*   - iRight. by iApply "HQ". *)
  (* Qed. *)

  (* Lemma post_crash_and P Q : *)
  (*   post_crash P ∧ post_crash Q -∗ post_crash (λ hG, P hG ∧ Q hG). *)
  (* Proof. *)
  (*   iIntros "HPQ"; iIntros (???) "#Hrel". *)
  (*   iSplit. *)
  (*   - iDestruct "HPQ" as "(HP&_)". by iApply "HP". *)
  (*   - iDestruct "HPQ" as "(_&HQ)". by iApply "HQ". *)
  (* Qed. *)

  Lemma post_crash_pure (P : Prop) : P → ⊢ <PC> _, ⌜ P ⌝.
  Proof. intros HP. iIntrosPostCrash. iFrame "%∗". Qed.

  (* Any resource [P] is available after a crash. This lemmas is intended for
  cases where [P] does not refer to the global resources/gname. *)
  Lemma post_crash_nodep P : P -∗ <PC> _, P.
  Proof. iIntros "?". iIntrosPostCrash. iFrame "∗". Qed.

  Lemma post_crash_for_all Q :
    (∀ hG, Q hG) -∗ post_crash Q.
  Proof.
    iIntros "HP".
    iIntrosPostCrash. iFrame. iApply "HP".
  Qed.

  Lemma post_crash_proper :
    Proper (pointwise_relation _ (⊣⊢) ==> (⊣⊢)) post_crash.
  Proof.
    intros ?? eq.
    apply (anti_symm _).
    - iApply post_crash_mono. intros. rewrite -eq. iIntros "$".
    - iApply post_crash_mono. intros. rewrite -eq. iIntros "$".
  Qed.

  (* Lemma post_crash_exists {A} P Q : *)
  (*   (∀ (x: A), P hG x -∗ post_crash (λ hG, Q hG x)) -∗ *)
  (*   (∃ x, P hG x) -∗ post_crash (λ hG, ∃ x, Q hG x). *)
  (* Proof. *)
  (*   iIntros "Hall HP". iIntros (???) "#Hrel". *)
  (*   iDestruct "HP" as (x) "HP". *)
  (*   iExists x. iApply ("Hall" with "[$] [$]"). *)
  (* Qed. *)

  (* Lemma post_crash_forall {A} P Q : *)
  (*   (∀ (x: A), P hG x -∗ post_crash (λ hG, Q hG x)) -∗ *)
  (*   (∀ x, P hG x) -∗ post_crash (λ hG, ∀ x, Q hG x). *)
  (* Proof. *)
  (*   iIntros "Hall HP". iIntros (???) "#Hrel". *)
  (*   iIntros (?). iApply ("Hall" with "[HP] [$]"). iApply "HP". *)
  (* Qed. *)

  (* Lemma post_crash_exists_intro {A} P (x: A): *)
  (*   (∀ (x: A), P hG x -∗ post_crash (λ hG, P hG x)) -∗ *)
  (*   P hG x -∗ post_crash (λ hG, ∃ x, P hG x). *)
  (* Proof. *)
  (*   iIntros "Hall HP". iIntros (???) "#Hrel". *)
  (*   iExists x. iApply ("Hall" with "[$] [$]"). *)
  (* Qed. *)

  (* Global Instance from_exist_post_crash {A} (Φ: nvmBaseFixedG Σ, nvmBaseDeltaG → iProp Σ) (Ψ: nvmBaseFixedG Σ, nvmBaseDeltaG → A → iProp Σ) *)
  (*   {Himpl: ∀ hG, FromExist (Φ hG) (λ x, Ψ hG x)} : *)
  (*   FromExist (post_crash (λ hG, Φ hG)) (λ x, post_crash (λ hG, Ψ hG x)). *)
  (* Proof. *)
  (*   hnf; iIntros "H". *)
  (*   iDestruct "H" as (x) "H". *)
  (*   rewrite /post_crash. *)
  (*   iIntros (σ hG') "Hrel". *)
  (*   iSpecialize ("H" with "Hrel"). *)
  (*   iExists x; iFrame. *)
  (* Qed. *)

  Lemma post_crash_named P name:
    named name (post_crash (λ hG, P hG)) ⊢
    post_crash (λ hG, named name (P hG)).
  Proof. rewrite //=. Qed.

  Lemma post_crash_persisted V :
    persisted V -∗
    post_crash (λ hG', persisted (view_to_zero V) ∗
                       ∃ CV, ⌜V ⊑ CV⌝ ∗ crashed_at CV).
  Proof.
    iIntros "pers".
    iIntrosPostCrash.
    iFrame.
    iDestruct ("perToRec" with "pers") as "[$ $]".
  Qed.

  Lemma post_crash_persisted_loc ℓ t :
    persisted_loc ℓ t -∗
    post_crash (λ hG',
      persisted_loc ℓ 0 ∗
      ∃ CV t', ⌜CV !! ℓ = Some (MaxNat t') ∧ t ≤ t'⌝ ∗ crashed_at CV)%I.
  Proof.
    iIntros "pers".
    iDestruct (post_crash_persisted with "pers") as "H".
    iApply (post_crash_mono with "H").
    rewrite view_to_zero_singleton.
    setoid_rewrite view_le_singleton.
    setoid_rewrite bi.pure_exist.
    setoid_rewrite bi.sep_exist_r.
    naive_solver.
  Qed.

  Lemma post_crash_persisted_persisted V :
    persisted V -∗ post_crash (λ hG', persisted (view_to_zero V)).
  Proof.
    iIntros "pers".
    iDestruct (post_crash_persisted with "pers") as "p".
    iApply (post_crash_mono with "p").
    iIntros (?) "[??]". iFrame.
  Qed.

  Lemma post_crash_persisted_recovered V :
    persisted V -∗ post_crash (λ hG', ∃ CV, ⌜V ⊑ CV⌝ ∗ crashed_at CV).
  Proof.
    iIntros "pers".
    iDestruct (post_crash_persisted with "pers") as "p".
    iApply (post_crash_mono with "p").
    iIntros (?) "[??]". iFrame.
  Qed.

  Lemma post_crash_mapsto ℓ q hist :
    ℓ ↦h{#q} hist -∗ post_crash (λ hG', mapsto_post_crash _ ℓ q hist).
  Proof.
    iIntros "pts".
    iIntrosPostCrash.
    iApply (post_crash_map_exchange with "map pts").
  Qed.

  (*
  Lemma recovered_look_eq V W ℓ t t' :
    V !! ℓ = Some (MaxNat t) →
    W !! ℓ = Some (MaxNat t') →
    recovered V -∗
    recovered W -∗
    ⌜t = t'⌝.
  Proof.
    iIntros (lookV lookW) "rec rec'".
    iDestruct "rec" as (?) "[%all ag]".
    iDestruct "rec'" as (full) "[%all' ag']".
    iDestruct (own_valid_2 with "ag ag'") as %->%to_agree_op_inv_L.
    iPureIntro.
    eapply map_Forall_lookup_1 in all; last done.
    eapply map_Forall_lookup_1 in all'; last done.
    assert (Some (MaxNat t) = Some (MaxNat t')) as [=] by congruence.
    done.
  Qed.

  Lemma recovered_lookup_extract_singleton V ℓ t :
    V !! ℓ = Some (MaxNat t) →
    recovered V -∗
    recovered {[ℓ := MaxNat t]}.
  Proof.
    iIntros (look) "rec".
    iDestruct "rec" as (full all) "ag".
    iExists full. iFrame.
    iPureIntro.
    apply map_Forall_singleton.
    apply all.
    done.
  Qed.
  *)

  (* This lemma is no longer up to date after the change to
  recovered/crashed_at, but if (or when) we need it we can tweak it. *)
  (*
  Lemma mapsto_post_crash_recovered V t__low ℓ q hist :
    V !! ℓ = Some (MaxNat t__low) →
    (∃ CV, ⌜V ⊑ CV⌝ ∗ recovered CV) -∗  (* What persisted gives us after crash. *)
    mapsto_post_crash hG ℓ q hist -∗      (* What mapsto gives us after crash *)
    (∃ t msg, ⌜hist !! t = Some msg⌝ ∗
              ⌜t__low ≤ t⌝ ∗
              ℓ ↦h{#q} ({[ 0 := Msg msg.(msg_val) ∅ ∅ ∅]}) ∗
              (∃ RV, ⌜msg.(msg_persisted_after_view) ⊑ RV⌝ ∗ recovered RV) ∗
              recovered {[ ℓ := MaxNat t ]}).
  Proof.
    iIntros (look) "A [B|B]"; iDestruct "A" as (RV incl) "#rec".
    - iDestruct "B" as (t msg look') "(pts & #rec' & hihi)".
      iExists t, msg. iFrame "%#∗".
      pose proof (view_le_look _ _ _ _ look incl) as [t' [RVlook ho]].
      iDestruct (recovered_look_eq with "rec rec'") as "<-"; [done|apply lookup_singleton|].
      done.
    - pose proof (view_le_look _ _ _ _ look incl) as [t' [RVlook ho]].
      iExFalso. iApply "B".
      iApply recovered_lookup_extract_singleton; done.
  Qed.
  *)

End post_crash_prop.

Class IntoCrash {Σ} `{nvmBaseFixedG Σ, nvmBaseDeltaG}
      (P : iProp Σ) (Q : nvmBaseDeltaG → iProp Σ) :=
  into_crash : P ⊢ post_crash (Σ := Σ) (λ hG', Q hG').

Section IntoCrash.
  Context `{hG : !nvmBaseFixedG Σ, hDG : nvmBaseDeltaG}.

  Global Instance sep_into_crash P P' Q Q':
    IntoCrash P P' →
    IntoCrash Q Q' →
    IntoCrash (P ∗ Q)%I (λ hG, P' hG ∗ Q' hG)%I.
  Proof.
    iIntros (H1 H2). rewrite /IntoCrash.
    rewrite (@into_crash _ _ _ P).
    rewrite (@into_crash _ _ _ Q).
    apply post_crash_sep.
  Qed.

(*   Global Instance or_into_crash P P' Q Q': *)
(*     IntoCrash P P' → *)
(*     IntoCrash Q Q' → *)
(*     IntoCrash (P ∨ Q)%I (λ hG, P' hG ∨ Q' hG)%I. *)
(*   Proof. *)
(*     iIntros (H1 H2). rewrite /IntoCrash. *)
(*     rewrite (@into_crash _ _ P). *)
(*     rewrite (@into_crash _ _ Q). *)
(*     rewrite post_crash_or //. *)
(*   Qed. *)

(*   Global Instance and_into_crash P P' Q Q': *)
(*     IntoCrash P P' → *)
(*     IntoCrash Q Q' → *)
(*     IntoCrash (P ∧ Q)%I (λ hG, P' hG ∧ Q' hG)%I. *)
(*   Proof. *)
(*     iIntros (H1 H2). rewrite /IntoCrash. *)
(*     rewrite (@into_crash _ _ P). *)
(*     rewrite (@into_crash _ _ Q). *)
(*     rewrite post_crash_and //. *)
(*   Qed. *)

  (* XXX: probably should rephrase in terms of IntoPure *)
  Global Instance pure_into_crash (P : Prop) :
    IntoCrash (⌜ P ⌝%I) (λ _, ⌜ P ⌝%I).
  Proof. rewrite /IntoCrash. iIntros "%". by iApply post_crash_pure. Qed.

  Global Instance exist_into_crash {A} Φ Ψ:
    (∀ x : A, IntoCrash (Φ x) (λ hG, Ψ hG x)) →
    IntoCrash (∃ x, Φ x)%I (λ hG, (∃ x, Ψ hG x)%I).
  Proof.
    rewrite /IntoCrash.
    iIntros (?) "H". iDestruct "H" as (?) "HΦ". iPoseProof (H with "[$]") as "HΦ".
    iApply (post_crash_mono with "HΦ"). eauto.
  Qed.

  (* Global Instance forall_into_crash {A} Φ Ψ: *)
  (*   (∀ x : A, IntoCrash (Φ x) (λ hG, Ψ hG x)) → *)
  (*   IntoCrash (∀ x, Φ x)%I (λ hG, (∀ x, Ψ hG x)%I). *)
  (* Proof. *)
  (*   rewrite /IntoCrash. *)
  (*   iIntros (?) "H". iApply post_crash_forall; last eauto. iIntros (?). iApply H. *)
  (* Qed. *)

(*   (* *)
(*   Global Instance post_crash_into_crash P : *)
(*     IntoCrash (post_crash P) P. *)
(*   Proof. rewrite /IntoCrash. by iApply post_crash_mono. Qed. *)
(*    *) *)

  Lemma into_crash_proper P P' Q Q':
    IntoCrash P Q →
    (P ⊣⊢ P') →
    (∀ hG, Q hG ⊣⊢ Q' hG) →
    IntoCrash P' Q'.
  Proof.
    rewrite /IntoCrash.
    iIntros (HD Hwand1 Hwand2) "HP".
    iApply post_crash_mono; last first.
    { iApply HD. iApply Hwand1. eauto. }
    intros. simpl. rewrite Hwand2. naive_solver.
  Qed.

(*   Global Instance big_sepL_into_crash: *)
(*     ∀ (A : Type) Φ (Ψ : nvmBaseFixedG Σ, nvmBaseDeltaG → nat → A → iProp Σ) (l : list A), *)
(*     (∀ (k : nat) (x : A), IntoCrash (Φ k x) (λ hG, Ψ hG k x)) → *)
(*     IntoCrash ([∗ list] k↦x ∈ l, Φ k x)%I (λ hG, [∗ list] k↦x ∈ l, Ψ hG k x)%I. *)
(*   Proof. *)
(*     intros. *)
(*     cut (∀ n, IntoCrash ([∗ list] k↦x ∈ l, Φ (n + k)%nat x)%I *)
(*                         (λ hG, [∗ list] k↦x ∈ l, Ψ hG (n + k)%nat x)%I). *)
(*     { intros Hres. specialize (Hres O). eauto. } *)
(*     induction l => n. *)
(*     - rewrite //=. apply _. *)
(*     - rewrite //=. apply sep_into_crash; eauto. *)
(*       eapply into_crash_proper; first eapply (IHl (S n)). *)
(*       * intros. setoid_rewrite Nat.add_succ_r. setoid_rewrite <-Nat.add_succ_l. eauto. *)
(*       * intros. setoid_rewrite Nat.add_succ_r. setoid_rewrite <-Nat.add_succ_l. eauto. *)
(*   Qed. *)

  Global Instance big_sepM_into_crash `{Countable K} :
    ∀ (A : Type) Φ (Ψ : nvmBaseDeltaG → K → A → iProp Σ) (m : gmap K A),
    (∀ (k : K) (x : A), IntoCrash (Φ k x) (λ hG, Ψ hG k x)) →
    IntoCrash ([∗ map] k↦x ∈ m, Φ k x)%I (λ hG, [∗ map] k↦x ∈ m, Ψ hG k x)%I.
  Proof.
    intros. induction m using map_ind.
    - eapply (into_crash_proper True%I _ (λ _, True%I)).
      * apply _.
      * rewrite big_sepM_empty; auto.
      * intros. rewrite big_sepM_empty; auto.
    - eapply (into_crash_proper (Φ i x ∗ [∗ map] k↦x0 ∈ m, Φ k x0) _
                                (λ _, (Ψ _ i x ∗ [∗ map] k↦x0 ∈ m, Ψ _ k x0)%I)).
      * apply _.
      * rewrite big_sepM_insert //=.
      * intros. rewrite big_sepM_insert //=.
  Qed.

(*   Global Instance big_sepS_into_crash `{Countable K} : *)
(*     ∀ Φ (Ψ : nvmBaseFixedG Σ, nvmBaseDeltaG → K → iProp Σ) (m : gset K), *)
(*     (∀ (k : K), IntoCrash (Φ k) (λ hG, Ψ hG k)) → *)
(*     IntoCrash ([∗ set] k ∈ m, Φ k)%I (λ hG, [∗ set] k ∈ m, Ψ hG k)%I. *)
(*   Proof. *)
(*     intros. induction m as [|i m ? IH] using set_ind_L => //=. *)
(*     - eapply (into_crash_proper True%I _ (λ _, True%I)). *)
(*       { apply _. } *)
(*       * rewrite big_sepS_empty; eauto. *)
(*       * intros. rewrite big_sepS_empty; eauto. *)
(*     - eapply (into_crash_proper (Φ i ∗ [∗ set] k ∈ m, Φ k) _ *)
(*                                 (λ _, (Ψ _ i ∗ [∗ set] k ∈ m, Ψ _ k)%I)). *)
(*       { apply _. } *)
(*       * rewrite big_sepS_insert //=. *)
(*       * intros. rewrite big_sepS_insert //=. *)
(*   Qed. *)

(*   Lemma into_crash_post_crash_frame_l P P' `{!IntoCrash P P'} Q : *)
(*     P -∗ post_crash Q -∗ post_crash (λ hG', P' hG' ∗ Q hG'). *)
(*   Proof. iIntros "HP HQ". rewrite (@into_crash _ _ P). iApply post_crash_sep. iFrame. Qed. *)

(*   Lemma into_crash_post_crash_frame_r P P' `{!IntoCrash P P'} Q : *)
(*     post_crash Q -∗ P  -∗ post_crash (λ hG', Q hG' ∗ P' hG'). *)
(*   Proof. iIntros "HP HQ". rewrite (@into_crash _ _ P). iApply post_crash_sep. iFrame. Qed. *)

  Global Instance persisted_into_crash PV :
    IntoCrash (persisted PV)
              (λ hG', persisted ((λ _, MaxNat 0) <$> PV) ∗
                      ∃ CV, ⌜PV ⊑ CV⌝ ∗ crashed_at CV)%I.
  Proof. rewrite /IntoCrash. iApply post_crash_persisted. Qed.

  Global Instance persisted_loc_into_crash ℓ t :
    IntoCrash
      (persisted_loc ℓ t)
      (λ hG', persisted_loc ℓ 0 ∗
              ∃ CV t', ⌜CV !! ℓ = Some (MaxNat t') ∧ t ≤ t'⌝ ∗ crashed_at CV)%I.
  Proof. rewrite /IntoCrash. iApply post_crash_persisted_loc. Qed.

End IntoCrash.

Lemma modus_ponens {Σ} (P Q : iProp Σ) : P ⊢ (P -∗ Q) -∗ Q.
Proof. iIntros "HP Hwand". by iApply "Hwand". Qed.

Ltac crash_env Γ :=
  match Γ with
    | environments.Enil => idtac
    | environments.Esnoc ?Γ' ?id (post_crash _) => crash_env Γ'
    | environments.Esnoc ?Γ' ?id ?A => first [ iEval (rewrite (@into_crash _ _ _ A) ) in id || iClear id ] ; crash_env Γ'
  end.

Ltac crash_ctx :=
  match goal with
  | [ |- environments.envs_entails ?Γ _] =>
    let spatial := pm_eval (environments.env_spatial Γ) in
    let intuit := pm_eval (environments.env_intuitionistic Γ) in
    crash_env spatial; crash_env intuit
  end.

Ltac iCrash :=
  crash_ctx;
  iApply (modus_ponens with "[-]"); [ iNamedAccu | ];
  rewrite ?post_crash_named ?post_crash_sep; iApply post_crash_mono;
  intros; simpl;
  let H := iFresh in iIntros H; iNamed H.

Section post_crash_modality_test.
  Context {Σ: gFunctors}.
  Context `{nvmBaseFixedG Σ, nvmBaseDeltaG}.
  Context `{Q : iProp Σ}.
  Context `{Hi1: !IntoCrash P P'}.
  Context `{Hi2: !IntoCrash Q Q'}.

  Lemma test R ℓ t :
    P -∗ persisted_loc ℓ t -∗ ⌜ R ⌝ -∗ post_crash (λ hG', P' hG').
  Proof using All.
    iIntros "HP HQ HR".
    iCrash.
    iFrame.
  Qed.

End post_crash_modality_test.
