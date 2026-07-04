From iris_named_props Require Import named_props.
From iris.algebra Require Import excl.

From self.high.lib Require Import abstract_state abstract_state_instances.
From self.high Require Import protocol wpc_proofmode.
From self.high Require Import recovery_weakestpre adequacy.

From self.examples.lib Require Import gen_maps.

Definition init: expr :=
  λ: <>,
    let: "l" := ref_AT #0 in
    Flush "l";;
    FenceSync ;;
    "l".

Definition deposit ℓ: expr :=
  λ: "n",
    FAA #ℓ "n" ;;
    Flush #ℓ ;;
    FenceSync.

(* This [withdraw] is weaker than the in-paper version, but we can
 * nevertheless verify against the same spec. *)
Definition withdraw ℓ: expr :=
  λ: "n",
    let: "v" := FAA #ℓ (- "n") in
    (* Flush #ℓ ;; *)
    (* FenceSync ;; *)
    "v".

Section bank_protocol.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !gen_mapG nat Σ Ω}.
  Notation state := (list (nat + nat)).
  Variables (γ: gname).
  Implicit Types (m m__w: gmap nat nat) (h: state) (v: val).

  (* abstract state *)
  Program Instance list_abstract_state T `{!EqDecision T, Countable T} : AbstractState (list T) :=
    { abs_state_relation := prefix }.

  Definition to_auth (h: state): gmap nat nat :=
    omap (λ x, match x with inl n => Some n | _ => None end) $ map_seq 0 h.

  Definition dsum h :=
    (foldl (λ sum x, match x with inl n => sum + n | _ => sum end) 0 h).
  Definition wsum h :=
    (foldl (λ sum x, match x with inr n => sum + n | _ => sum end) 0 h).

  Definition map_sum m := ([^Nat.add map] _ ↦ n ∈ m, n).

  (* The sub-map where all keys are less than [l] *)
  Definition map_take l m := (filter (λ '(k, _), Nat.lt k l) m).

  (* evaluating history leads us to the physical value. *)
  Definition eval h v:= ∃ (n: nat), #n = v ∧ (wsum h + n)%nat = dsum h .

  (* For every prefix of history, the sum of available tokens is greater than
   * that of all withdrawals. *)
  Definition settled (h: state) (m__w: gmap nat nat): Prop :=
    ∀ i, wsum (take i h) ≤ map_sum (map_take i m__w).

  Definition full h: iProp Σ :=
    "auth" ∷ ghost_map_auth γ (DfracOwn 1) (to_auth h) ∗
    ∃ (m__w: gmap nat nat),
      "frags" ∷ ([∗ map] k ↦ n ∈ m__w, ghost_map_elem γ k (DfracOwn 1) n) ∗
      "%settled" ∷ ⌜ settled h m__w ⌝.

  Definition prot : LocationProtocol state :=
    {| p_full := λ (h : state) v, (⌜ eval h v ⌝ ∗ ⎡ full h ⎤)%I;
      p_read := λ (h : state) v, ⌜ eval h v ⌝%I;
      p_pers := λ (h : state) v, ⎡ gmap_token γ (length h) ⎤%I;
      p_bumper h := h |}.

  (* auxiliary lemmas *)
  Lemma to_auth_lookup_length_None h:
    to_auth h !! length h = None.
  Proof.
    rewrite lookup_omap bind_None.
    left.
    rewrite lookup_map_seq_None.
    lia.
  Qed.

  Lemma to_auth_snoc_insert h n:
    <[ length h := n ]> (to_auth h) = to_auth (h ++ [inl n]).
  Proof.
    rewrite {2}/to_auth map_seq_snoc (omap_insert_Some _ _ _ _ n); last done.
    f_equal.
  Qed.

  Lemma to_auth_snoc_noop h n:
    to_auth h = to_auth (h ++ [inr n]).
  Proof.
    rewrite {2}/to_auth map_seq_snoc omap_insert_None /=; last done.
    rewrite -omap_delete delete_id; last (apply lookup_map_seq_None; lia).
    done.
    Qed.

  Lemma to_auth_dsum h:
    dsum h = map_sum (to_auth h).
  Proof.
    rewrite /dsum /map_sum.
    induction h  as [ | [ n | n ] h IH ] using rev_ind.
    - rewrite /to_auth omap_empty big_opM_empty //.
    - rewrite -to_auth_snoc_insert foldl_snoc.
      rewrite big_opM_insert; last apply to_auth_lookup_length_None.
      lia.
    - rewrite -to_auth_snoc_noop foldl_snoc.
      lia.
  Qed.

  Lemma to_auth_lookup h i:
    to_auth h !! i = (h !! i) ≫= (λ x, match x with inl n => Some n | _ => None end).
  Proof.
    rewrite /to_auth lookup_omap lookup_map_seq_0 //.
  Qed.

  Lemma map_sum_proper:
    Proper ((⊆) ==> (≤)) map_sum.
  Proof.
    rewrite /Proper => m1 m2 ?.
    rewrite -(map_difference_union m1 m2) //.
    rewrite /map_sum big_opM_union; last by apply map_disjoint_difference_r1.
    lia.
  Qed.

  Lemma map_take_proper:
    Proper ((≤) ==> (⊆@{gmap nat nat}) ==> (⊆@{gmap nat nat})) map_take.
  Proof.
    rewrite /Proper => i1 i2 ? m1 m2 ?.
    apply map_subseteq_spec. intros ??.
    rewrite !map_lookup_filter_Some.
    intros [? ?].
    split; last lia.
    by eapply lookup_weaken.
  Qed.

  Lemma map_sum_take_le_all m i:
    map_sum (map_take i m) ≤ map_sum m.
  Proof. apply map_sum_proper, map_filter_subseteq. Qed.

  Lemma settled_deposit h m__w n:
    settled h m__w → settled (h ++ [inl n]) m__w.
  Proof.
    intros Hsettled i.
    etrans; last apply Hsettled.
    destruct (decide (i ≤ length h)).
    - rewrite take_app_le //.
    - rewrite take_ge; last (rewrite length_app /=; lia).
      rewrite /wsum foldl_snoc /=.
      rewrite take_ge //.
      lia.
  Qed.

  Lemma settled_withdraw h m__w n k:
    m__w !! k = None →
    k < length h →
    settled h m__w →
    settled (h ++ [inr n]) (<[k := n]> m__w).
  Proof.
    intros ?? Hsettled i.
    destruct (decide (i ≤ length h)).
    - rewrite take_app_le //.
      etrans; first apply Hsettled.
      apply map_sum_proper, map_take_proper, insert_subseteq; done.
    - rewrite take_ge; last (rewrite length_app /=; lia).
      rewrite /wsum foldl_snoc /=.
      rewrite /map_take map_filter_insert_True; last lia.
      rewrite /map_sum big_opM_insert; last by rewrite map_lookup_filter_None; left.
      rewrite (comm Nat.add).
      apply Nat.add_le_mono_l.
      etrans; last apply Hsettled.
      rewrite take_ge //.
      lia.
  Qed.

  Lemma map_take_take_min i j m:
    map_take i (map_take j m) = map_take (i `min` j) m.
  Proof. rewrite /map_take map_filter_filter. apply map_filter_ext. intros. lia. Qed.

  Lemma settled_crash h__c h m__w:
    h__c ⊑ h →
    settled h m__w →
    settled h__c (map_take (length h__c) m__w).
  Proof.
    intros [h' ->] Hsettled i.
    rewrite map_take_take_min.
    etrans; last apply Hsettled.
    destruct (decide (i ≤ length h__c)).
    - rewrite Nat.min_l //.
      rewrite take_app_le //.
    - rewrite Nat.min_r; last lia.
      rewrite take_app_le //.
      rewrite ?take_ge //; try lia.
  Qed.

  Lemma to_auth_crash h__c h:
    h__c ⊑ h →
    map_take (length h__c) (to_auth h) = to_auth h__c.
  Proof.
    intros. apply map_eq => i.
    rewrite map_lookup_filter !to_auth_lookup.
    destruct (decide (i < length h__c)).
    - rewrite -?(prefix_lookup_lt h__c h) //.
      destruct (h__c !! i) as [ [ | ] | ]; rewrite /= ?option_guard_True //.
    - rewrite (lookup_ge_None_2 h__c i); last lia. simpl.
      destruct (h !! i) as [ [ | ] | ]; rewrite /= ?option_guard_False //.
  Qed.

  #[global] Instance prot_cond ℓ : ProtocolConditions ℓ prot.
  Proof.
    split; try apply _.
    - intros h v. rewrite /prot /=.
      iSplit.
      + iIntros "[$ $] $".
      + iIntros "[? impl]". by iApply "impl".
    - rewrite /prot /=.
      iIntros "_" (h__p v__p h__f v__f) "% tok [%Heval full]".
      iDestruct "full" as "[auth (%m__w & frags & %Hsettled)]".
      iSplit.
      + iMod (ghost_map_auth_elems_token_nextgen (length h__f)
               with "auth frags tok") as "NG".
        { by apply prefix_length. }
        iModIntro. iApply nextgen_flush_nextgen. iModIntro. iIntros "_".
        iDestruct "NG" as "(auth & frags & tok)".
        iFrame.
        iSplitR; first done.
        iSplitL "auth".
        (* TODO: make [ghost_map] lemmas use [map_take] as well. *)
        { rewrite -{2}(to_auth_crash h__f h__f) //. }
        iPureIntro.
        by eapply settled_crash.
      + iIntros (h__c v__c) "!> % % %".
        iMod (ghost_map_auth_elems_token_nextgen (length h__c)
               with "auth frags tok") as "NG".
        { by apply prefix_length. }
        iModIntro. iApply nextgen_flush_nextgen. iModIntro. iIntros "_".
        iDestruct "NG" as "(auth & frags & tok)".
        iFrame.
        iSplitR; first done.
        iSplitL "auth".
        (* TODO: make [ghost_map] lemmas use [map_take] as well. *)
        { rewrite -(to_auth_crash h__c h__f) //. }
        iPureIntro.
        eapply (settled_crash h__c h__f); done.
    - rewrite /prot /=. by iIntros (???) "!>".
  Qed.
End bank_protocol.

Section bank_spec.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ, !gen_mapG nat Σ Ω}.

  (** Interface assertions. *)
  Definition is_bank ℓ γ: dProp Σ := ℓ ↦_AT^{prot γ} [ [] ] ∗ persist_lb ℓ (prot γ) [].
  Definition receipt γ (n: nat): dProp Σ :=
    ⎡ ∃ k p, ⌜ (k < p)%nat ⌝ ∗ ghost_map_elem γ k (DfracOwn 1) n ∗ gmap_rely γ p ⎤.

  Lemma wp_init:
    {{{ emp }}}
      init #()
  {{{ γ ℓ, RET #ℓ; is_bank ℓ γ }}}.
  Proof.
    rewrite /init.
    iIntros (Φ) "_ HΦ".
    wp_pures.
    rewrite wp_wpc. iApply fupd_wpc.
    iMod (gmap_alloc_empty) as (γ) "[auth tok]".
    rewrite -wp_wpc.
    iModIntro.
    wp_apply (wp_alloc_at #0 [] (prot γ) with "[$auth $tok]").
    { iSplit; first by iExists 0.
      iExists ∅.
      rewrite big_sepM_empty.
      iPureIntro.
      split; first done.
      intros ?.
      rewrite take_nil /wsum /=.
      lia. }
    iIntros (ℓ) "#mapsto".
    wp_pures.
    wp_apply (wp_flush_lb ℓ (prot γ) []).
    { by iApply (mapsto_at_store_lb _ _ []). }
    iIntros "[_ persistLb]".
    wp_pures.
    wp_apply (wp_fence_sync).
    iModIntro.
    wp_pures.
    iModIntro.
    iApply "HΦ".
    iFrame "∗#".
  Qed.

  Variable (ℓ: loc) (γ: gname).

  Lemma receipt_nextgen n:
    receipt γ n ⊢ <NG> receipt γ n.
  Proof.
    rewrite /receipt.
    iIntros "H".
    iDestruct "H" as (???) "[elem rely]".
    iDestruct (gmap_elem_rely_nextgen with "elem rely") as "H"; first done.
    iModIntro.
    by iDestruct "H" as "[$ $]".
  Qed.
  
  Lemma deposit_update n h:
    full γ h ==∗ full γ (h ++ [inl n]) ∗ ghost_map_elem γ (length h) (DfracOwn 1) n.
  Proof.
    iIntros "[auth (%m__w & frags & %Hsettled)]".
    iMod (ghost_map_insert (length h) n with "auth") as "[auth $]".
    { apply to_auth_lookup_length_None. }
    rewrite to_auth_snoc_insert.
    iFrame.
    iPureIntro.
    by apply settled_deposit.
  Qed.

  Lemma withdraw_impl n (v: nat) h:
    eval h #v →
    ⎡ full γ h ⎤ -∗
    receipt γ n -∗
    ⎡ full γ (h ++ [inr n]) ⎤ ∗ ⌜ n ≤ v ⌝.
  Proof.
    rewrite /full -to_auth_snoc_noop.
    iIntros (Heval) "[auth (%m__w & frags & %Hsettled)] (% & % & % & frag & _)".
    rewrite embed_big_sepM.
    iAssert ⌜ m__w !! k = None ⌝%I as "%".
    { destruct (m__w !! k) as [ | ] eqn:Heq; last done.
      iPoseProof (big_sepM_lookup _ _ k with "frags") as "frag'"; first done.
      by iPoseProof (ghost_map_elem_valid_2 with "frag frag'") as "[% _]". }
    iPoseProof (big_sepM_insert with "[$frags $frag]") as "frags"; first done.
    rewrite -embed_big_sepM.
    iPoseProof (gen_maps.ghost_map_lookup_big with "auth frags") as "%Hsub".
    assert (k < length h).
    { assert (to_auth h !! k = Some n) as Hlook.
      { eapply lookup_weaken; last done. rewrite lookup_insert decide_True //. }
      rewrite to_auth_lookup in Hlook.
      destruct (h !! k) as [ | ] eqn:Heq; simpl in Hlook; last done.
      apply lookup_lt_Some in Heq. done. }
    assert (n ≤ v).
    { destruct Heval as (? & ? & Heval).
      simplify_eq.
      rewrite to_auth_dsum in Heval.
      (* pose proof (to_auth_dsum h) as Hdsum. *)
      apply map_sum_proper in Hsub.
      rewrite /map_sum big_opM_insert in Hsub; last done.
      unfold map_sum in Heval.
      rewrite -Heval in Hsub.
      assert (wsum h ≤ map_sum m__w); last (unfold map_sum in *; lia).
      specialize (Hsettled (length h)).
      rewrite ?take_ge // in Hsettled.
      etrans; first apply Hsettled.
      apply map_sum_take_le_all. }
    iFrame.
    iSplit; last done.
    iPureIntro. by apply settled_withdraw.
  Qed.

  Lemma wp_deposit n:
    {{{ is_bank ℓ γ }}}
      deposit ℓ #n
    {{{ RET #(); receipt γ n }}}.
  Proof.
    rewrite /is_bank /deposit.
    iIntros (Φ) "#[mapsto _] HΦ".
    wp_pures.
    wp_apply (wp_faa
                (λ σ_l n_l σ_t, ⎡ ghost_map_elem γ (length σ_l) (DfracOwn 1) n ⎤ ∗ ⌜(length σ_l < length σ_t)%nat⌝ ∗ seen_state ℓ σ_l)%I
                (λ σ_l (n_l: Z), ⌜ eval σ_l #n_l ⌝ ∗ ⎡ full γ σ_l ⎤: dProp Σ)%I
                [] [] ℓ (prot γ)).
    { iFrame "mapsto".
      iIntros (σ_l n_l) "_".
      iSplitR.
      { iIntros (??) "!> (% & % & %)". by iExists _. }
      iExists (σ_l ++ [inl n]).
      iSplitR.
      { iIntros "!> _". iPureIntro. by apply prefix_app_r. }
      iSplitR.
      { iIntros (σ_n v_n) "_ [_ full] disj".
        iDestruct "full" as "[auth _]".
        iDestruct "disj" as "[[_ [auth' _]] | [_ (% & % & % & [_ [auth' _]])]]";
          iDestruct (ghost_map_auth_valid_2 with "[$] [$]") as %[? _]; done. }
      iSplitR.
      { iIntros "!> [%Heval full]". by iFrame. }
      iIntros "#seen [(%n_l' & % & %) full]".
      simplify_map_eq.
      iMod (deposit_update n σ_l with "full") as "[full frag]".
      iModIntro.
      iFrame "∗#".
      iPureIntro.
      rewrite length_app /=.
      split; last lia.
      exists (n_l' + n).
      split.
      - f_equal. by rewrite Nat2Z.inj_add.
      - unfold dsum, wsum in *. rewrite !foldl_snoc /=. lia. }
    iIntros (σ_l σ_t n_l) "[Hfence #mapsto']".
    wp_pures.
    iDestruct "Hfence" as "(>frag & % & seen)".
    wp_apply (wp_flush_xchg ℓ (prot γ) with "[$seen frag]"); last first.
    {  iIntros "receipt".
       wp_pures.
       iApply (wp_fence_sync' with "[$]").
       iNext. iIntros "[_ receipt]". by iApply "HΦ". }
    iSplitR; first by iNamed "mapsto".
    iSplitR.
    { iApply (mapsto_at_store_lb with "mapsto'"). }
    iIntros (v) "!> $".
    iIntros (σ_old v_old) "!>".
    iSplit.
    - iIntros (?) "tok".
      rewrite /prot /=.
      iMod (gmap_token_strengthen (length σ_t) with "tok") as "[$ #rely]".
      { by apply prefix_length. }
      iModIntro.
      iIntros (v_xchg) "!> $".
      iFrame "∗#".
      by iPureIntro.
    - iIntros (?) "token".
      rewrite /prot /=.
      iMod (gmap_token_strengthen (length σ_old) with "token") as "[$ #rely]"; first done.
      iModIntro.
      iIntros (v_xchg) "!> $".
      iFrame "∗#".
      iPureIntro.
      eapply Nat.lt_le_trans; first done.
      by apply prefix_length.
  Qed.

  Lemma wp_withdraw n:
    {{{ is_bank ℓ γ ∗ receipt γ n }}}
      withdraw ℓ #n
      {{{ (v: Z), RET #v; ⌜ (0 ≤ v)%Z ⌝ }}}.
  Proof.
    rewrite /withdraw.
    iIntros (Φ) "[[#mapsto _] receipt] HΦ".
    wp_pures.
    wp_apply (wp_faa
                (λ σ_l n_l σ_t, ⌜(0 ≤ n_l)%Z⌝)%I
                (λ σ_l (n_l: Z), ⌜ eval σ_l #n_l ⌝ ∗ ⎡ full γ σ_l ⎤: dProp Σ)%I
                [] [] with "[$mapsto receipt]"); last first.
    { iIntros (? σ_t n_l) "[>%Hf _]".
      wp_pures.
      iModIntro.
      by iApply "HΦ". }
    iIntros (σ_l n_l) "_".
    iSplitR "receipt".
    { iIntros (??) "!> (% & % & %)". by iExists _. }
    iExists (σ_l ++ [inr n]).
    iSplitR.
    { iIntros "!> _". iPureIntro. by apply prefix_app_r. }
    iSplitR.
    { iIntros (σ_n v_n) "_ [_ full1] disj".
      iDestruct "full1" as "[auth1 _]".
      iDestruct "disj" as "[[_ [auth2 _]] | [_ (% & % & % & [_ [auth2 _]])]]";
        iDestruct (ghost_map_auth_valid_2 with "auth1 auth2") as %[Hv _]; done. }
    iSplitR.
    { iIntros "!> [%Heval full]". by iFrame. }
    iIntros "#seen [(%n_l' & % & %) full] !>".
    simplify_map_eq.
    iDestruct (withdraw_impl n n_l' σ_l with "full receipt") as "[fullσt %Hnv]".
    { exists n_l'. done. }
    iFrame "∗#".
    iPureIntro.
    split; last lia.
    exists (n_l' - n).
    split.
    - f_equal. by rewrite Nat2Z.inj_sub.
    - unfold wsum, dsum in *. rewrite !foldl_snoc /=. lia.
  Qed.
End bank_spec.
