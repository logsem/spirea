From iris.proofmode Require Import tactics.
From iris.bi Require Import monpred.
From iris.program_logic Require weakestpre.
From iris.algebra Require Import gmap.

From self.base Require Import primitive_laws.
From self.lang Require Import lang.
From self.high Require Import dprop.

From self.lang Require Export notation lang lemmas tactics syntax.
From self.algebra Require Import view.
From self.base Require Import primitive_laws class_instances adequacy.
From self.high Require Import proofmode wpc_proofmode.
From self.high Require Import weakestpre_exp weakestpre_at weakestpre_na locations.
From self.high.modalities Require Import fence.
From self.high Require Import protocol no_buffer abstract_state_instances.

Section FAA_Axiom.
  Context `{AbstractState ST}.
  Context `{!nvmG Σ}.

  Implicit Types (ℓ : loc) (s : ST) (prot : LocationProtocol ST).

  Definition faa: expr :=
    rec: "faa" "l" "v_add" :=
      let: "v_old" := !_AT "l" in
      if: (CAS "l" "v_old" ("v_old" + "v_add")) then
        "v_old"
      else
        "faa" "l" "v_add".

  Lemma wp_faa Q R next ℓ prot `{!ProtocolConditions prot} ss (v_add: Z) st E:
    {{{
      ℓ ↦_AT^{prot} (ss) ∗
      (∀ s_l (v_l: Z) s_p v_p, ∃ P,
        (  (* The state we write fits in the history. *)
           (<obj> (prot.(p_full) s_l #v_l -∗ ⌜ s_l ⊑ next s_l ⌝)) ∗
           (∀ s_n v_n, ⌜ s_l ⊑ s_n ⌝ -∗ prot.(p_full) s_l #v_l -∗
                       prot.(p_full) s_n v_n ∨
                         (prot.(p_read) s_n v_n ∧
                          ∃ s_n' v_n', ⌜ s_n ⊑ s_n' ⌝ ∗ prot.(p_full) s_n' v_n') -∗
                       ⌜ next s_l ⊑ s_n ⌝) ∗
           (* Extract the objective knowledge from [p_pers] *)
           (<obj> (prot.(p_pers) s_p v_p -∗ <obj> P ∗ (P -∗ prot.(p_pers) s_p v_p))) ∗
           (* Extract from the location we load. *)
           (<obj> (prot.(p_full) s_l #v_l ∗ P -∗ prot.(p_read) s_l #v_l ∗ R s_l v_l)) ∗
           (* Establish the invariant for the value we store. *)
           (R s_l v_l ==∗ prot.(p_full) (next s_l) #(v_l + v_add) ∗ <obj> P ∗ Q s_l v_l)
        ))
    }}}
      FAA #ℓ #v_add @ st; E
    {{{ (v_l: Z) s_l, RET #v_l;
        <fence> Q s_l v_l ∗ ℓ ↦_AT^{prot} (ss ++ [next s_l])
    }}}.
    Proof.
  Admitted.
End FAA_Axiom.

Section Bank.
  Context `{!nvmG Σ}.

  Variables (ℓ: loc) (γ: gname).

  (* axiomatized section begins *)
  Definition trans := (gmap nat nat) → (gmap nat nat).
  Definition promise := trans → Prop.
  Variables (nextgen: dProp Σ → dProp Σ) (token: gname → promise → iProp Σ) (rely: gname → promise → iProp Σ).

  Instance rely_persistent prom: Persistent (rely γ prom).
  Proof. Admitted.

  Hypothesis (token_strengthen: ∀ (prom1 prom2: promise), (∀ tr, prom2 tr → prom1 tr) → token γ prom1 ==∗ token γ prom2).
  Hypothesis (token_bupd_rely: ∀ (prom: promise), token γ prom ==∗ token γ prom ∗ rely γ prom).
  Hypothesis (rely_weaken: ∀ (prom1 prom2: promise), (∀ tr, prom1 tr → prom2 tr) → rely γ prom1 -∗ rely γ prom2).
  (* axiomatized section ends *)

  Definition deposit: expr :=
    λ: "n",
      FAA #ℓ "n" ;;
      Flush #ℓ ;;
      FenceSync.

  Definition withdraw: expr :=
    λ: "n",
      let: "v" := FAA #ℓ (- "n") in
      (* Flush #ℓ ;; *)
      (* FenceSync ;; *)
      "v".

  (* abstract state *)
  Program Instance list_abstract_state T `{!EqDecision T, Countable T} : AbstractState (list T) :=
    { abs_state_relation := prefix }.

  Notation state := (list (nat + nat)).

  (* ghost resource *)
  Context `{!ghost_mapG Σ nat nat}.

  Definition to_auth (h: state): gmap nat nat :=
    omap (λ x, match x with inl n => Some n | _ => None end) $ map_seq 0 h.

  Notation dsum h :=
    (foldl (λ sum x, match x with inl n => sum + n | _ => sum end) 0 h).

  Notation wsum h :=
    (foldl (λ sum x, match x with inr n => sum + n | _ => sum end) 0 h).

  Definition state_match h v: dProp Σ :=
    ⌜ ∃ (n: nat), #n = v ∧ (wsum h + n)%nat = dsum h ⌝.

  Definition full_pred h: iProp Σ :=
    ghost_map_auth γ (DfracOwn 1) (to_auth h) ∗
    ∃ (m__w: gmap nat nat), ([∗ map] k ↦ n ∈ m__w, ghost_map_elem γ k (DfracOwn 1) n) ∗
                          ⌜ wsum h = [^(Nat.add) map] n ∈ m__w, n ⌝.

  Definition map_trans k (m: gmap nat nat) :=
    filter (λ '(k', _), k' ≤ k) m.

  Definition map_prom k tr :=
    ∃ k', k' ≥ k ∧ tr = map_trans k'.

  (* protocol for [ℓ] *)
  Definition prot : LocationProtocol state :=
    {| p_full := λ (h : state) v, (state_match h v ∗ ⎡ full_pred h ⎤ )%I;
      p_read := λ (h : state) v, state_match h v;
      p_pers := λ (h : state) v, ⎡ token γ (map_prom (length h - 1)) ⎤%I;
      p_bumper h := h |}.
  Global Instance prot_cond : ProtocolConditions prot.
  Proof.
    split; try done; try solve_proper; try apply _.
    - intros.
      rewrite /prot /=.
      rewrite bi.equiv_entails.
      split.
      { iIntros "[% ?]". iFrame "∗%". done. }
      { iIntros "[% H]". iFrame "%".
        iDestruct ("H" with "[//]") as "[_ $]". }
    - rewrite /prot /=.
      iIntros (??) "token".
      admit.
    - iIntros.
      iApply post_crash_flush_pure.
      done.
  Admitted.

  Definition is_bank: dProp Σ := ℓ ↦_AT^{prot} [ [] ].
  Definition receipt (n: nat): dProp Σ := ⎡ ∃ k, ghost_map_elem γ k (DfracOwn 1) n ∗ rely γ (map_prom k) ⎤.

  (* auxiliary lemmas *)

  Lemma to_auth_lookup_length_None h:
    to_auth h !! length h = None.
  Proof.
    rewrite /to_auth.
    rewrite lookup_omap.
    rewrite bind_None.
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
    rewrite -omap_delete delete_notin; last (apply lookup_map_seq_None; lia).
    done.
    Qed.

  Lemma to_auth_dsum h:
    dsum h = [^Nat.add map] n ∈ to_auth h, n.
  Proof.
    induction h  as [ | [ n | n ] h IH ] using rev_ind.
    - rewrite /to_auth omap_empty big_opM_empty //.
    - rewrite -to_auth_snoc_insert foldl_snoc.
      rewrite big_opM_insert; last apply to_auth_lookup_length_None.
      lia.
    - rewrite -to_auth_snoc_noop foldl_snoc.
      lia.
  Qed.

  Lemma full_pred_deposit_bupd n h:
    full_pred h ==∗ full_pred (h ++ [inl n]) ∗ ghost_map_elem γ (length h) (DfracOwn 1) n.
  Proof.
    rewrite /full_pred.
    iIntros "[auth (% & tokens & %)]".
    iMod (ghost_map_insert (length h) n with "auth") as "[auth $]".
    { apply to_auth_lookup_length_None. }
    rewrite to_auth_snoc_insert.
    iFrame "auth".
    iModIntro.
    iExists m__w.
    iFrame.
    rewrite foldl_snoc //.
  Qed.

  Lemma full_pred_withdraw n (v: nat) h:
    state_match h #v -∗ ⎡ full_pred h ⎤ -∗ receipt n -∗ ⎡ full_pred (h ++ [inr n]) ⎤ ∗ ⌜ n ≤ v ⌝.
  Proof.
    rewrite /full_pred -to_auth_snoc_noop.
    iIntros "%steq [auth (% & tokens & %eq)] (%k & frag & _)".
    simplify_eq.
    rewrite embed_big_sepM.
    iAssert ⌜ m__w !! k = None ⌝%I as "%".
    { destruct ((m__w !! k)) as [ | ] eqn:?; last done.
      iPoseProof (big_sepM_lookup _ _ k with "tokens") as "frag'"; first done.
      iPoseProof (ghost_map_elem_valid_2 with "[$] [$]") as "[% _]".
      done. }
    iPoseProof (big_sepM_insert with "[$tokens $frag]") as "tokens"; first done.
    rewrite -embed_big_sepM.
    iPoseProof (ghost_map_lookup_big with "[$] [$]") as "%".
    iFrame.
    iSplit.
    { iExists (<[ k := n ]> m__w).
      iFrame.
      iPureIntro.
      rewrite foldl_snoc /=.
      rewrite big_opM_insert; last done.
      lia. }
    pose proof (to_auth_dsum h) as bigeq.
    rewrite -(map_difference_union (<[k:=n]> m__w) (to_auth h)) in bigeq; last done.
    rewrite big_opM_union in bigeq; last by apply map_disjoint_difference_r.
    iPureIntro.
    rewrite big_opM_insert in bigeq; last done.
    destruct steq as (? & ? & ?).
    simplify_eq.
    lia.
  Qed.

  Lemma map_prom_strengthen k1 k2:
    k1 ≤ k2 → ∀ tr, map_prom k2 tr → map_prom k1 tr.
  Proof.
    rewrite /map_prom.
    intros ??(k' & ? & ?).
    exists k'.
    split; last done.
    lia.
  Qed.

  Lemma wp_deposit n:
    {{{ is_bank }}}
      deposit #n
    {{{ RET #(); receipt n }}}.
  Proof.
    rewrite /is_bank.
    iIntros (?) "#is_bank HΦ".
    wp_pures.
    wp_bind (FAA _ _).
    iApply (wp_faa
              (λ h _, ⎡ ghost_map_elem γ (length h) (DfracOwn 1) n⎤)%I
              (λ h v, state_match h #v ∗ ⎡ full_pred h ⎤)%I
              (λ h, h ++ [inl n]) _ prot).
    { iSplitL; first iFrame "#".
      iIntros.
      iExists (True)%I.
      iSplitL "".
      { iIntros "!> _".
        iPureIntro.
        by eexists. }
      iSplitL "".
      { iIntros (???) "[_ [full1 _]] [[_ [full2 _]] | [_ (% & % & % & [_ [full2 _]])]]";
          by iPoseProof (ghost_map_auth_valid_2 with "full1 full2") as "[%frac _]". }
      iSplitL "".
      { iIntros "!> pers".
        iSplitL ""; first by iModIntro.
        iIntros. iFrame. }
      iSplitL "".
      { iIntros "!> [full _]".
        iSplit.
        - iDestruct "full" as "[? _]".
          done.
        - iFrame. }
      iIntros "[%steq full]".
      iMod (full_pred_deposit_bupd n with "full") as "[full receipt]".
      iModIntro.
      iFrame.
      iSplitPure.
      { rewrite ?foldl_snoc.
        destruct steq as (?n' & ? & ?).
        simplify_eq.
        exists (n' + n).
        split; first rewrite Nat2Z.inj_add //.
        lia. }
      by iModIntro.
    }
    iModIntro.
    iIntros (??) "[frag #mapsto]".
    iPoseProof (post_fence_flush_free with "frag") as "frag".
    wp_pures.
    wp_bind (Flush _).
    iPoseProof (mapsto_at_store_lb with "mapsto") as "#lb".
    iApply (weakestpre_exp.wp_flush_lb _ _ _ _ _ ⎡ rely γ (map_prom $ length s_l) ⎤%I with "[$lb]").
    { iSplit.
      { iDestruct "is_bank" as (???????) "H".
        iNamed "H".
        iAssumption. }
      iIntros "!>" (???).
      iExists (True)%I.
      iSplit; first by iIntros "_ !>!>".
      iIntros "_".
      rewrite /p_pers /prot //=.
      iSplit.
      - iIntros "[% %eq] pers".
        iMod (token_strengthen _ (map_prom (length s_l)) with "pers").
        { apply map_prom_strengthen.
          assert (length_eq: length s_l + length [@inl nat nat n] = length s_p + length k).
          { rewrite -?app_length. by f_equiv. }
          simpl in length_eq.
          lia. }
        rewrite app_length //=.
        replace (_ + 1 - 1) with (length s_l) by lia.
        iMod (token_bupd_rely with "[$]") as "[? ?]".
        by iFrame.
      - iIntros "[% ->] pers".
        iMod (token_bupd_rely with "[$]") as "[$ rely]".
        iModIntro.
        iApply (rely_weaken with "rely").
        apply map_prom_strengthen.
        rewrite ?app_length //=.
        lia.
    }
    iIntros "!> post_fence_sync".
    wp_pures.
    iApply (weakestpre_exp.wp_fence_sync _ prot with "post_fence_sync").
    iIntros "!> [_ rely]".
    iApply "HΦ".
    iExists (length s_l).
    iFrame.
  Qed.

  Lemma wp_withdraw n:
    {{{ is_bank ∗ receipt n }}}
      withdraw #n
    {{{ (v: Z), RET #v; ⌜ (0 ≤ v)%Z ⌝ }}}.
  Proof.
    rewrite /is_bank.
    iIntros (?) "[#is_bank receipt] HΦ".
    wp_pures.
    wp_bind (FAA _ _).
    iApply (wp_faa
              (λ h v, state_match h #v)%I
              (λ h v, state_match h #v ∗ ⎡ full_pred h ⎤)%I
              (λ h, h ++ [inr n]) _ prot with "[receipt]").
    { iSplitL ""; first iFrame "#".
      iIntros.
      iExists (True)%I.
      iSplitL "".
      { iIntros "!> _".
        iPureIntro.
        by eexists. }
      iSplitL "".
      { iIntros (???) "[_ [full1 _]] [[_ [full2 _]] | [_ (% & % & % & [_ [full2 _]])]]";
          by iPoseProof (ghost_map_auth_valid_2 with "full1 full2") as "[%frac _]". }
      iSplitL "".
      { iIntros "!> pers".
        iSplitL ""; first by iModIntro.
        iIntros. iFrame. }
      iSplitL "".
      { iIntros "!> [full _]".
        iSplit.
        - iDestruct "full" as "[? _]".
          done.
        - iFrame. }
      iIntros "[%eq full]".
      destruct eq as (n' & ? & ?).
      simplify_eq.
      iPoseProof (full_pred_withdraw with "[%] full receipt") as "[full %]".
      { by exists n'. }
      iFrame "%".
      iModIntro.
      iFrame.
      rewrite Z.add_opp_r.
      iSplit.
      { iPureIntro.
        rewrite -Nat2Z.inj_sub; last done.
        eexists.
        split; first done.
        rewrite ?foldl_snoc.
        lia. }
      iSplit; first by iModIntro.
      iPureIntro.
      by eexists.
    }
    iIntros "!>" (??) "[post #mapsto]".
    iPoseProof (post_fence_flush_free with "post") as "(% & % & %)".
    wp_pures.
    iModIntro.
    iApply "HΦ".
    simplify_eq.
    iPureIntro.
    lia.
  Qed.

  Lemma receipt_nextgen n:
    receipt n ⊢ nextgen $ receipt n.
  Proof. Abort.

  Lemma is_bank_nextgen:
    is_bank ⊢ nextgen is_bank.
  Proof. Abort.

  Lemma receipt_split n1 n2:
    receipt n1 ∗ receipt n2 ⊣⊢ receipt (n1 + n2).
  Proof. Abort.

End Bank.
