(*** HighSpirea Generational Resources. *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gset.
From iris.bi.lib Require Import fractional.
From iris_named_props Require Import named_props.

From self Require Import extra encode_relation.
From self.lang Require Import lang.

From self.base Require Export generational_resources if_rec.
From self.nextgen Require Import gen_ing nextgen_promises.
From self.high.resources Require Export
  gen_ghost_map gen_ghost_map_map gen_alocs gen_predicates auth_map_map.
From self.high.lib Require Export bumpers abstract_state.
From self.algebra Require Import view.

(** Typeclasses for highSpirea logic. *)
Class nvmHighGpreS Σ Ω `{!nvmBaseGS Σ Ω} := {
  nvmHighGpreS_predicates :: predicatesGpreS Σ Ω;
  nvmHighGpreS_bumpers :: ghost_mapGpreS loc (positive → option positive) Σ Ω;
  nvmHighGpreS_abs_histories :: ghost_map_mapGpreS loc time positive Σ Ω;
  nvmHighGpreS_phys_histories :: auth_map_mapR_inG (leibnizO message) Σ Ω;
  nvmHighGpreS_na_views :: ghost_mapGpreS loc view Σ Ω;
  nvmHighGpreS_orders :: ghost_mapGpreS loc (relation2 positive) Σ Ω;
  nvmHighGpre_locs :: gen_alocsR_inG Σ Ω;
}.

Class nvmHighGS Σ Ω `{!nvmBaseGS Σ Ω} := NvmHighG {
  #[local] nvmHighGS_inG :: nvmHighGpreS Σ Ω;
  full_predicates_name : gname;
  read_predicates_name : gname;
  pers_predicates_name : gname;
  abs_history_name : gname;
  (* resharing [phy_history] for atomic locations *)
  phy_history_name : gname;
  non_atomic_views_gname : gname;
  preorders_name : gname;
  exclusive_locs_name : gname;
  shared_locs_name : gname;
  new_locs_name : gname;
  bumpers_name : gname;
}.

(** we proceed to define assertions that needs to know the [gen_inG] typeclass instances. *)
Section location_sets.
  Context `{nvmHighGS}.
  Implicit Types (locs : gset loc) (ℓ : loc).

  Definition is_at_loc ℓ : iProp Σ :=
    gen_alocs_frag shared_locs_name {[ ℓ ]}.
  Definition is_na_loc ℓ : iProp Σ :=
    gen_alocs_frag exclusive_locs_name {[ ℓ ]}.
  
  Lemma location_sets_singleton_included {γ} locs ℓ :
    gen_alocs_auth γ locs -∗ gen_alocs_frag γ {[ ℓ ]} -∗ ⌜ ℓ ∈ locs ⌝.
  Proof.
    iNamed 1. iDestruct 1 as "(own_frag & _)".
    iDestruct (gen_own_valid_2 with "own_auth own_frag")
      as %[V%gset_included _]%auth_both_valid_discrete.
    rewrite elem_of_subseteq_singleton.
    done.
  Qed.

  Lemma location_sets_lookup γ locs ℓ :
    ℓ ∈ locs → gen_alocs_frag γ locs -∗ gen_alocs_frag γ {[ ℓ ]}.
  Proof.
    intros.
    iNamed 1.
    iPoseProof (gen_own_mono _ _ (◯ {[ ℓ ]}) with "own_frag") as "own_frag".
    { apply auth_frag_mono. set_solver. }
    iFrame "∗#".
  Qed.
End location_sets.

(* We need a different [offset], that allows us to insert [0] at new locations. *)
Section offset_loc.
  Context `{nvmHighGS}.

  Definition offset_auth (offsets: gmap loc nat): iProp Σ :=
    ∃ (OCV: view),
      "#crashed" ∷ crashed_at_offset OCV ∗
      "newLocs" ∷ gen_alocs_auth new_locs_name (dom offsets) ∗
      "%HLookup" ∷ ⌜ ∀ (ℓ: loc), ℓ ∈ dom offsets → offsets !! ℓ = Some (OCV !!0 ℓ) ⌝.

  Definition offset_loc ℓ (t: nat): iProp Σ :=
    ∃ OCV, crashed_at_offset OCV ∗
           gen_alocs_frag new_locs_name {[ ℓ ]} ∗ ⌜ OCV !!0 ℓ = t ⌝.

  Lemma offset_loc_agree ℓ t1 t2 :
    offset_loc ℓ t1 -∗
    offset_loc ℓ t2 -∗
    ⌜ t1 = t2 ⌝.
  Proof.
    rewrite /offset_loc.
    iIntros "(%OCV & crash & new_locs_frag & %look)".
    iIntros "(%OCV' & crash' & new_locs_frag' & %look')".
    iDestruct (crashed_at_offset_agree with "[$] [$]") as "->".
    iPureIntro.
    congruence.
  Qed.

  Lemma offset_loc_offset_auth_agree ℓ t offsets :
    offset_loc ℓ t -∗
    offset_auth offsets -∗
    ⌜ offsets !! ℓ = Some t ⌝.
  Proof.
    iIntros "(%OCV & crash & new_locs_frag & %look)". iNamed 1.
    iDestruct (crashed_at_offset_agree with "crash crashed") as "<-".
    iDestruct (location_sets_singleton_included with "[$] [$]") as "%Hdom".
    iPureIntro.
    specialize (HLookup ℓ Hdom).
    rewrite look /lookup_zero in HLookup.
    done.
  Qed.

  Lemma offset_loc_crashed_at_offset_agree ℓ t OCV:
    offset_loc ℓ t -∗
    crashed_at_offset OCV -∗
    ⌜ OCV !!0 ℓ = t ⌝.
  Proof.
    iIntros "(% & ? & _ & %) ?".
    iDestruct (crashed_at_offset_agree with "[$] [$]") as %->.
    done.
  Qed.
  
  Lemma offset_auth_insert OCV offsets ℓ:
    ℓ ∉ dom OCV →
    ℓ ∉ dom offsets →
    crashed_at_offset OCV -∗
    offset_auth offsets ==∗
    offset_auth (<[ ℓ := 0 ]> offsets) ∗ offset_loc ℓ 0.
  Proof.
    iIntros (HOCVdom Hoffsetsdom) "crashed'". iNamed 1.
    iDestruct (crashed_at_offset_agree with "crashed crashed'") as %->.
    iMod (gen_alocs_update (dom offsets) ℓ with "newLocs") as "[newLocs frag]".
    iModIntro.
    iSplitL "newLocs".
    - iExists _.
      rewrite dom_insert_L.
      replace ({[ℓ]} ∪ dom offsets) with (dom offsets ∪ {[ℓ]}); last by set_solver.
      iFrame "∗#".
      iPureIntro.
      intros ℓ'.
      destruct (decide (ℓ = ℓ')) as [ <- | ].
      * rewrite lookup_insert_eq lookup_zero_None_zero //.
        by apply not_elem_of_dom.
      * rewrite lookup_insert_ne //.
        intros.
        apply HLookup.
        set_solver.
    - iFrame.
      rewrite lookup_zero_None_zero //.
      by apply not_elem_of_dom.
  Qed.

  #[global] Instance offset_loc_into_nextgen ℓ t:
    IntoNextgen
    (offset_loc ℓ t)
    (if_rec ℓ (∃ tC, offset_loc ℓ tC ∗ ∀ OV OCV, crashed_at_both OV OCV -∗ ⌜ OV !!0 ℓ = t ⌝ ∗ ⌜ OCV !! ℓ = Some (MaxNat tC) ⌝)).
  Proof.
    rewrite /IntoNextgen.
    iDestruct 1 as (OCV) "(offset & newLocs & %)".
    iAssert (rely new_locs_name [#crashed_at_name] gen_alocs_rel (λ _, true))%I as "#rely".
    { by iNamed "newLocs". }
    iModIntro.
    iDestruct "offset" as (OV) "(%trans & picked & offset)".
    iDestruct "rely" as "(_ & % & %trans' & %promise & _ & picked')".
    iPickedInAgree "picked' picked".
    destruct promise as [(OCV' & -> & _) _].
    simpl.
    iIntros (OCV'' HOCVLook) "#crashed #persisted".
    iSpecialize ("newLocs" with "crashed").
    iExists _.
    rewrite /offset_loc.
    simpl.
    iDestruct "crashed" as (OV') "crashed".
    iDestruct (crashed_at_both_agree with "crashed offset") as %[ -> -> ].
    iSplit.
    - iExists OCV'.
      iSplit; first by iExists _.
      iSplit; last done.
      assert (ℓ ∈ dom OCV') by (by apply elem_of_dom).
      iEval (replace ({[ℓ]}) with ({[ℓ]} ∩ dom OCV') by set_solver).
      done.
    - iIntros (??) "crashed'".
      iDestruct (crashed_at_both_agree with "crashed crashed'") as %[ <- <- ].
      simplify_eq.
      iSplit; first done.
      iPureIntro.
      rewrite /lookup_zero.
      destruct HOCVLook as [[?] HOCVLook].
      rewrite ?HOCVLook //.
  Qed.

  Lemma offset_auth_picked_out (OCV': view) offsets:
    picked_out crashed_at_name (crashed_at_trans (OCV')) -∗
    offset_auth offsets -∗
    ⚡==> offset_auth $ max_nat_car <$> restrict (dom offsets) OCV'.
  Proof.
    iIntros "#picked". iNamed 1. iModIntro.
    iDestruct ("crashed") as (OV' t) "[picked'' crashed]".
    iPickedInAgree "picked picked''".
    iAssert (crashed_at_offset OCV')%I as "OCV'".
    { by iExists _. }
    iSpecialize ("newLocs" with "OCV'").
    iExists OCV'.
    iSplit; first done.
    iSplitL "newLocs".
    { rewrite dom_fmap_L restrict_dom_L //. }
    iPureIntro.
    intros ℓ look. rewrite lookup_fmap.
    rewrite dom_fmap_L restrict_dom_L in look.
    rewrite restrict_lookup_elem_of; last set_solver.
    rewrite /lookup_zero.
    assert (ℓ ∈ dom OCV') as [? ->]%elem_of_dom by set_solver.
    done.
  Qed.

End offset_loc.

Opaque offset_auth offset_loc.

Section preorders.
  Context `{nvmHighGS}.
  Implicit Type (preorders : gmap loc (relation2 positive)).
  Context `{Countable ST}.

  Definition own_all_preorders γ preorders :=
    ghost_map_auth γ drop_OCV (DfracOwn 1) preorders.

  Definition know_preorder_loc ℓ (preorder : relation2 ST) : iProp Σ :=
    ℓ ↪[preorders_name, drop_OCV]□ encode_relation preorder.

  Definition lastgen_know_preorder_loc ℓ (preorder : relation2 ST) : iProp Σ :=
    lastgen_ghost_map_elem preorders_name ℓ DfracDiscarded (encode_relation preorder).
  
  Lemma orders_lookup ℓ order1 order2 (orders : gmap loc (relation2 positive)) :
    orders !! ℓ = Some order1 →
    own_all_preorders preorders_name orders -∗
    know_preorder_loc ℓ order2 -∗
    ⌜order1 = encode_relation order2⌝.
  Proof.
    iIntros (look) "auth frag".
    iDestruct (ghost_map_lookup with "auth frag") as "%".
    iPureIntro. congruence.
  Qed.
End preorders.

Opaque own_all_preorders know_preorder_loc.

Section own_bumpers.
  Context `{nvmHighGS} `{AbstractState ST}.
  
  Definition own_all_bumpers γ (encoded_bumpers: gmap loc (positive → option positive)): iProp Σ :=
    ghost_map_auth γ drop_OCV (DfracOwn 1) encoded_bumpers.
  
  Definition know_bumper ℓ (bumper : ST → ST) : iProp Σ :=
    let encodedBumper := encode_bumper bumper in
    ⌜ ∀ s1 s2, s1 ⊑ s2 → bumper s1 ⊑ bumper s2 ⌝ ∗
    ℓ ↪[bumpers_name, drop_OCV]□ encodedBumper.

  Definition lastgen_know_bumper (ℓ : loc) (bumper : ST → ST) : iProp Σ :=
    let encodedBumper := encode_bumper bumper
    in ⌜∀ s1 s2, s1 ⊑ s2 → bumper s1 ⊑ bumper s2⌝ ∗
                 lastgen_ghost_map_elem bumpers_name ℓ DfracDiscarded encodedBumper.
  
  Lemma own_all_bumpers_persist γ encoded_bumpers :
    own_all_bumpers γ encoded_bumpers ==∗
    ghost_map_auth γ drop_OCV DfracDiscarded encoded_bumpers.
  Proof. by iApply ghost_map_auth_persist. Qed.

  Lemma own_all_bumpers_insert (bumpers : gmap loc _) ℓ (bumper : ST → ST)
        `{!Proper ((⊑@{ST}) ==> (⊑))%signature bumper} :
    bumpers !! ℓ = None →
    own_all_bumpers bumpers_name bumpers ==∗
    own_all_bumpers bumpers_name (<[ℓ := encode_bumper bumper]>bumpers) ∗ know_bumper ℓ bumper.
  Proof.
    rewrite /own_all_bumpers. iIntros (look) "auth".
    iMod (ghost_map_insert_persist with "auth") as "[$ #bumper]"; first done.
    iFrame "bumper".
    done.
  Qed.

  Lemma bumpers_lookup ℓ encoded_bumpers bumper :
    own_all_bumpers bumpers_name encoded_bumpers -∗
    know_bumper ℓ bumper -∗
    ⌜ encoded_bumpers !! ℓ = Some (encode_bumper bumper) ⌝.
  Proof.
    iIntros "A [mono F]".
    iDestruct (ghost_map_lookup with "A F") as "$".
  Qed.
End own_bumpers.

Section NAView.
  Context `{nvmHighGS}.

  Definition know_na_view ℓ q (SV : view) : iProp Σ :=
    ℓ ↪[non_atomic_views_gname, drop_OCV_clear]{#q} SV%I.  
  
  Lemma know_na_view_agree ℓ p q V V' :
    know_na_view ℓ q V -∗
    know_na_view ℓ p V' -∗
    ⌜ V = V' ⌝.
  Proof.
    apply: ghost_map_elem_agree.
  Qed.

  Global Instance know_na_view_fractional ℓ V :
    Fractional (λ q, know_na_view ℓ q V).
  Proof. apply _. Qed.

  Global Instance know_na_view_as_fractional ℓ V q :
    AsFractional (know_na_view ℓ q V)
      (λ q, know_na_view ℓ q V) q.
  Proof. apply _. Qed.

  #[global] Instance know_na_view_into_nextgen ℓ q (SV: view):
    IntoNextgen
      (know_na_view ℓ q SV)
      (if_rec ℓ (know_na_view ℓ q ∅)).
  Proof.
    rewrite /IntoNextgen /know_na_view.
    iIntros "know !>" (OCV ?) "#OCV _".
    iDestruct "know" as "[_ know]".
    iApply "know"; first done.
    rewrite elem_of_dom //.
  Qed.
End NAView.
(* so that iDestruct will prioritize fractional lemma over splitting [gen_own] *)
#[global] Opaque know_na_view.

Definition new_hist t (bumper : positive → option positive) (hist : gmap time positive) :=
  omap bumper (map_extra.drop_above t hist).

Section Histories.
  Context `{nvmHighGS}.
  Implicit Types (q: Qp) (ℓ: loc)
    (enc_abs_hist : gmap time positive)
    (abs_hists : gmap loc (gmap time positive)).

  Definition know_phys_hist_msg ℓ t msg : iProp Σ :=
    auth_map_map_frag_singleton histories_rel phy_history_name ℓ t msg.
  
  (** The encoded version of history assertions. *)
  Definition know_full_encoded_history_loc ℓ q enc_abs_hist : iProp Σ :=
    full_entry bumpers_name abs_history_name ℓ (DfracOwn q) enc_abs_hist.

  Definition know_frag_encoded_history_loc ℓ t e : iProp Σ :=
    frag_entry bumpers_name abs_history_name ℓ t e.

  Context `{Countable ST}.
  Implicit Types (abs_hist : gmap time ST).

  (** The decoded version of history assertions. *)
  Definition know_full_history_loc ℓ q abs_hist : iProp Σ :=
    full_entry bumpers_name abs_history_name ℓ (DfracOwn q) (encode <$> abs_hist).

  (* In this definition we store that decoding the stored encoded histry is
  equal to our abstract history. This is weaker than strogin the other way
  around, namely that encoding our history is equal to the stored encoded
  history. Storing this weaker fact makes the definition easier to show. This is
  important for the load lemma where, when we load some state and we want to
  return [store_lb] for the returned state. At that point we can conclude that
  decoding the encoding gives a result but not that the encoding is an encoding
  of some state. *)
  Definition know_frag_history_loc `{Countable ST} ℓ t (σ : ST) : iProp Σ :=
    ∃ eσ, ⌜ decode eσ = Some σ ⌝ ∗ frag_entry bumpers_name abs_history_name ℓ t eσ.

  Global Instance know_full_history_loc_fractional ℓ (abs_hist : gmap nat ST) :
    Fractional (λ q, know_full_history_loc ℓ q abs_hist).
  Proof. apply _. Qed.

  Global Instance know_full_history_loc_as_fractional ℓ (abs_hist : gmap nat ST) q :
    AsFractional (know_full_history_loc ℓ q abs_hist)
      (λ q, know_full_history_loc ℓ q abs_hist) q.
  Proof. apply _. Qed.

  (** Lemmas above history assertions. *)
  Lemma know_full_history_loc_agree ℓ p q abs_hist1 abs_hist2 :
    know_full_history_loc ℓ p abs_hist1 -∗
    know_full_history_loc ℓ q abs_hist2 -∗
    ⌜ abs_hist1 = abs_hist2 ⌝.
  Proof.
    iIntros "[A _]". iIntros "[B _]".
    iDestruct (full_entry_agree with "A B") as %<-%(inj _). done.
  Qed.

  Lemma know_full_history_loc_encode ℓ q abs_hist :
    know_full_history_loc ℓ q abs_hist ⊣⊢
      know_full_encoded_history_loc ℓ q (encode <$> abs_hist).
  Proof. done. Qed.

  Lemma know_frag_history_loc_decode ℓ t s :
    know_frag_encoded_history_loc ℓ t (encode s) -∗
    know_frag_history_loc ℓ t s.
  Proof. iIntros "H". iExists _. iFrame. rewrite decode_encode. done. Qed.

  Lemma full_map_frag_singleton_agree dq ℓ t (s : ST) hists :
    full_map bumpers_name abs_history_name dq hists -∗
    know_frag_history_loc ℓ t s -∗
    ⌜∃ hist enc,
      hists !! ℓ = Some hist ∧ hist !! t = Some enc ∧ decode enc = Some s⌝.
  Proof.
    iIntros "H1 (% & % & H2)".
    iDestruct (full_map_frag_entry with "H1 H2") as %(mi & EQ & hq).
    iPureIntro. eexists _, _. split_and!; done.
  Qed.

  Lemma know_full_encoded_history_lookup q ℓ enc_abs_hist t (s : ST) :
    know_full_encoded_history_loc ℓ q enc_abs_hist -∗
    know_frag_history_loc ℓ t s -∗
    ⌜∃ enc,
        enc_abs_hist !! t = Some enc ∧ decode enc = Some s⌝.
  Proof.
    rewrite /know_full_encoded_history_loc.
    iIntros "H1 (% & % & H2)".
    iDestruct (full_entry_frag_entry with "H1 H2") as %look.
    iPureIntro. eexists _. split_and!; done.
  Qed.

  Lemma know_full_encoded_history_lookup_big q ℓ full_enc_hist hist :
    know_full_encoded_history_loc ℓ q full_enc_hist -∗
    ([∗ map] t↦s ∈ hist, know_frag_history_loc ℓ t s) -∗
    ⌜ ∃ enc_hist,
      enc_hist ⊆ full_enc_hist ∧
      dom hist = dom enc_hist ∧
      omap decode enc_hist = hist ∧
      (* The last conjunc here is "bonus" and can be removed unless users of *)
(*        * the lemma make use of it. *)
      map_Forall (λ k enc, ∃ s, decode enc = Some s ∧
                                hist !! k = Some s) enc_hist ⌝.
  Proof.
    iIntros "F M".
    rewrite /know_frag_history_loc.
    iDestruct (big_sepM_exist_r with "M") as (hist_enc) "M".
    iDestruct (full_entry_lookup_big _ _ _ _ _ hist_enc with "F [M]") as %sub.
    { iApply big_sepM_forall.
      iIntros (???).
      iDestruct (big_sepM2_lookup_r with "M") as (???) "$"; first done. }
    iExists hist_enc.
    iSplit; first done.
    iDestruct (big_sepM2_dom with "M") as %domeq.
    iSplit; first done.
    iSplit.
    { rewrite map_eq_iff. iIntros (t).
      rewrite lookup_omap. destruct (hist_enc !! t) eqn:look.
      - iDestruct (big_sepM2_lookup_r with "M") as (?  look2 ?) "hih"; first done.
        rewrite look2. done.
      - iPureIntro. simpl. symmetry.
        eapply map_dom_eq_lookup_None; done. }
    iIntros (?? look).
    iDestruct (big_sepM2_lookup_r with "M") as (???) "hih"; first done.
    iExists x1. done.
  Qed.

  Lemma know_frag_history_singleton_agree ℓ t s1 s2 :
    know_frag_history_loc ℓ t s1 -∗
    know_frag_history_loc ℓ t s2 -∗
    ⌜ s1 = s2 ⌝.
  Proof.
    iDestruct 1 as (enc deq) "K".
    iDestruct 1 as (enc' deq') "K'".
    iDestruct (frag_entry_agree with "K K'") as %<-.
    iPureIntro. congruence.
  Qed.

  Lemma know_full_history_lookup ℓ q abs_hist t s :
    know_full_history_loc ℓ q abs_hist -∗
    know_frag_history_loc ℓ t s -∗
    ⌜ abs_hist !! t = Some s ⌝.
  Proof.
    iIntros "A B".
    iDestruct ("B") as (e decEq) "B".
    iDestruct (full_entry_frag_entry with "A B") as %look.
    apply lookup_fmap_Some in look as (s' & encEq & look).
    assert (s = s') as <-.
    { rewrite -encEq decode_encode in decEq. by inversion decEq. }
    done.
  Qed.

  (** nextgen instances *)

  Definition lastgen_know_frag_history_loc `{Countable ST} ℓ t (σ : ST) : iProp Σ :=
    ∃ eσ, ⌜ decode eσ = Some σ ⌝ ∗ lastgen_frag_entry abs_history_name ℓ t eσ.
  
  Context `{!AbstractState ST}.
  #[global] Instance know_frag_history_loc_into_nextgen ℓ t (σ: ST):
    IntoNextgen
      (know_frag_history_loc ℓ t σ)
      (lastgen_know_frag_history_loc ℓ t σ ∗
       ∀ OCV (bumper: ST → ST), ⌜ ℓ ∈ dom OCV ∧ t ≤ OCV !!0 ℓ ⌝ -∗
                                crashed_at_offset OCV -∗
                                know_bumper ℓ bumper -∗
                                know_frag_history_loc ℓ t (bumper σ)).
  Proof.
    rewrite /IntoNextgen.
    iIntros "(%eσ & %Hdecode & frag)".
    iModIntro.
    iDestruct "frag" as "[lastgen_frag frag]".
    iSplitL "lastgen_frag".
    { iExists _. by iFrame. }
    iIntros (OCV bumper [? ?]) "OCV [% bumper]".
    iSpecialize ("frag" with "OCV [//] bumper").
    rewrite /drop_above_bump decide_True; last done.
    rewrite /encode_bumper /safe_bumper Hdecode /=.
    iExists _. iFrame.
    iPureIntro.
    apply decode_encode.
  Qed.
End Histories.

(* TODO: replace this definition with [picked_in] of abstract history *)
Section crashed_in.
  Context `{nvmHighGS}.
  Context `{Countable ST}.

  (* [crashed_in ℓ s] means location [ℓ] crashed in (latest) abstract state [s]
   * (before applying bumper). *)
  Definition crashed_in_loc (ℓ: loc) (σ : ST) : iProp Σ :=
    ∃ eσ OCV, crashed_at_offset OCV ∗ ⌜ ℓ ∈ dom OCV ⌝ ∗ ⌜ decode eσ = Some σ ⌝ ∗ lastgen_frag_entry abs_history_name ℓ (OCV !!0 ℓ) eσ.

  (* The encoded [crashed_in] assertion for use in [interp], it contains the
   * additional knowledge for [persist_lb]. *)
  Definition crashed_in_enc `{nvmHighGS} ℓ (eσ : positive) : iProp Σ :=
    ∃ OCV, crashed_at_offset OCV ∗ ⌜ ℓ ∈ dom OCV ⌝ ∗
           lastgen_frag_entry abs_history_name ℓ (OCV !!0 ℓ) eσ ∗
           offset_loc ℓ (OCV !!0 ℓ) ∗
           persisted_loc ℓ 0.

  Lemma crashed_in_loc_agree ℓ σ1 σ2:
    crashed_in_loc ℓ σ1 -∗ crashed_in_loc ℓ σ2 -∗ ⌜ σ1 = σ2 ⌝.
  Proof.
    iDestruct 1 as (??) "(#OCV & _ & % & know)".
    iDestruct 1 as (??) "(#OCV' & _ & % & know')".
    iDestruct (crashed_at_offset_agree with "OCV OCV'") as %->.
    iDestruct (lastgen_frag_entry_agree with "know know'") as %->.
    by simplify_eq.
  Qed.

  Lemma crashed_in_OCV OCV ℓ σ:
    crashed_at_offset OCV -∗ crashed_in_loc ℓ σ -∗ ⌜ ℓ ∈ dom OCV ⌝.
  Proof.
    iIntros "OCV".
    iDestruct 1 as (??) "(#OCV' & % & _)".
    by iDestruct (crashed_at_offset_agree with "OCV OCV'") as %->.
  Qed.
End crashed_in.

Opaque crashed_in_loc.

Section NextgenLemmas.
  Context `{!nvmBaseGS Σ Ω, !nvmHighGS Σ Ω, !PerennialG Σ}.
  Context `{AbstractState ST}.

  #[global] Instance know_bumper_nextgen ℓ (bumper: ST → ST):
    IntoNextgen
      (know_bumper ℓ bumper)
      (if_rec ℓ (know_bumper ℓ bumper)).
  Proof.
    rewrite /IntoNextgen.
    iIntros "[%bumpValid #bumper]".
    iPoseProof (ghost_map_elem_into_nextgen_ifrec with "bumper") as "#bumper'".
    iModIntro.
    iDestruct "bumper'" as "[_ ?]".
    iModIntro.
    iSplit; done.
  Qed.

  (* Lemma frag_history_nextgen ℓ t offset bumper (σ : ST) : *)
  (*   ⎡ know_preorder_loc ℓ (abs_state_relation (ST := ST)) ⎤ -∗ *)
  (*   ⎡ offset_loc ℓ offset ⎤ -∗ *)
  (*   ⎡ know_bumper ℓ bumper ⎤ -∗ *)
  (*   ⎡ know_frag_history_loc ℓ t σ ⎤ -∗ *)
  (*   <NG> if_rec ℓ (∃ σC CV tC v, *)
  (*              ⌜ CV !! ℓ = Some (MaxNat tC) ⌝ ∗ *)
  (*              ⎡ crashed_at CV ⎤ ∗ *)
  (*              ⎡ crashed_in ℓ σC ⎤ ∗ *)
  (*              ⎡ know_frag_history_loc ℓ (offset + tC) (bumper σC) ⎤ ∗ *)
  (*              ⎡ know_phys_hist_msg ℓ (offset + tC) (memory.Msg v ∅ ∅ ∅) ⎤ ∗ *)
  (*              (⌜ t ≤ offset + tC ⌝ -∗ *)
  (*               ⌜ σ ⊑ σC ⌝ ∗ ⎡ know_frag_history_loc ℓ t (bumper σ) ⎤)). *)
  (* Proof. *)
  (*   iIntros "preOrder #offset #bumper fragHist". *)
  (*   iPoseProof (ghost_map_elem_into_nextgen_ifrec with "preOrder") as "preOrder". *)
  (*   rewrite /know_frag_history_loc /know_frag_history_loc. *)
  (*   iDestruct "fragHist" as (encσ Hdecodeσ) "frag_hist_entry". *)
  (*   iPoseProof (frag_entry_local_nextgen with "frag_hist_entry [bumper]") as "frag_hist_entry". *)
  (*   { iDestruct "bumper" as "[? $]". } *)
  (*   iModIntro. *)
  (*   rewrite -?if_rec_lift_if_rec. *)
  (*   iModIntro. *)
  (* Abort. *)
End NextgenLemmas.
