(* Wrappers around Perennials' invariant/fupd resources that survive crashes. *)

From iris.algebra Require Import gmap auth agree gset coPset list vector excl.
From iris.base_logic Require Import lib.later_credits.
From Perennial.algebra Require Import mlist.
From Perennial.Helpers Require Import ipm.
From Perennial.base_logic.lib Require Import wsat.
From Perennial.program_logic Require Export weakestpre.
From Perennial.program_logic Require Export crash_lang.

From self.nextgen Require Import nextgen_promises_ng.

(* Below are the resources used in Perennial for fupd, but where [inG] has been
 * replaced with [inG]. *)

Class ngFmlistG (A : Type) {Heq: EqDecision A} Σ Ω :=
  { ngFmlist_inG :> ngInG Σ Ω (fmlistUR A) }.

(** The ghost state for later credits *)
Class ngLcGpreS (Σ : gFunctors) Ω := LcGpreS {
  ngLcGpreS_inG : ngInG Σ Ω (authR natUR)
}.

Class ngLcGS (Σ : gFunctors) Ω := NgLcGS {
  ngLcGS_inG :> ngInG Σ Ω (authR natUR);
  ngLcGS_name : gname;
}.

#[global]
Instance ngLcGS_unwrap Σ Ω : ngLcGS Σ Ω → lcGS Σ := {
  lcGS_inG := _;
  lcGS_name := ngLcGS_name;
}.

(* Global Hint Mode ngLcGS - : typeclass_instances. *)
(* Local Existing Instances lcGS_inG lcGpreS_inG. *)

Definition invR Σ :=
  authR (gmapUR positive
    (prodR (agreeR (prodO (listO (laterO (iPropO Σ))) bi_schemaO))
      (optionR (prodR fracR (agreeR (listO (laterO (iPropO Σ)))))))).

Class ngInvGpreS (Σ : gFunctors) Ω : Set := WsatPreG {
  inv_inPreG :> ngInG Σ Ω (invR Σ);
  enabled_inPreG :> ngInG Σ Ω coPset_disjR;
  disabled_inPreG :> ngInG Σ Ω (gset_disjR positive);
  mlist_inPreG :> ngFmlistG (invariant_level_names) Σ Ω;
  inv_lcPreG : ngLcGpreS Σ Ω;
}.

Class ngInvGS (Σ : gFunctors) Ω : Set := WsatG {
  inv_inG :> ngInvGpreS Σ Ω;
  invGS_lc :> ngLcGS Σ Ω;
  inv_list_name : gname;
  enabled_name : gname;
  disabled_name : gname;
}.

Section ngInv_lemmas.
  Context `{!ngInvGS Σ Ω}.

  Lemma nextgen_lc k : £ k ⊢ ⚡==> £ k.
  Proof.
    iIntros "O".
    rewrite later_credits.lc_unseal /later_credits.lc_def.
    iModIntro.
    done.
  Qed.

  #[global]
  Instance into_nextgen_lc k : IntoNextgen _ _ := nextgen_lc k.

End ngInv_lemmas.
