From Perennial.program_logic Require crash_weakestpre.

From self.high Require Export dprop.
From self.base Require Import primitive_laws.
From self.high Require Import weakestpre.

Section wpc.
  Context `{!nvmG Σ}.

  Program Definition wpc_def s k E e (Φ : val → dProp Σ) (Φc : dProp Σ) : dProp Σ :=
    MonPred (λ V,
      ⌜ Objective Φc ⌝ ∗
      ∀ TV,
        ⌜V ⊑ TV⌝ -∗
        validV (store_view TV) -∗
        interp -∗
        WPC (ThreadState e TV) @ s; k; E {{ λ res,
          let '(ThreadVal v TV') := res return _ in
            validV (store_view TV') ∗ (Φ v TV') ∗ interp
          }}{{ Φc TV }}
    )%I _.
  Next Obligation. solve_proper. Qed.

  (* This is sealing follows the same ritual as the [wp] in Iris. *)
  Definition wpc_aux : seal (@wpc_def). by eexists. Qed.

  Global Instance expr_wpc : Wpc expr_lang (dProp Σ) stuckness nat := wpc_aux.(unseal).

  Lemma wpc_eq : wpc = wpc_def.
  Proof. rewrite -wpc_aux.(seal_eq). done. Qed.

  Lemma wpc_bind K s k E1 (e : expr) Φ Φc :
    WPC e @ s; k; E1 {{ v, WPC fill K (of_val v) @ s; k; E1 {{ Φ }} {{ Φc }} }} {{ Φc }}
                      ⊢ WPC fill K e @ s; k; E1 {{ Φ }} {{ Φc }}.
  Proof.
    rewrite wpc_eq.
    iStartProof (iProp _). iIntros (V).
    iIntros "[#obj WP]".
    iFrame "obj".
    iIntros (TV) "incl val interp".
    iDestruct ("WP" with "incl val interp") as "HI".
    (* iApply (crash_weakestpre.wpc_bind nvm_lang). *)
    Check wp_bind.
    rewrite nvm_fill_fill.
    iApply crash_weakestpre.wpc_bind.
    { apply: ectx_lang_ctx. }
    iApply (wpc_mono with "HI").
    2: { done. }
    iIntros ([v TV']) "(val & [obj wpc] & interp)".
    iDestruct ("wpc" $! TV' with "[//] val interp") as "HI".
    rewrite nvm_fill_fill.
    simpl. rewrite /thread_of_val. simpl.
    iDestruct "obj" as %obj.
    iApply (wpc_crash_mono with "[] HI").
    iModIntro.
    iApply objective_at.
  Qed.

End wpc.
