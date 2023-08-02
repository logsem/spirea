(* A variant of the authorative resource algebra that has _two_ fractions. One
per-generation fraction and one cross-generation fraction. *)

From iris.algebra Require Import dfrac auth.

From self Require Import cmra_morphism_extra.

Definition gen_auth (A : ucmra) : Type := option dfrac * auth A.
Definition gen_authR (A : ucmra) : cmra := prodR (optionR dfracR) (authR A).
Definition gen_authUR (A : ucmra) : cmra := prodUR (optionUR dfracR) (authR A).

Definition set_dfrac_auth {A : ucmra} (dq : option dfrac) (a : option (dfrac * agree A)) :=
  match (dq, a) with
  | (Some (DfracOwn dq1), Some (dq2, ag)) => Some (DfracOwn dq1, ag)
  | (Some (DfracBoth dq1), Some (dq2, ag)) => Some (DfracOwn dq1, ag)
  | _ => None
  end.

#[global]
Instance set_dfrac_auth_ne {A : ucmra} : NonExpansive2 (set_dfrac_auth (A := A)).
Proof.
  intros n ? mdq eq.
  rewrite -discrete_iff in eq.
  apply leibniz_equiv in eq.
  subst.
  destruct mdq as [?|]; intros [[??]|] [[??]|] eq;
    rewrite /set_dfrac_auth; simpl; inversion eq; try done.
  destruct d; try done.
  - f_equiv. f_equiv. apply H1.
  - f_equiv. f_equiv. apply H1.
Qed.

Definition gen_auth_floor {A : ucmra} (a : gen_auth A) : gen_auth A :=
  match a with
  | (mdq, View a b) => (mdq, View (set_dfrac_auth mdq a) b)
  end.

Global Instance gen_auth_floor_gentrans A : CmraMorphism (gen_auth_floor (A := A)).
Proof.
  split.
  - intros n [? [??]] [? [??]]. simpl.
    rewrite /prod_equiv.
    intros [fracEq authEq].
    rewrite -discrete_iff in fracEq.
    simpl in fracEq.
    apply leibniz_equiv in fracEq.
    rewrite fracEq.
    split; first done.
    simpl in *.
    f_equiv.
    * inversion authEq. solve_proper.
    * apply authEq.
  - intros ?.
    (* admit. *)
    intros [[[q| |q]|] [[[??]|]?]]; try (cbv; naive_solver).
    simpl. rewrite /set_dfrac_auth.
    (* Holds since validity of [DfracBoth q] implies validity of [DfracOwn q]. *)
    admit.
  - intros [[?|] [[[??]|]?]]; try done.
    * destruct c; destruct d; try done.
    * destruct c; done.
  - intros [[[q| |q]|] [[[??]|]?]];
      intros [[[q'| |q']|] [[[??]|]?]]; try done.
    * simpl.
Admitted.
