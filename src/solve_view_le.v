(** A tactic that solves goals of the form [A ⊑ B] when [A] and [B] are either
[view]s or [thread_view]s.  *)

From self.lang Require Export thread_view.
From self.high Require Export dprop.

Ltac destruct_thread_view_le :=
  match goal with
    | [H : ((_, _, _) ⊑ (_, _, _)) |- _] => destruct H as [[??]?]
  end.

Ltac destruct_thread_view :=
  match goal with
    | [H : thread_view |- _] => destruct H as [[??]?]
    | [H : bi_index_type thread_view_bi_index |- _] => destruct H as [[??]?]
  end.

Create HintDb view_le.

#[global] Hint Extern 0 (_ ≤ _) => lia : view_le.
#[global] Hint Resolve thread_view_le : view_le.
#[global] Hint Resolve view_le_l : view_le.
#[global] Hint Resolve view_le_r : view_le.
#[global] Hint Resolve view_insert_le' : view_le.
#[global] Hint Resolve view_lub_le : view_le.
#[global] Hint Extern 2 (_ ⊑ _) => (etrans; last eassumption) : view_le.
#[global] Hint Extern 2 (_ ⊑ _) => (etrans; first eassumption) : view_le.
#[global] Hint Resolve view_le_lub_r : view_le.
#[global] Hint Resolve view_le_lub_l : view_le.

Ltac solve_view_le :=
  repeat destruct_thread_view;
  repeat destruct_thread_view_le;
  eauto with view_le.
