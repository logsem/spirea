(** Allow async proof-checking of sections. *)
#[export] Set Default Proof Using "Type".

(** Enforces that every tactic is executed with a single focused goal, meaning
that bullets and curly braces must be used to structure the proof. *)
#[export] Set Default Goal Selector "!".
