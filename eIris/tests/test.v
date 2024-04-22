Require Import Utf8.

Lemma opg1a (R : nat → Prop) : ∃x, R x → (∀y, R y).
Proof.
  
