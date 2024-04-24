Require Import Utf8.

□ P * Q ⊢ R

Lemma opg1a (R : nat → Prop) : ∃x, R x → (∀y, R y).
Proof.
  

