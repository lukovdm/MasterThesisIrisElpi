From elpi Require Import elpi.
From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.bi Require Import fixpoint.
From iris.algebra Require Import ofe monoid list.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation.
From stdpp Require Import base finite.

#[arguments(raw)] Elpi Command PrintCommand.
Elpi Accumulate lp:{{

  % main is, well, the entry point
  main Arguments :- coq.say "PrintCommand" Arguments.

}}.
Elpi Typecheck.

Elpi Export PrintCommand.

#[arguments(raw)] Elpi Command EI.ind.
Elpi Accumulate lp:{{

  % main is, well, the entry point
  main [indt-decl (inductive Name In-Or-Co)] :- coq.say "Hello" Arguments.

}}.
Elpi Typecheck.

Elpi Export EI.ind.


Section Tests.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  EI.ind 
  Inductive is_list : val → list val → iProp :=
    | empty_is_list : is_list NONEV []
    | cons_is_list l v vs : ∃ tl, l ↦ (v, tl) -∗ is_list tl vs -∗ is_list (SOMEV #l) (v :: vs).

End Tests.
