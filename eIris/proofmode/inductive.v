From elpi Require Import elpi.
From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.bi Require Import fixpoint.
From iris.algebra Require Import ofe monoid list.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation.
From stdpp Require Import base finite.

Context `{!heapGS Σ}.
Notation iProp := (iProp Σ).

Elpi Command PrintCommand.
Elpi Accumulate lp:{{

  % main is, well, the entry point
  main Arguments :- coq.say "PrintCommand" Arguments.

}}.
Elpi Typecheck.

Elpi Export PrintCommand.

#[arguments(raw)] Elpi Command EI.ind.
Elpi Accumulate lp:{{

  pred print-contructors i:list indc-decl.
  print-contructors [].
  print-contructors [constructor Name Arity | CS] :-
    coq.say Name "of type" { coq.term->string { coq.arity->term Arity } },
    print-contructors CS.

  pred type-to-fun i:term, o:term.
  type-to-fun (prod N T F) (fun N FT FB) :- !,
    type-to-fun T FT, (pi x\ type-to-fun (F x) (FB x)).
  type-to-fun X X :- !.

  % main is, well, the entry point
  main [indt-decl (inductive Name _In-Or-Co Arity Constructors as _Inductive)] :- 
    coq.say "Creating inductive" Name,
    coq.arity->term Arity TypeTerm,
    coq.say TypeTerm,
    coq.say "With type" { coq.term->string TypeTerm },
    pi x\ print-contructors (Constructors x),
    (pi b\ type-to-fun ({{ uPred (iResUR Σ) }}) b => type-to-fun TypeTerm (FunTerm b)), % TODO: A proper PROP should be added not the hacky heap-lang one
    (pi b\ [
      (sigma N T T1 F F1 A A1 A2 \ (fold-map (fun N T F) A (fun N T1 F1) A2 :- !,
        fold-map T A T1 A1, pi x\ fold-map (F x) [x | A1] (F1 x) A2)),
      (sigma L \ fold-map b L (app L) L:- !)
    ] => fun { coq.string->name "F" } TypeTerm (f\ FunTerm b)),
    coq.say { coq.term->string Bo }.
    % coq.env.add-const {calc (Name ^ "_pre")}

}}.
Elpi Typecheck.

Elpi Export EI.ind.

Section Tests.
  Implicit Types l : loc.

  Elpi Trace Browser.

  EI.ind 
  Inductive is_list : val → list val → iProp :=
    | empty_is_list : is_list NONEV []
    | cons_is_list l v vs : (∃ tl, l ↦ (v, tl) ∗ is_list tl vs) -∗ is_list (SOMEV #l) (v :: vs).

  PrintCommand
  Definition is_list_pre : (val -d> list val -d> iProp) -d> val -d> list val -d> iProp := λ is_list hd vs,
    match vs with
    | [] => ⌜hd = NONEV⌝
    | v :: vs => ∃ l tl, ⌜hd = SOMEV #l⌝ ∗ l ↦ (v,tl) ∗ ▷ is_list tl vs
    end%I.

End Tests.
