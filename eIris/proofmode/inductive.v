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

  pred constructor->term i:indc-decl, o:term.
  constructor->term (constructor _ Arity) T :- coq.arity->term Arity T.

  pred type-to-fun i:term, o:term.
  type-to-fun (prod N T F) (fun N FT FB) :- !,
    type-to-fun T FT, (pi x\ type-to-fun (F x) (FB x)).
  type-to-fun X X :- !.

  pred init-prod-to-bi-forall i:term, o:term.
  init-prod-to-bi-forall (prod N T F) {{ bi_forall lp:Fun}} :- !,
    (pi x\ init-prod-to-bi-forall (F x) (F' x)),
    Fun = (fun N T F').
  init-prod-to-bi-forall X X.

  % main is, well, the entry point
  main [indt-decl (inductive Name _In-Or-Co Arity Constructors)] :- 
    coq.say "------ Creating inductive" Name,
    coq.arity->term Arity TypeTerm,
    coq.say "------ With type" { coq.term->string TypeTerm },
    (pi x\ print-contructors (Constructors x)),
    (pi f\ std.map (Constructors f) constructor->term (ConstrTerms f)),
    (pi f\ std.map (ConstrTerms f) init-prod-to-bi-forall (ConstrBiTerms f)),
    (pi f\ coq.say "------ Constructor Bi Terms" {std.map (ConstrBiTerms f) coq.term->string} (ConstrBiTerms f)),
    (pi f\ std.fold 
      { std.drop-last 1 (ConstrBiTerms f) } 
      { std.last (ConstrBiTerms f) }
      (x\ a\ r\ r = {{ bi_or lp:a lp:x }}) 
      (ConstrBo f)),
    coq.say "------ Constructor body disjunction" {coq.term->string (ConstrBo {{ True }})} ConstrBo,
    (pi b\ (type-to-fun ({{ uPred (iResUR Σ) }}) b :- !) => type-to-fun TypeTerm (FunTerm b)), % TODO: A proper PROP should be added not the hacky heap-lang one
    (pi b\
      (pi N T T1 F F1 A \ fold-map (fun N T F) A (fun N T1 F1) A :- !,
                                  fold-map T A T1 _, pi x\ fold-map (F x) [x | A] (F1 x) _) =>
      (pi L F B \ fold-map b L B L:- !, std.last L F, B = (ConstrBo F)) =>
          fold-map {{fun F : lp:TypeTerm => lp:{{ FunTerm b }} }} [] Bo _),
    coq.say "------- Body" { coq.term->string Bo } Bo,
    Ty = {{ lp:TypeTerm -> lp:TypeTerm }},
    std.assert-ok! (coq.elaborate-skeleton Bo Ty EBo) "Type check failed",
    coq.env.add-const {calc (Name ^ "_pre")} EBo Ty ff C,
    coq.say "const" C.
}}.
Elpi Typecheck.

Elpi Export EI.ind.

Section Tests.
  Implicit Types l : loc.

  Elpi Trace Browser.

  EI.ind 
  Inductive is_list : val → list val → iProp :=
    | empty_is_list : is_list NONEV []
    | cons_is_list l v vs : l ↦ NONEV -∗ is_list (SOMEV #l) (v :: vs). (*(∃ tl, l ↦ (v, tl) ∗ is_list tl vs) -∗ is_list (SOMEV #l) (v :: vs).*)

  Print is_list_pre.

  PrintCommand
  Definition is_list_pre : (val -d> list val -d> iProp) -d> val -d> list val -d> iProp := λ is_list hd vs,
    match vs with
    | [] => ⌜hd = NONEV⌝
    | v :: vs => ∃ l tl, ⌜hd = SOMEV #l⌝ ∗ l ↦ (v,tl) ∗ ▷ is_list tl vs
    end%I.

End Tests.
