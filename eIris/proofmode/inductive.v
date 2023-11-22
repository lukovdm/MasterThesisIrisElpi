From elpi Require Import elpi.
From iris.proofmode Require Import base environments proofmode tactics coq_tactics reduction intro_patterns class_instances spec_patterns.
From iris.prelude Require Import options.
From iris.bi Require Import  bi telescopes fixpoint.
From iris.algebra Require Import ofe monoid list.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation.
From stdpp Require Import base finite.

From eIris.proofmode Require Export proper.
From eIris.proofmode Require Import reduction.

From eIris.proofmode Require Import base.
From eIris.proofmode.elpi Extra Dependency "proper_solver.elpi" as proper_solver.

#[arguments(raw)] Elpi Command EI.ind.
Elpi Accumulate Db reduction.db.
Elpi Accumulate File proper_solver.
Elpi Accumulate lp:{{
  kind param type.
  type par id -> implicit_kind -> term -> term -> param.

  pred constructor->term i:indc-decl, o:term.
  constructor->term (constructor _ Arity) T :- coq.arity->term Arity T.

  pred find-PROP i:term, o:term.
  find-PROP (prod _ _ F) O :- !,
    (pi x\ find-PROP (F x) O).
  find-PROP O O :- !.

  pred type-to-fun i:term, o:term.
  type-to-fun (prod N T F) (fun N T FB) :- !,
    (pi x\ type-to-fun (F x) (FB x)).
  type-to-fun X X :- !.

  pred init-prod-to-bi-exist i:term, o:term.
  init-prod-to-bi-exist (prod N T F) {{ bi_exist lp:Fun}} :- !,
    (pi x\ init-prod-to-bi-exist (F x) (F' x)),
    Fun = (fun N T F').
  init-prod-to-bi-exist X X.

  pred last-rec-to-and i:term, i:list term, i:term, o:term.
  last-rec-to-and A B {{ bi_exist lp:{{ fun N T F}} }} {{ bi_exist lp:{{ fun N T F' }} }} :- !,
    (pi x\ last-rec-to-and A B (F x) (F' x)).
  last-rec-to-and A B {{ bi_sep lp:L lp:R }} {{ bi_sep lp:L lp:R' }} :- !,
    last-rec-to-and A B R R'.
  last-rec-to-and A B {{ bi_or lp:L lp:R }} {{ bi_or lp:L' lp:R' }} :- !,
    last-rec-to-and A B L L',
    last-rec-to-and A B R R'.
  last-rec-to-and F [] (app [F]) {{ True }}.
  last-rec-to-and F [L | LS] (app [F, T | TS]) TS' :-
    {std.length LS} = {std.length TS}, !,
    std.fold2 LS TS {{ (⌜lp:L = lp:T⌝)%I }} (l\ t\ a\ r\ sigma TMP\ TMP = {{ (⌜lp:l = lp:t⌝)%I }}, r = {{ (lp:a ∗ lp:TMP)%I }}) TS'.
  last-rec-to-and _ [_ | _] (app [T | TS]) _ :-
    coq.error "EI.Ind: " {coq.term->string (app [T | TS])} "has to many or to few arguments".

  pred top-wand-to-sepand i:term, o:term.
  top-wand-to-sepand {{ bi_emp_valid lp:T }} T' :- !,
    top-wand-to-sepand T T'.
  top-wand-to-sepand {{ bi_exist lp:{{ fun N T F}} }} {{ bi_exist lp:{{ fun N T F' }} }} :- !,
    (pi x\ top-wand-to-sepand (F x) (F' x)).
  top-wand-to-sepand {{ bi_forall lp:{{ fun N T F}} }} {{ bi_forall lp:{{ fun N T F' }} }} :- !,
    (pi x\ top-wand-to-sepand (F x) (F' x)).
  top-wand-to-sepand {{ bi_wand lp:L lp:R }} {{ bi_sep lp:L lp:R' }} :- !,
    top-wand-to-sepand R R'.
  top-wand-to-sepand {{ bi_sep lp:L lp:R }} {{ bi_sep lp:L lp:R' }} :- !,
    top-wand-to-sepand R R'.
  top-wand-to-sepand X X :- !.

  pred replace-params-bo i:list param, i:term, o:term.
  replace-params-bo [] T T.
  replace-params-bo [(par ID _IK Type C) | Params] Term (fun N Type FTerm) :-
    coq.id->name ID N,
    replace-params-bo Params Term Term',
    (pi x\ (copy C x :- !) => copy Term' (FTerm x)).

  pred replace-params-ty i:list param, i:term, o:term.
  replace-params-ty [] T T.
  replace-params-ty [(par ID _IK PType C) | Params] Type (prod N PType FType) :-
    coq.id->name ID N,
    replace-params-ty Params Type Type',
    (pi x\ (copy C x :- !) => copy Type' (FType x)).

  pred constr-body-disj i:(term -> list indc-decl), o:(term -> term).
  constr-body-disj Constructors ConstrBo :-
    if-debug ((pi x\ print-contructors (Constructors x))),
    (pi f\ std.map (Constructors f)
      (x\ r\ sigma TMP1 TMP2\ 
        constructor->term x TMP1, 
        init-prod-to-bi-exist TMP1 TMP2, 
        top-wand-to-sepand TMP2 r) % You can't spill here otherwise the TMP1 and TMP2 will be bound in the outer scope.
      (ConstrBiTerms f)),
    if-debug ((pi f\ coq.say "------ Constructor Bi Terms" {std.map (ConstrBiTerms f) coq.term->string})),
    (pi f\ std.fold 
      { std.drop-last 1 (ConstrBiTerms f) } 
      { std.last (ConstrBiTerms f) }
      (x\ a\ r\ r = {{ bi_or lp:a lp:x }}) 
      (ConstrBo f)),
    if-debug (coq.say "------ Constructor body disjunction" {coq.term->string (ConstrBo {{ True }})}).

  pred constr-body i:list param, i:term, i:(term -> list indc-decl), o:term, o:term.
  constr-body Params TypeTerm Constructors EBo Ty :-
    find-PROP TypeTerm PROP,
    constr-body-disj Constructors ConstrBo,
    (pi b\ (type-to-fun PROP b :- !) => type-to-fun TypeTerm (FunTerm b)), % TODO: A proper PROP should be added not the hacky heap-lang one
    (pi b\
      % Save the variables of functions in a list
      (pi N T T1 F F1 A \ fold-map (fun N T F) A (fun N T1 F1) A :- !,
                                  fold-map T A T1 _, pi x\ fold-map (F x) [x | A] (F1 x) _) => 
      % When we hit our placeholder for the function body we replace it with the function body with the last application replaced by equalities for the arguments
      (pi L L' F B \ fold-map b L B L :- !, std.rev L [F | L'], last-rec-to-and F L' (ConstrBo F) B) => 
          fold-map {{fun F : lp:TypeTerm => lp:{{ FunTerm b }} }} [] Bo _),
    replace-params-bo Params Bo PBo,
    if-debug (coq.say "------- Body" { coq.term->string PBo }),
    replace-params-ty Params {{ lp:TypeTerm -> lp:TypeTerm }} Ty, !,
    if-debug (coq.say "------- Type" { coq.term->string Ty }),
    @keepunivs! => std.assert-ok! (coq.elaborate-skeleton PBo Ty EBo) "Type check body failed".

  pred build-proper i:list param, i:term, i:term, o:term.
  build-proper Params F Type EBo :-
    find-PROP Type PROP,
    (pi N T F A T1 F1 A1 \ fold-map (prod N T F) A (prod N T1 F1) (some {{ (.> lp:A1)%i_signature }}) :-
          fold-map T A T1 _, !, (pi x\ fold-map (F x) A (F1 x) (some A1))) =>
      (pi A \ fold-map PROP A PROP (some {{ bi_wand }}) :- !) =>
        fold-map Type none Type (some R),
    std.map Params (x\r\ x = (par _ _ _ r)) Ps,
    Fapp = app [F | Ps],
    replace-params-ty Params {{ IProper (□> lp:R ==> lp:R) lp:Fapp }} Proper,
    @keepunivs! => std.assert-ok! (coq.elaborate-skeleton Proper {{ Prop }} EBo) "Type check proper failed".

  pred proper-proof i:term, o:term.
  proper-proof Proper Proof :-
    coq.typecheck Proof Proper ok,
    do-solve-proper (hole Proper Proof).

  pred create-iInductive i:list param, i:indt-decl.
  create-iInductive Params' (inductive Name _In-Or-Co Arity Constructors) :-
    std.rev Params' Params,
    coq.say Params,
    if-debug (coq.say "------ Creating inductive" Name),
    coq.arity->term Arity TypeTerm,
    if-debug (coq.say "------ With type" { coq.term->string TypeTerm }),

    constr-body Params TypeTerm Constructors EBo Ty,
    if-debug (coq.say "------ typed body" { coq.term->string EBo }),
    coq.env.add-const {calc (Name ^ "_pre")} EBo Ty ff C,
    if-debug (coq.say "const" C),

    if (get-option "noproper" tt) (true)
      (
        build-proper Params (global (const C)) TypeTerm Proper,
        if-debug (coq.say "Relation" {coq.term->string Proper})
      ),

    if (get-option "nosolver" tt) (true)
      (
      proper-proof Proper ProofTerm,
      coq.env.add-const { calc (Name ^ "_pre_mono") } ProofTerm Proper ff M,
      if-debug (coq.say "Mono" M)
      ).
  create-iInductive Params (parameter ID IK T IND) :-
    pi p\ create-iInductive [(par ID IK T p) | Params] (IND p).

  % main is, well, the entry point
  main [indt-decl I] :- 
    attributes A,
    coq.parse-attributes A [
      att "debug" bool,
      att "noproper" bool,
      att "nosolver" bool,
    ] Opts,
    gettimeofday Start,
    [get-option "start" Start | Opts] => (
      if (get-option "noproper" tt, not (get-option "nosolver" tt)) (coq.error "Can't do solver when noproper") (true),
      create-iInductive [] I
      ).
}}.
Elpi Typecheck.

Elpi Export EI.ind.

Elpi Tactic IProper_solver.
Elpi Accumulate Db reduction.db.
Elpi Accumulate File proper_solver.
Elpi Accumulate lp:{{
  solve (goal _Ctx _Trigger Type Proof []) _ :- 
    do-solve-proper (hole Type Proof).
  
  solve (goal _Ctx _Trigger Type Proof [str "debug"]) _ :- 
    gettimeofday Start,
    [get-option "debug" tt, get-option "start" Start] => do-solve-proper (hole Type Proof).
}}.
Elpi Typecheck.
Elpi Export IProper_solver.

Section Tests.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  EI.ind 
  Inductive is_list : val → list val → iProp :=
    | empty_is_list : is_list NONEV []
    | cons_is_list l v vs tl : l ↦ (v,tl) -∗ is_list tl vs -∗ is_list (SOMEV #l) (v :: vs).

  Print is_list_pre.
  Check is_list_pre_mono.

  EI.ind 
  Inductive is_P_list : (val → iProp) → val → iProp :=
    | empty_is_P_list P : is_P_list P NONEV
    | cons_is_P_list P l v tl : l ↦ (v,tl) -∗ P v -∗ is_P_list P tl -∗ is_P_list P (SOMEV #l).

  Print is_P_list_pre.
  Check is_P_list_pre_mono.

  EI.ind 
  Inductive is_P2_list {A} (P : val → A → iProp) : val → list A → iProp :=
    | empty_is_P2_list : is_P2_list P NONEV []
    | cons_is_P2_list l v tl x xs : l ↦ (v,tl) -∗ P v x -∗ is_P2_list P tl xs -∗ is_P2_list P (SOMEV #l) (x :: xs).

  Print is_P2_list_pre.
  Check is_P2_list_pre_mono.
End Tests.
