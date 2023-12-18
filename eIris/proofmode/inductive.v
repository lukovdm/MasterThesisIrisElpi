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
From eIris.proofmode Require Import inductiveDB.

From eIris.proofmode Require Import base intros apply startProof.
From eIris.proofmode.elpi Extra Dependency "proper_solver.elpi" as proper_solver.

#[arguments(raw)] Elpi Command EI.ind.
Elpi Accumulate Db reduction.db.
Elpi Accumulate Db induction.db.
Elpi Accumulate File proper_solver.
Elpi Accumulate lp:{{
  kind param type.
  type par id -> implicit_kind -> term -> term -> param.

  
  pred constructor->term i:indc-decl, o:term.
  constructor->term (constructor _ Arity) T :- coq.arity->term Arity T.


  pred type-depth i:term, o:int.
  type-depth (prod _ _ F) N :- !,
    (pi x\ type-depth (F x) N'),
    N is N' + 1.
  type-depth _ 0.

  
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

  
  pred mk-constr-body-disj i:(term -> list indc-decl), o:int, o:(term -> term).
  mk-constr-body-disj Constructors NConstr ConstrBo :-
    if-debug ((pi x\ print-contructors (Constructors x))),
    (pi f\ std.length (Constructors f) NConstr),
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

  
  pred mk-constr-body i:list param, i:term, i:(term -> list indc-decl), o:int, o:term, o:term.
  mk-constr-body Params TypeTerm Constructors NConstr EBo Ty :-
    find-PROP TypeTerm PROP,
    mk-constr-body-disj Constructors NConstr ConstrBo,
    (pi b\ (type-to-fun PROP b :- !) => type-to-fun TypeTerm (FunTerm b)),
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

  
  pred mk-proper i:list param, i:term, i:term, o:term.
  mk-proper Params F Type EBo :-
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

  
  pred mk-fixpoint.fun i:term, i:list param, i:term, i:term, i:list term, o:term.
  mk-fixpoint.fun Pre Params Type (prod N T F) L (fun N T F') :-
    @pi-decl N T x\ mk-fixpoint.fun Pre Params Type (F x) [x | L] (F' x).
  mk-fixpoint.fun Pre Params Type _ RevL {{ bi_forall lp:F }} :-
    std.rev RevL L,
    coq.id->name "Φ" N,
    F = fun N Type Forall,
    @pi-decl N Type phi\ ( sigma AppPhi\ sigma Prem\
      AppPhi = app [phi | L],
      mk-fixpoint.forall Pre Params phi [] Type Prem,
      Forall phi = {{ bi_wand (□ lp:Prem) lp:AppPhi }}
    ).

  
  pred mk-fixpoint.forall i:term, i:list param, i:term, i:list term, i:term, o:term.
  mk-fixpoint.forall Pre Params Phi Xs (prod N T F) {{ bi_forall lp:Fun }} :-
    Fun = fun N T F',
    pi x\ mk-fixpoint.forall Pre Params Phi [x | Xs] (F x) (F' x).
  mk-fixpoint.forall Pre Params Phi RevXs _ {{ bi_wand lp:L lp:R }} :-
    std.rev RevXs Xs,
    std.map Params (x\r\ x = par _ _ _ r) Ps,
    L = app { std.append [Pre | Ps] [Phi | Xs] },
    R = app [Phi | Xs].

  
  pred mk-fixpoint i:list param, i:term, i:term, o:term.
  mk-fixpoint Params Type Pre Fixpoint :-
    mk-fixpoint.fun Pre Params Type Type [] Fixpoint',
    replace-params-bo Params Fixpoint' Fixpoint,
    if-debug (coq.say "----- Fixpoint Body" {coq.term->string Fixpoint}),
    coq.typecheck Fixpoint _ D, 
    if (D = ok) (true) (coq.error D).


  pred mk-fix-toproof i:(list term -> list term -> term -> prop), i:list param, i:term, i:list term, i:list term, i:term, o:term.
  mk-fix-toproof MK Params Pre Fixes Xs (prod N T F) (prod N T F') :-
    @pi-decl N T x\ mk-fix-toproof MK Params Pre Fixes [x | Xs] (F x) (F' x).
  mk-fix-toproof MK Params Pre Fixes RevXs _ Res :-
    std.rev RevXs Xs,
    std.map Params (x\r\ x = par _ _ _ r) Ps,
    std.map Fixes (f\r\ sigma App\ std.append [Pre | Ps] [app [f | Ps] | Xs] App, r = app App) Unfolds,
    std.map Fixes (f\r\ sigma App\ std.append Ps Xs App, r = app [f | App]) Folds,
    MK Unfolds Folds Res.
  

  pred mk-unfold-2.proof i:int, i:int, i:term, i:term, i:hole.
  mk-unfold-2.proof Ps N Proper Mono (hole Type Proof) :-
    do-intros-forall (hole Type Proof) (mk-unfold-2.proof-1 Ps N Proper Mono).

  pred mk-unfold-2.proof-1 i:int, i:int, i:term, i:term, i:hole.
  mk-unfold-2.proof-1 Ps N Proper Mono H :-
    do-iStartProof H IH', !,
    if-debug (coq.say "started proof unfold_2" {ihole->string IH'}),
    do-iIntros [iIdent (iNamed "HF"), iPure none, 
                iIntuitionistic (iIdent (iNamed "HI")), 
                iHyp "HI"] IH' (mk-unfold-2.proof-2 Ps N Proper Mono).

  pred mk-unfold-2.proof-2 i:int, i:int, i:term, i:term, i:ihole.
  mk-unfold-2.proof-2 Ps N Proper Mono IH :-
    ((copy {{ @IProper }} {{ @iProper }} :- !) => copy Mono MonoiProper'),
    type-to-fun MonoiProper' MonoiProper,
    std.map {std.iota Ps} (x\r\ r = {{ _ }}) Holes, !,
    do-iApplyLem (app [MonoiProper | Holes]) IH [(h\ sigma PType\ sigma PProof\ sigma List\ sigma Holes2\ !,
      h = hole PType PProof,
      std.iota Ps List,
      std.map List (x\r\ r = {{ _ }}) Holes2,
      coq.elaborate-skeleton (app [Proper | Holes2]) PType PProof D,
      if (D = ok) (true) (if-debug (coq.say "IProper error" D), fail)
    )] [IH1, IH2],
    if-debug (coq.say "pre apply HF" {ihole->string IH2}), !,
    do-iApplyHyp "HF" IH2 [], !,
    std.map {std.iota N} (x\r\ r = iPure none) Pures, !,
    do-iIntros {std.append [iModalIntro | Pures] [iIdent (iNamed "H"), iHyp "H", iModalIntro, iHyp "HI"]} IH1 (ih\ true).

  pred mk-unfold-2 i:list param, i:term, i:term, i:term, i:term, i:term, o:hole.
  mk-unfold-2 Params Pre Proper Mono Fix Type (hole ToProof Proof) :-
    mk-fix-toproof (u\f\res\ sigma U\ sigma F\ u = [U], f = [F], res = {{ lp:U ⊢ lp:F }}) Params Pre [Fix] [] Type ToProof', !,
    replace-params-ty Params ToProof' ToProof, !,
    if-debug (coq.say "unfold 2:" {coq.term->string ToProof}),
    mk-unfold-2.proof {std.length Params} {type-depth Type} Proper Mono (hole ToProof Proof).


  pred mk-unfold-1.proof i:int, i:int, i:term, i:term, i:term, i:hole.
  mk-unfold-1.proof Ps N Unfold2 Proper Mono (hole Type Proof) :-
    do-intros-forall (hole Type Proof) (mk-unfold-1.proof-1 Ps N Unfold2 Proper Mono).

  pred mk-unfold-1.proof-1 i:int, i:int, i:term, i:term, i:term, i:hole.
  mk-unfold-1.proof-1 Ps N Unfold2 Proper Mono H :-
    do-iStartProof H IH', !,
    if-debug (coq.say "started proof unfold_1" {ihole->string IH'}),
    std.map {std.iota N} (x\r\ r = iPure none) Pures, !,
    do-iIntros { std.append [iIdent (iNamed "HF"), iHyp "HF", iModalIntro | Pures]
                            [iIdent (iNamed "Hy")] } 
               IH' (mk-unfold-1.proof-2 Ps N Unfold2 Proper Mono).
               
  pred mk-unfold-1.proof-2 i:int, i:int, i:term, i:term, i:term, i:ihole.
  mk-unfold-1.proof-2 Ps N Unfold2 Proper Mono IH :-
    ((copy {{ @IProper }} {{ @iProper }} :- !) => copy Mono MonoiProper'),
    type-to-fun MonoiProper' MonoiProper,
    std.map {std.iota Ps} (x\r\ r = {{ _ }}) Holes, !,
    do-iApplyLem (app [MonoiProper | Holes]) IH [(h\ sigma PType\ sigma PProof\ sigma List\ sigma Holes2\ !,
      h = hole PType PProof,
      std.iota Ps List,
      std.map List (x\r\ r = {{ _ }}) Holes2,
      coq.elaborate-skeleton (app [Proper | Holes2]) PType PProof D,
      if (D = ok) (true) (if-debug (coq.say "IProper error" D), fail)
    )] [IH1, IH2],
    do-iApplyHyp "Hy" IH2 [], !,
    std.map {std.iota N} (x\r\ r = iPure none) Pures, !,
    do-iIntros {std.append [iModalIntro | Pures] [iIdent (iNamed "HF")]} IH1 (mk-unfold-1.proof-3 Ps Unfold2).

  pred mk-unfold-1.proof-3 i:int, i:term, i:ihole.
  mk-unfold-1.proof-3 Ps Unfold2 IH :-
    std.map {std.iota Ps} (x\r\ r = {{ _ }}) Holes, !,
    do-iApplyLem (app [Unfold2 | Holes]) IH [] [AppliedIH], !,
    do-iApplyHyp "HF" AppliedIH [].

  pred mk-unfold-1 i:list param, i:term, i:term, i:term, i:term, i:term, i:term, o:hole.
  mk-unfold-1 Params Unfold2 Pre Proper Mono Fix Type (hole ToProof Proof) :-
    mk-fix-toproof (u\f\res\ sigma U\ sigma F\ u = [U], f = [F], res = {{ lp:F ⊢ lp:U }}) Params Pre [Fix] [] Type ToProof', !,
    replace-params-ty Params ToProof' ToProof,!,
    if-debug (coq.say "unfold 1:" {coq.term->string ToProof}),
    mk-unfold-1.proof {std.length Params} {type-depth Type} Unfold2 Proper Mono (hole ToProof Proof),
    if-debug (coq.say "unfold 1 done").


  pred mk-unfold.proof i:int, i:term, i:term, i:hole.
  mk-unfold.proof Ps Unfold1 Unfold2 (hole Type Proof) :-
    do-intros-forall (hole Type Proof) (mk-unfold.proof-1 Ps Unfold1 Unfold2).

  pred mk-unfold.proof-1 i:int, i:term, i:term, i:hole.
  mk-unfold.proof-1 Ps Unfold1 Unfold2 H :-
    do-iStartProof H (ihole N H'), !,
    if-debug (coq.say "Started proof" {ihole->string (ihole N H')}),
    do-iAndSplit H' H1 H2,
    if-debug (coq.say "H1:" {ihole->string (ihole N H1)}),
    if-debug (coq.say "H2:" {ihole->string (ihole N H2)}),
    std.map {std.iota Ps} (x\r\ r = {{ _ }}) Holes1, !,
    do-iApplyLem (app [Unfold1 | Holes1]) (ihole N H1) [] [], !,
    std.map {std.iota Ps} (x\r\ r = {{ _ }}) Holes2, !,
    do-iApplyLem (app [Unfold2 | Holes2]) (ihole N H2) [] [].

  pred mk-unfold i:list param, i:term, i:term, i:term, i:term, i:term, o:hole.
  mk-unfold Params Unfold1 Unfold2 Pre Fix Type (hole ToProof Proof) :-
    mk-fix-toproof (u\f\res\ sigma U\ sigma F\ u = [U], f = [F], res = {{ lp:F ⊣⊢ lp:U }}) Params Pre [Fix] [] Type ToProof', !,
    replace-params-ty Params ToProof' ToProof,!,
    if-debug (coq.say "unfold:" {coq.term->string ToProof}),
    mk-unfold.proof {std.length Params} Unfold1 Unfold2 (hole ToProof Proof),
    if-debug (coq.say "unfold done").


  pred mk-iter.toproof-inner-1 i:list param, i:term, i:term, i:list term, i:term, o:term.
  mk-iter.toproof-inner-1 Params Pre Phi Xs (prod N T F) {{ bi_forall lp:Fun }} :-
    Fun = fun N T F',
    @pi-decl N T x\ mk-iter.toproof-inner-1 Params Pre Phi [x | Xs] (F x) (F' x).
  mk-iter.toproof-inner-1 Params Pre Phi RevXs _ {{ bi_wand lp:L lp:R }} :-
    std.rev RevXs Xs,
    std.map Params (x\r\ x = par _ _ _ r) Ps,
    L = app {std.append [Pre | Ps] [Phi | Xs]},
    R = app [Phi | Xs].

  pred mk-iter.toproof-inner-2 i:list param, i:term, i:term, i:list term, i:term, o:term.
  mk-iter.toproof-inner-2 Params Fix Phi Xs (prod N T F) {{ bi_forall lp:Fun }} :-
    Fun = fun N T F',
    @pi-decl N T x\ mk-iter.toproof-inner-2 Params Fix Phi [x | Xs] (F x) (F' x).
  mk-iter.toproof-inner-2 Params Fix Phi RevXs _ {{ bi_wand lp:L lp:R }} :-
    std.rev RevXs Xs,
    std.map Params (x\r\ x = par _ _ _ r) Ps,
    L = app {std.append [Fix | Ps] Xs},
    R = app [Phi | Xs].

  pred mk-iter.toproof i:list param, i:term, i:term, i:term, o:term.
  mk-iter.toproof Params Pre Fix Type (prod N Type F) :-
    coq.id->name "Φ" N,
    (pi phi\ mk-iter.toproof-2 Params Pre Fix Type phi (F phi)).
  
  pred mk-iter.toproof-2 i:list param, i:term, i:term, i:term, i:term, o:term.
  mk-iter.toproof-2 Params Pre Fix Type Phi ToProof :-
    mk-iter.toproof-inner-1 Params Pre Phi [] Type Assump,
    mk-iter.toproof-inner-2 Params Fix Phi [] Type Prem,
    ToProof = {{ (□ lp:Assump) -∗ lp:Prem }}.

  pred mk-iter.proof i:int, i:hole.
  mk-iter.proof N (hole Type Proof) :-
    do-intros-forall (hole Type Proof) (mk-iter.proof-1 N).

  pred mk-iter.proof-1 i:int, i:hole.
  mk-iter.proof-1 N H :-
    do-iStartProof H IH, !,
    std.map { std.iota N } (x\r\ r = iPure none) Pures, !,
    do-iIntros {std.append [iIntuitionistic (iIdent (iNamed "Hphi")) | Pures]
                           [iIdent (iNamed "HF"), iHyp "HF", iHyp "Hphi"]}
               IH (ih\ true).
  
  pred mk-iter i:list param, i:term, i:term, i:term, o:hole.
  mk-iter Params Pre Fix Type (hole ToProof Proof) :- 
    mk-iter.toproof Params Pre Fix Type ToProof', !,
    replace-params-ty Params ToProof' ToProof, !,
    if-debug (coq.say "iter to proof" {coq.term->string ToProof}), !,
    mk-iter.proof {type-depth Type} (hole ToProof Proof),
    if-debug (coq.say "iter proof finished").


  pred mk-ind.toproof i:list param, i:term, i:term, i:term, o:term.
  mk-ind.toproof Params Pre Fix Type (prod N Type F) :-
    coq.id->name "Φ" N,
    (pi phi\ mk-ind.toproof-2 Params Pre Fix Type phi (F phi)).
  
  pred mk-ind.toproof-2 i:list param, i:term, i:term, i:term, i:term, o:term.
  mk-ind.toproof-2 Params Pre Fix Type Phi {{ (□ lp:L) -∗ lp:R }} :-
    mk-ind.toproof-inner Params Pre Fix Phi [] Type Type L,
    mk-iter.toproof-inner-2 Params Fix Phi [] Type R.

  pred mk-ind.toproof-fun i:list param, i:term, i:term, i:list term, i:term, o:term.
  mk-ind.toproof-fun Params Phi Fix Xs (prod N T F) (fun N T F') :-
    pi x\ mk-ind.toproof-fun Params Phi Fix [x | Xs] (F x) (F' x).
  mk-ind.toproof-fun Params Phi Fix RevXs _ Res :-
    std.rev RevXs Xs,
    std.map Params (x\r\ x = par _ _ _ r) Ps,
    L = app [Phi | Xs],
    R = app [Fix | {std.append Ps Xs}],
    Res = {{ bi_and lp:L lp:R }}.

  pred mk-ind.toproof-inner i:list param, i:term, i:term, i:term, i:list term, i:term, i:term, o:term.
  mk-ind.toproof-inner Params Pre Fix Phi Xs Type (prod N T F) {{ bi_forall lp:Fun }} :-
    Fun = fun N T F',
    @pi-decl N T x\ mk-ind.toproof-inner Params Pre Fix Phi [x | Xs] Type (F x) (F' x).
  mk-ind.toproof-inner Params Pre Fix Phi RevXs Type _ {{ bi_wand lp:L lp:R }} :-
    std.rev RevXs Xs,
    std.map Params (x\r\ x = par _ _ _ r) Ps,
    mk-ind.toproof-fun Params Phi Fix [] Type IH,
    L = app {std.append [Pre | Ps] [IH | Xs]},
    R = app [Phi | Xs].

  pred mk-ind.proof i:int, i:int, i:term, i:term, i:term, i:term, i:term, i:hole.
  mk-ind.proof Ps N Unfold1 Unfold2 Proper Mono Iter (hole Type Proof) :-
    do-intros-forall (hole Type Proof) (mk-ind.proof-1 Ps N Unfold1 Unfold2 Proper Mono Iter).
  
  pred mk-ind.proof-1 i:int, i:int, i:term, i:term, i:term, i:term, i:term i:hole.
  mk-ind.proof-1 Ps N Unfold1 Unfold2 Proper Mono Iter H :-
    do-iStartProof H IH, !,
    std.map {std.iota N} (x\r\ r = iPure none) Pures, !,
    do-iIntros {std.append [iIntuitionistic (iIdent (iNamed "Hmon")) | Pures] 
                           [iIdent (iNamed "Hx"), iHyp "Hmon"]} IH (mk-ind.proof-2 Ps N Unfold1 Unfold2 Proper Mono Iter).

  pred mk-ind.proof-2 i:int, i:int, i:term, i:term, i:term, i:term, i:term, i:ihole.
  mk-ind.proof-2 Ps N Unfold1 Unfold2 Proper Mono Iter (ihole IN H) :-
    do-iEvalIn (iNamed "Hx") H IH H1,
    do-iApplyLem Unfold1 IH [] [], !,
    % Apply Monotinicity
    ((copy {{ @IProper }} {{ @iProper }} :- !) => copy Mono MonoiProper'),
    type-to-fun MonoiProper' MonoiProper,
    std.map {std.iota Ps} (x\r\ r = {{ _ }}) Holes, !,
    do-iApplyLem (app [MonoiProper | Holes]) (ihole IN H1) [(h\ sigma PType\ sigma PProof\ sigma List\ sigma Holes'\ sigma PTypeString\ !,
      h = hole PType PProof,
      std.iota Ps List,
      std.map List (x\r\ r = {{ _ }}) Holes',
      coq.elaborate-skeleton (app [Proper | Holes']) PType PProof D,
      if (D = ok) (true) (if-debug (coq.say "IProper error" D), fail)
    )] [(ihole N2 H2), IH2], !,
    do-iApplyHyp "Hx" IH2 [], !,
    % Continue proof
    do-iModIntro H2 H3,
    do-iApplyLem Iter (ihole N2 H3) [] [IH3],
    std.map {std.iota N} (x\r\ r = iPure none) Pures, !,
    do-iIntros {std.append [iModalIntro | Pures] [iIdent (iNamed "Hilp")]} IH3 (mk-ind.proof-3 Ps N Unfold2 Proper Mono).

  pred mk-ind.proof-3 i:int, i:int, i:term, i:term, i:term, i:ihole.
  mk-ind.proof-3 Ps N Unfold2 Proper Mono (ihole IN H) :-
    do-iAndSplit H H1 H2,!,
    % Left branch
    do-iApplyHyp "Hmon" (ihole IN H1) [IH1],!,
    do-iApplyHyp "Hilp" IH1 [],!,
    % Right branch
    do-iApplyLem Unfold2 (ihole IN H2) [] [IH2],!,
    % Apply Mono
    ((copy {{ @IProper }} {{ @iProper }} :- !) => copy Mono MonoiProper'),
    type-to-fun MonoiProper' MonoiProper,
    std.map {std.iota Ps} (x\r\ r = {{ _ }}) Holes, !,
    do-iApplyLem (app [MonoiProper | Holes]) IH2 [(h\ sigma PType\ sigma PProof\ sigma List\ sigma Holes'\ !,
      h = hole PType PProof,
      std.iota Ps List,
      std.map List (x\r\ r = {{ _ }}) Holes',
      coq.elaborate-skeleton (app [Proper | Holes']) PType PProof D,
      if (D = ok) (true) (if-debug (coq.say "IProper error" D), fail)
    )] [IH3, IH4],!,
    do-iApplyHyp "Hilp" IH4 [], !,
    std.map {std.iota N} (x\r\ r = iPure none) Pures, !,
    do-iIntros {std.append [iModalIntro | Pures] [iList [[iDrop, iIdent (iNamed "Hilp")]], iHyp "Hilp"]} IH3 (ih\ true).

  pred mk-ind i:list param, i:term, i:term, i:term, i:term, i:term, i:term, i:term, i:term, o:hole.
  mk-ind Params Pre Fix Unfold1 Unfold2 Proper Mono Iter Type (hole ToProof Proof) :-
    mk-ind.toproof Params Pre Fix Type ToProof',
    replace-params-ty Params ToProof' ToProof, !,
    if-debug (coq.say "ind to proof" {coq.term->string ToProof}), !,
    mk-ind.proof {std.length Params} {type-depth Type} Unfold1 Unfold2 Proper Mono Iter (hole ToProof Proof), !,
    if-debug (coq.say "ind proof finished").


  pred create-iInductive i:list param, i:indt-decl.
  create-iInductive Params' (inductive Name _In-Or-Co Arity Constructors) :-
    std.rev Params' Params,
    if-debug (coq.say Params),
    if-debug (coq.say "------ Creating inductive" Name),
    coq.arity->term Arity TypeTerm,
    if-debug (coq.say "------ With type" { coq.term->string TypeTerm }),

    mk-constr-body Params TypeTerm Constructors NConstr EBo Ty,
    if-debug (coq.say "------ typed body" { coq.term->string EBo }),
    coq.env.add-const {calc (Name ^ "_pre")} EBo Ty ff C,
    if-debug (coq.say "const" C),!,

    if (get-option "noproper" tt) (true)
      (
        mk-proper Params (global (const C)) TypeTerm Proper,
        if-debug (coq.say "Relation" {coq.term->string Proper})
      ),!,

    if (get-option "nosolver" tt) (true)
      (
      proper-proof Proper MonoProof,
      coq.env.add-const { calc (Name ^ "_pre_mono") } MonoProof Proper ff M,
      if-debug (coq.say "Mono" M)
      ),!,

    if (get-option "nofixpoint" tt) (true)
      (
      mk-fixpoint Params TypeTerm (global (const C)) Fixpoint,
      coq.env.add-const Name Fixpoint _ ff Fix,
      if-debug (coq.say "Fixpoint" Fix),

      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-pre (const Fix) (const C) NConstr)),
      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-mono (const Fix) (const M)))
      ),!,

    if (get-option "nounfold" tt) (true)
      (
      mk-unfold-2 Params (global (const C)) (global (const M)) Proper (global (const Fix)) TypeTerm (hole Unfold2Type Unfold2Proof),
      coq.env.add-const {calc (Name ^ "_unfold_2")} Unfold2Proof Unfold2Type ff U2,
      if-debug (coq.say "unfold_2" U2), !,

      mk-unfold-1 Params (global (const U2)) (global (const C)) (global (const M)) Proper (global (const Fix)) TypeTerm (hole Unfold1Type Unfold1Proof),
      coq.env.add-const {calc (Name ^ "_unfold_1")} Unfold1Proof Unfold1Type ff U1,
      if-debug (coq.say "unfold_1" U1),

      mk-unfold Params (global (const U1)) (global (const U2)) (global (const C)) (global (const Fix)) TypeTerm (hole UnfoldType UnfoldProof),
      coq.env.add-const {calc (Name ^ "_unfold")} UnfoldProof UnfoldType ff U,
      if-debug (coq.say "unfold" U)
      ),!,

    if (get-option "noiter" tt) (true)
      (
      mk-iter Params (global (const C)) (global (const Fix)) TypeTerm (hole IterType IterProof),
      coq.env.add-const {calc (Name ^ "_iter")} IterProof IterType ff IterConst,
      if-debug (coq.say "Iter" IterConst),
      
      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-iter (const Fix) (const IterConst)))
      ),!,

    if (get-option "noind" tt) (true)
      (
      mk-ind Params (global (const C)) (global (const Fix)) (global (const U1)) (global (const U2)) (global (const M)) Proper (global (const IterConst)) TypeTerm (hole IndType IndProof), !,
      % if-debug (coq.say "Pre add const" {coq.term->string IndType} {coq.term->string IndProof}),
      coq.ltac.collect-goals IndProof GS SGS,
      std.forall GS (x\ coq.ltac.open show-goal x _),
      std.forall SGS (x\ coq.ltac.open show-goal x _),
      coq.env.add-const {calc (Name ^ "_ind")} IndProof IndType ff IndConst,
      if-debug (coq.say "Induction" IndConst),

      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-ind (const Fix) (const IndConst)))
      ).
  create-iInductive Params (parameter ID IK T IND) :-
    coq.id->name {calc (ID ^ "_param")} N,
    @pi-decl N T p\ create-iInductive [(par ID IK T p) | Params] (IND p).
    % pi p\ create-iInductive [(par ID IK T p) | Params] (IND p).


  main [indt-decl I] :- 
    attributes A,
    coq.parse-attributes A [
      att "debug" bool,
      att "noproper" bool,
      att "nosolver" bool,
      att "nofixpoint" bool,
      att "nounfold" bool,
      att "noiter" bool,
      att "noind" bool,
    ] Opts,
    gettimeofday Start,
    [get-option "start" Start | Opts] => (
      if (get-option "noproper" tt, not (get-option "nosolver" tt)) (coq.error "Can't do solver when noproper") (true),
      create-iInductive [] I
      ).
}}.
Elpi Typecheck.

Elpi Export EI.ind.

(* Elpi Tactic IProper_solver.
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
Elpi Export IProper_solver. *)

(* Implicit Types l : loc.

#[debug]
EI.ind 
Inductive is_list `{!heapGS Σ} : val → list val → iProp Σ :=
  | empty_is_list : is_list NONEV []
  | cons_is_list l v vs tl : l ↦ (v,tl) -∗ is_list tl vs -∗ is_list (SOMEV #l) (v :: vs). *)


Section Tests.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  EI.ind 
  Inductive is_list (q : Qp) : val → list val → iProp :=
    | empty_is_list : is_list q NONEV []
    | cons_is_list l v vs tl : l ↦{#q} (v,tl) -∗ is_list q tl vs -∗ is_list q (SOMEV #l) (v :: vs).

  Print is_list_pre.
  Check is_list_pre_mono.
  Print is_list.
  Check is_list_unfold_2.
  Check is_list_unfold_1.
  Check is_list_unfold.
  Check is_list_iter.
  Check is_list_ind.

  (* islist q ∗ islist q' ∗-∗ islist (q+q') *)
  (* islist q -> [] ∨ q <= 1 *)
  (* islist (DfracOwn q) -> |==> islist (DfracDiscarded) *)
  (* Pers islist DfracDiscarded *)

  (* Lemma least_fixpoint_ind_ei (q : Qp) (Φ : val → list val → iProp) :
    □ (∀ x y, is_list_pre q (λ x' y', Φ x' y' ∧ is_list q x' y') x y -∗ Φ x y) -∗
    ∀ x y, is_list q x y -∗ Φ x y.
  Proof using Type*.
    eiIntros "#Hmon % %".
    eiIntros "Hx @Hmon".

    notypeclasses refine (tac_eval_in _ "Hx" _ _ _ _ _ _ _).
    1: {
      pm_reflexivity.
    }
    1: {
      pm_reduce.
      eiStartProof.
      1: iApply is_list_unfold_1.
    }
    pm_reduce.

    iApply (iProper (□> .> .> bi_wand ==> .> .> bi_wand) (is_list_pre q)).
    { apply is_list_pre_mono. }
    2: { iApply "Hx". }
    eiIntros "!>".
    iApply is_list_iter.
    eiIntros "!> % % Hilp".
    iSplit.
    - eiIntros "@Hmon @Hilp".
    - iApply is_list_unfold_2.
      iApply (iProper (□> .> .> bi_wand ==> .> .> bi_wand) (is_list_pre q)).
      { apply is_list_pre_mono. }
      2: { iApply "Hilp". }
      eiIntros "!> % % [_ Hilp] @Hilp".
  Qed. *)
(* 
  Lemma least_fixpoint_ind (q : Qp) (Φ : val → list val → iProp) :
    □ (∀ x y, is_list_pre q (λ x' y', Φ x' y' ∧ is_list q x' y') x y -∗ Φ x y) -∗
    ∀ x y, is_list q x y -∗ Φ x y.
  Proof using Type*.
    iIntros "#Hmon" (x y).
    rewrite is_list_unfold_1.
    iIntros "Hx".
    eiIntros "@Hmon".
    iApply (iProper (□> .> .> bi_wand ==> .> .> bi_wand) (is_list_pre q)).
    { apply is_list_pre_mono. }
    2: { iApply "Hx". }
    iModIntro.
    iApply is_list_iter.
    iIntros "!>" (a b) "Hilp".
    iSplit.
    - iApply "Hmon". iApply "Hilp".
    - iApply is_list_unfold_2.
      iApply (iProper (□> .> .> bi_wand ==> .> .> bi_wand) (is_list_pre q)).
      { apply is_list_pre_mono. }
      2: { iApply "Hilp". }
      iIntros "!>" (c d) "Hilp".
      iDestruct "Hilp" as "[_ $]".
  Qed. *)

  Lemma ind_test_1 (q q' : Qp) (v : val) (vs : list val) :
    is_list q v vs ∗ is_list q' v vs ∗-∗ is_list (q+q') v vs.
  Proof.
    iSplit.
    - eiIntros "[Hq Hq']".
      iRevert "Hq'".
      iApply (is_list_ind q (λ v vs, is_list q' v vs -∗ is_list (q + q') v vs)%I with "[] Hq").
      iIntros "!> %x %y [IH|IH]"; iIntros "Hq'".
      + iDestruct "IH" as "[%l' [%v' [%vs' [%tl' (Hl' & IH & %Hx & %Hy)]]]]". 
        simplify_eq.
        iApply is_list_unfold_2.
        iLeft.
        iExists l', v', vs', tl'.
        (* iPoseProofCore (is_list_unfold _ _ _) as true (fun Heq => idtac Heq;
        eapply (tac_rewrite_in _ Heq _ _ "Hq'" _ _ Right)).
        1: {
          pm_reflexivity.
        }
        1: {
          pm_reflexivity.
        }
        1: {
          tc_solve || let P := match goal with |- IntoInternalEq ?P _ _ => P end in fail "iRewrite:" P "not an equality".
          
        } *)
        (* iRewrite is_list_unfold in "Hq'". *)
        iEval (rewrite is_list_unfold) in "Hq'".
        iDestruct "Hq'" as "[[%l'' [%v'' [%vs'' [%tl'' (Hl & Hilq' & %Hl & %Hv)]]]] | [%Hl %Hv]]"; simplify_eq.
        iCombine "Hl' Hl" as "Hl" gives %[_ ?]; simplify_eq.
        iFrame.
        admit.
      + iApply is_list_unfold_2.
        unfold is_list_pre.
        iRight.
        iFrame.
    - eiIntros "Hi".
      iApply (least_fixpoint_ind _ (λ v vs, is_list q v vs ∗ is_list q' v vs)%I with "[] Hi").
      iIntros "!> %x %y [IH|IH]".
      + iDestruct "IH" as "[%l [%v' [%vs' [%tl ([Hq Hq'] & [[Hiq Hiq'] _] & %Hx & %Hy)]]]]".
        iSplitL "Hq Hiq".
        * iApply is_list_unfold.
          iLeft.
          iExists l, v', vs', tl.
          iFrame.
          by iPureIntro.
        * iApply is_list_unfold.
          iLeft.
          iExists l, v', vs', tl.
          iFrame.
          by iPureIntro.
      + iDestruct "IH" as "[-> ->]".
        iSplitL.
        * iApply is_list_unfold.
          iRight.
          by iPureIntro.
        * iApply is_list_unfold.
          iRight.
          by iPureIntro.
  Admitted.

  EI.ind 
  Inductive is_l : val → iProp :=
    | empty_is_l : is_l NONEV
    | cons_is_l l v tl : l ↦ (v,tl) -∗ is_l tl -∗ is_l (SOMEV #l).

  Print is_l_pre.
  Check is_l_pre_mono.
  Print is_l.
  Check is_l_unfold_2.
  Check is_l_unfold_1.

  EI.ind 
  Inductive is_P_list : (val → iProp) → val → iProp :=
    | empty_is_P_list P : is_P_list P NONEV
    | cons_is_P_list P l v tl : l ↦ (v,tl) -∗ P v -∗ is_P_list P tl -∗ is_P_list P (SOMEV #l).

  Print is_P_list_pre.
  Check is_P_list_pre_mono.
  Print is_P_list.
  Check is_P_list_unfold_2.
  Check is_P_list_unfold_1.

  EI.ind 
  Inductive is_P2_list {A} (P : val → A → iProp) : val → list A → iProp :=
    | empty_is_P2_list : is_P2_list P NONEV []
    | cons_is_P2_list l v tl x xs : l ↦ (v,tl) -∗ P v x -∗ is_P2_list P tl xs -∗ is_P2_list P (SOMEV #l) (x :: xs).
 
  Print is_P2_list_pre.
  Check is_P2_list_pre_mono.
  Print is_P2_list.
  Check is_P2_list_unfold_2.
  Check is_P2_list_unfold_1.

End Tests.
