From elpi Require Import elpi.
From iris.proofmode Require Import base environments proofmode tactics coq_tactics reduction intro_patterns class_instances spec_patterns.
From iris.prelude Require Import options.
From iris.bi Require Import  bi.
From iris.algebra Require Import ofe monoid list.
From iris.heap_lang Require Import proofmode notation.
From stdpp Require Import base finite.

From eIris.proofmode Require Export proper.
From eIris.proofmode Require Export reduction.
From eIris.proofmode Require Import inductiveDB.
From eIris.proofmode Require Import base.
From eIris.common Extra Dependency "stdpp.elpi" as stdpp.
From eIris.common Extra Dependency "datatypes.elpi" as datatypes.
From eIris.proofmode.elpi Extra Dependency "eiris_tactics.elpi" as eiris_tactics.
From eIris.proofmode.elpi Extra Dependency "mk_inductive.elpi" as mkinductive.

#[arguments(raw)] 
Elpi Command EI.ind.
Elpi Accumulate File datatypes.
Elpi Accumulate Db reduction.db.
Elpi Accumulate Db induction.db.
Elpi Accumulate File mkinductive.
(* Elpi Query lp:{{
  coq.say {{{{ ∀ n (rec : lp:_NEType), lp:{{ F {{ n }} {{ rec }} }} }}}},
  coq.say F.
}}. *)
Elpi Accumulate lp:{{
  pred create-iInductive i:list param, i:indt-decl, o:gref, o:iind.
  create-iInductive Params' (inductive Name _In-Or-Co Arity Constructors) (const Fix) (iind NConstr TypeTerm) :-
    std.rev Params' Params,
    if-debug (coq.say Params),
    if-debug (coq.say "------ Creating inductive" Name),
    coq.arity->term Arity NETypeTerm',
    ne-to-prod NETypeTerm' TypeTerm',
    std.assert-ok! (coq.elaborate-skeleton NETypeTerm' {{ Type }} NETypeTerm) "NE Type elaboration failed",
    std.assert-ok! (coq.elaborate-skeleton TypeTerm' {{ Type }} TypeTerm) "Type elaboration failed",
    if-debug (coq.say "------ With NE type" { coq.term->string NETypeTerm } " and type" { coq.term->string TypeTerm }),

    mk-constr-body Params TypeTerm Constructors NConstr BIConstructors EBo Ty,
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

    if (get-option "noprene" tt; TypeTerm = NETypeTerm) (true)
      (
      mk-pre-ne Params TypeTerm NETypeTerm (global (const C)) (hole PreNEType PreNEProof),
      coq.env.add-const { calc (Name ^ "_pre_ne") } PreNEProof PreNEType ff PreNE,
      coq.TC.declare-instance (const PreNE) 1,
      if-debug (coq.say "Pre Non-Expansive" PreNE)
      ),!,

    if (get-option "nofixpoint" tt) (true)
      (
      mk-fixpoint Params TypeTerm NETypeTerm (global (const C)) Fixpoint,
      coq.env.add-const Name Fixpoint _ ff Fix,
      if-debug (coq.say "Fixpoint" Fix),

      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-pre (const Fix) (const C))),
      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-mono (const Fix) (const M)))
      ),!,

    if (get-option "nofixne" tt; TypeTerm = NETypeTerm) (true)
      (
      mk-fix-ne Params NETypeTerm (global (const Fix)) (hole FixNEType FixNEProof),
      coq.env.add-const { calc (Name ^ "_ne") } FixNEProof FixNEType ff FixNE,
      coq.TC.declare-instance (const FixNE) 1,
      if-debug (coq.say "Fix Non-Expansive" FixNE)
      ),!,

    if (get-option "nounfold" tt) (true)
      (
      mk-unfold-2 Params (global (const C)) (global (const M)) Proper (global (const Fix)) TypeTerm (hole Unfold2Type Unfold2Proof),
      coq.env.add-const {calc (Name ^ "_unfold_2")} Unfold2Proof Unfold2Type ff U2, !,
      if-debug (coq.say "unfold_2" U2), !,
 
      mk-unfold-1 Params (global (const U2)) (global (const C)) (global (const M)) Proper (global (const Fix)) TypeTerm
                  NETypeTerm (hole Unfold1Type Unfold1Proof), !,
      if-debug (coq.say "unfold_1 made now defining it (slow?)"), !,
      coq.env.add-const {calc (Name ^ "_unfold_1")} Unfold1Proof Unfold1Type ff U1, !,
      if-debug (coq.say "unfold_1" U1), !,

      mk-unfold Params (global (const U1)) (global (const U2)) (global (const C)) (global (const Fix)) TypeTerm (hole UnfoldType UnfoldProof),
      coq.env.add-const {calc (Name ^ "_unfold")} UnfoldProof UnfoldType ff U, !,
      if-debug (coq.say "unfold" U), !,

      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-unfold (const Fix) (const U1) (const U2) (const U) NConstr))
      ),!,

    if (get-option "noconstr" tt) (true)
      (
        std.map { std.iota NConstr } (n\ r\ mk-constr-lem Params (global (const U2)) BIConstructors EBo (global (const Fix)) TypeTerm n NConstr r) ConstrLems,
        if-debug (coq.say "Constructor Lemmas" ConstrLems)
      ), !,

    if (get-option "noiter" tt) (true)
      ( 
      mk-iter Params (global (const C)) (global (const Fix)) TypeTerm NETypeTerm (hole IterType IterProof),
      coq.env.add-const {calc (Name ^ "_iter")} IterProof IterType ff IterConst,
      if-debug (coq.say "Iter" IterConst),
      
      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-iter (const Fix) (const IterConst)))
      ),!,

    if (get-option "noind" tt) (true)
      (
      mk-ind Params (global (const C)) (global (const Fix)) (global (const U1)) (global (const U2)) (global (const M)) Proper 
                    (global (const IterConst)) TypeTerm NETypeTerm (hole IndType IndProof), !,
      coq.ltac.collect-goals IndProof GS SGS,
      if-debug (std.forall GS (x\ coq.ltac.open show-goal x _)),
      if-debug (std.forall SGS (x\ coq.ltac.open show-goal x _)),
      coq.env.add-const {calc (Name ^ "_ind")} IndProof IndType ff IndConst,
      if-debug (coq.say "Induction" IndConst),

      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-ind (const Fix) (const IndConst)))
      ).
  create-iInductive Params (parameter ID IK T IND) Fix (iind_param ID T IInd') :-
    coq.id->name {calc (ID ^ "_param")} N,
    @pi-decl N T p\ create-iInductive [(par ID IK T p) | Params] (IND p) Fix (IInd' p).
 
  main [indt-decl I] :- 
    attributes A,
    coq.parse-attributes A [
      att "debug" bool,
      att "noproper" bool,
      att "nosolver" bool,
      att "noprene" bool,
      att "nofixpoint" bool,
      att "nofixne" bool,
      att "nounfold" bool,
      att "noconstr" bool,
      att "noiter" bool,
      att "noind" bool,
    ] Opts,
    gettimeofday Start,
    [get-option "start" Start | Opts] => (
      if (get-option "noproper" tt, not (get-option "nosolver" tt)) (coq.error "Can't do solver when noproper") (true),
      create-iInductive [] I Fix IInd,
      if-debug (coq.say "Storing" IInd),
      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-type Fix IInd))
    ).
}}.
Elpi Export EI.ind.
