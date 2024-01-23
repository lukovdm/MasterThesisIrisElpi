From elpi Require Import elpi.
From iris.proofmode Require Import base environments proofmode tactics coq_tactics reduction intro_patterns class_instances spec_patterns.
From iris.prelude Require Import options.
From iris.bi Require Import  bi.
From iris.algebra Require Import ofe monoid list.
From iris.heap_lang Require Import proofmode notation.
From stdpp Require Import base finite.

From eIris.proofmode Require Export proper.
From eIris.proofmode Require Import reduction.
From eIris.proofmode Require Import inductiveDB.
From eIris.proofmode Require Import base.
(* From eIris.proofmode Require Import intros apply startProof. *)
From eIris.proofmode.elpi Extra Dependency "mk_inductive.elpi" as mkinductive.

#[arguments(raw)] 
Elpi Command EI.ind.
Elpi Accumulate Db reduction.db.
Elpi Accumulate Db induction.db.
Elpi Accumulate File mkinductive.
Elpi Accumulate lp:{{
  pred constr-in-prebody i:term, i:list term, i:option term, i:list term, i:int, i:int, o:term.
  constr-in-prebody Pre Ps Fix Xs Nth Total Res :- 
    if-debug (coq.say "constr-in-prebody" {coq.term->string Pre} Ps Fix Xs Nth Total Res), fail.
  constr-in-prebody (fun _ _ F) [P | Ps] Fix Xs Nth Total Res :- !,
    constr-in-prebody (F P) Ps Fix Xs Nth Total Res.
  constr-in-prebody (fun _ _ F) [] (some Fix) Xs Nth Total Res :- !,
    constr-in-prebody (F Fix) [] none Xs Nth Total Res.
  constr-in-prebody (fun _ _ F) [] none [X | Xs] Nth Total Res :- !,
    constr-in-prebody (F X) [] none Xs Nth Total Res.
  constr-in-prebody (app [_, _, _, R]) [] none [] 1 2 R :- !.
  constr-in-prebody (app [_, _, L, _]) [] none [] 0 _ L :- !.
  constr-in-prebody (app [_, _, _, R]) [] none [] Nth Total Res :- !,
    constr-in-prebody R [] none [] { calc (Nth - 1) } { calc (Total - 1) } Res.


  pred mk-constr-lem.toproof i:list param, i:term, i:term, i:term, i:int, i:int, i:list term, i:list term, o:term.
  mk-constr-lem.toproof [(par ID _ T C) | Params] PreBody Fix Type Nth Total Ps [] (prod N T F) :- !,
    coq.id->name ID N,
    mk-constr-lem.toproof Params PreBody Fix Type Nth Total [C | Ps] [] Lem,
    pi x\ (copy C x :- !) => copy Lem (F x).
  mk-constr-lem.toproof [] PreBody Fix (prod N T F) Nth Total Ps Xs (prod N T F') :- !,
    @pi-decl N T x\ mk-constr-lem.toproof [] PreBody Fix (F x) Nth Total Ps [x | Xs] (F' x).
  mk-constr-lem.toproof [] PreBody Fix _ Nth Total PsRev XsRev {{ lp:Constr -∗ lp:FixTerm }} :- !,
    std.rev PsRev Ps,
    std.rev XsRev Xs,
    constr-in-prebody PreBody Ps (some (app [Fix | Ps])) Xs Nth Total Constr,
    FixTerm = app {std.append [Fix | Ps] Xs}.

  pred mk-constr-lem.proof i:term, i:int, i:int, i:int, i:hole.
  mk-constr-lem.proof Unfold2 Ps Nth Total (hole Type Proof) :-
    do-intros-forall (hole Type Proof) (mk-constr-lem.proof-1 Unfold2 Ps Nth Total).

  pred mk-constr-lem.proof-1 i:term, i:int, i:int, i:int, i:hole.
  mk-constr-lem.proof-1 Unfold2 Ps Nth Total H :-
    do-iStartProof H IH, !,
    do-iIntros [iIdent (iNamed "H")] IH (mk-constr-lem.proof-2 Unfold2 Ps Nth Total).

  pred mk-constr-lem.proof-2 i:term, i:int, i:int, i:int, i:ihole.
  mk-constr-lem.proof-2 Unfold2 Ps Nth Total IH :-
    std.map {std.iota Ps} (x\r\ r = {{ _ }}) Holes, !,
    do-iApplyLem (app [Unfold2 | Holes]) IH [] [AppliedIH], !,
    mk-constr-lem.proof-3 Nth Total AppliedIH.

  pred mk-constr-lem.proof-3 i:int, i:int, i:ihole.
  mk-constr-lem.proof-3 1 2 (ihole N H) :- !,
    do-iRight H H', !,
    do-iApplyHyp "H" (ihole N H') [].
  mk-constr-lem.proof-3 0 _ (ihole N H) :- !,
    do-iLeft H H', !,
    do-iApplyHyp "H" (ihole N H') [].
  mk-constr-lem.proof-3 Nth Total (ihole N H) :- !,
    do-iRight H H', !,
    mk-constr-lem.proof-3 { calc (Nth - 1) } {calc (Total - 1)} (ihole N H').

  pred mk-constr-lem i:list param, i:term, i:(term -> list indc-decl), i:term, i:term, i:term, i:int, i:int, o:constant.
  mk-constr-lem Params Unfold2 Constructors PreBody Fix Type Nth Total ConstrLem :-
    mk-constr-lem.toproof Params PreBody Fix Type Nth Total [] [] ConstrType,
    if-debug (coq.say "----- Constr Lemma" { coq.term->string ConstrType } ),
    mk-constr-lem.proof Unfold2 {std.length Params} Nth Total (hole ConstrType ConstrProof),
    
    std.nth Nth (Constructors Fix) (constructor Name _),
    coq.env.add-const Name ConstrProof ConstrType ff ConstrLem.


  pred create-iInductive i:list param, i:indt-decl, o:gref , o:indt-decl.
  create-iInductive Params' (inductive Name In-Or-Co Arity Constructors) (const Fix) (inductive Name In-Or-Co Arity BIConstructors) :-
    std.rev Params' Params,
    if-debug (coq.say Params),
    if-debug (coq.say "------ Creating inductive" Name),
    coq.arity->term Arity TypeTerm,
    if-debug (coq.say "------ With type" { coq.term->string TypeTerm }),

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

    if (get-option "nofixpoint" tt) (true)
      (
      mk-fixpoint Params TypeTerm (global (const C)) Fixpoint,
      coq.env.add-const Name Fixpoint _ ff Fix,
      if-debug (coq.say "Fixpoint" Fix),

      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-pre (const Fix) (const C))),
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
      if-debug (coq.say "unfold" U),

      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-unfold (const Fix) (const U1) (const U2) (const U) NConstr))
      ),!,

    if (get-option "noconstr" tt) (true)
      (
        std.map { std.iota NConstr } (n\ r\ mk-constr-lem Params (global (const U2)) BIConstructors EBo (global (const Fix)) TypeTerm n NConstr r) ConstrLems,
        if-debug (coq.say "Constructor Lemmas" ConstrLems)
      ), !,

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
      coq.ltac.collect-goals IndProof GS SGS,
      std.forall GS (x\ coq.ltac.open show-goal x _),
      std.forall SGS (x\ coq.ltac.open show-goal x _),
      coq.env.add-const {calc (Name ^ "_ind")} IndProof IndType ff IndConst,
      if-debug (coq.say "Induction" IndConst),

      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-ind (const Fix) (const IndConst)))
      ).
  create-iInductive Params (parameter ID IK T IND) Fix (parameter ID IK T IND') :-
    coq.id->name {calc (ID ^ "_param")} N,
    @pi-decl N T p\ create-iInductive [(par ID IK T p) | Params] (IND p) Fix (IND' p).

  main [indt-decl I] :- 
    attributes A,
    coq.parse-attributes A [
      att "debug" bool,
      att "noproper" bool,
      att "nosolver" bool,
      att "nofixpoint" bool,
      att "nounfold" bool,
      att "noconstr" bool,
      att "noiter" bool,
      att "noind" bool,
    ] Opts,
    gettimeofday Start,
    [get-option "start" Start | Opts] => (
      if (get-option "noproper" tt, not (get-option "nosolver" tt)) (coq.error "Can't do solver when noproper") (true),
      create-iInductive [] I Fix I',
      % if-debug (coq.say "saving type" Fix I'),
      coq.elpi.accumulate _ "induction.db" (clause _ _ (inductive-type Fix I'))
    ).
}}.
Elpi Typecheck.
Elpi Export EI.ind.

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

  (* EI.ind 
  Inductive is_list (q : Qp) : val → list val → iProp :=
    | empty_is_list : is_list q NONEV []
    | cons_is_list l v vs tl : l ↦{#q} (v,tl) -∗ is_list q tl vs -∗ is_list q (SOMEV #l) (v :: vs).

  Print is_list_pre.
  Check is_list_pre_mono.
  Print is_list.
  Check is_list_unfold_2.
  Check is_list_unfold_1.
  Check is_list_unfold.
  Check empty_is_list.
  Check cons_is_list.
  Check is_list_iter.
  Check is_list_ind.

  (* islist q ∗ islist q' ∗-∗ islist (q+q') *)
  (* islist q -> [] ∨ q <= 1 *)
  (* islist (DfracOwn q) -> |==> islist (DfracDiscarded) *)
  (* Pers islist DfracDiscarded *)

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
  Check empty_is_P2_list. *)

End Tests.
