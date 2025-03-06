From elpi Require Import elpi.
From iris.proofmode Require Import tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.bi Require Import bi.
From iris.algebra Require Import ofe monoid list.

From stdpp Require Import numbers.

From eIris.proofmode Require Import base inductiveDB inductive.
From eIris.proofmode Require Export reduction.
From eIris.common Extra Dependency "datatypes.elpi" as datatypes.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.
From eIris.proofmode.elpi Extra Dependency "eiris_tactics.elpi" as eiris_tactics.

From iris.heap_lang Require Import proofmode notation.

Elpi Tactic eiIntros.
Elpi Accumulate Db reduction.db.
Elpi Accumulate Db induction.db.
Elpi Accumulate File eiris_tactics.
Elpi Accumulate lp:{{
  shorten coq.ltac.{ open, thenl, all }.

  pred parse_args i:list argument, o:list intro_pat.
  parse_args [tac Intro, str Args] [iCoqIntro Intro | IPS] :- !,
    tokenize Args T, !,
    parse_ipl T IPS.
  parse_args [str Args] IPS :- !,
    tokenize Args T, !,
    parse_ipl T IPS.
  parse_args Args _ :-
    coq.ltac.fail 0 "Did not recognize arguments" Args.

  solve (goal _ _ Type Proof [str "debug" | Args]) GS :-
    gettimeofday Start,
    [get-option "debug" tt, get-option "start" Start] => (
      parse_args Args IPS, !,
      do-iStartProof (hole Type Proof) IH, !,
      do-iIntros IPS IH (ih\ set-ctx-count-proof ih _), !,
      coq.ltac.collect-goals Proof GL SG,
      all (open show-goal) GL _,
      all (open pm-reduce-goal) GL GL', !,
      all (open show-goal) GL' _,
      std.append GL' SG GS
    ).
  solve (goal _ _ Type Proof Args) GS :-
    parse_args Args IPS, !,
    do-iStartProof (hole Type Proof) IH, !,
    do-iIntros IPS IH (ih\ set-ctx-count-proof ih _), !,
    coq.ltac.collect-goals Proof GL SG,
    all (open pm-reduce-goal) GL GL',
    std.append GL' SG GS.
}}.

Elpi Tactic eiDestruct.
Elpi Accumulate Db reduction.db.
Elpi Accumulate Db induction.db.
Elpi Accumulate File eiris_tactics.
Elpi Accumulate lp:{{
  shorten coq.ltac.{ open, thenl, all }.

  pred parse_destruct_args i:list argument, o:ident, o:intro_pat.
  parse_destruct_args [str IDS, str Args] (iNamed IDS) IP :- !,
    tokenize Args T, !,
    parse_ipl T [IP].
  parse_destruct_args Args _ _ :-
    coq.ltac.fail 0 "Did not recognize arguments" Args.

  solve (goal _ _ Type Proof [str "debug" | Args]) GS :-
    gettimeofday Start,
    [get-option "debug" tt, get-option "start" Start] => (
      parse_destruct_args Args ID IP, !,
      do-iStartProof (hole Type Proof) IH, !,
      do-iDestruct ID IP IH (ih\ set-ctx-count-proof ih _), !,
      coq.ltac.collect-goals Proof GL SG,
      all (open pm-reduce-goal) GL GL',
      all (open show-goal) GL' _,
      std.append GL' SG GS
    ).
  solve (goal _ _ Type Proof Args) GS :-
    parse_destruct_args Args ID IP, !,
    do-iStartProof (hole Type Proof) IH, !,
    do-iDestruct ID IP IH (ih\ set-ctx-count-proof ih _), !,
    coq.ltac.collect-goals Proof GL SG,
    all (open pm-reduce-goal) GL GL',
    std.append GL' SG GS.
}}.

Elpi Tactic eiInduction.
Elpi Accumulate File datatypes.
Elpi Accumulate Db reduction.db.
Elpi Accumulate Db induction.db.
Elpi Accumulate File eiris_tactics.
Elpi Accumulate lp:{{
  shorten coq.ltac.{ open, thenl, all }.
 
  pred do-iInduction i:ident, i:intro_pat, i:ihole, o:(ihole -> prop).
  do-iInduction ID IP (ihole _ (hole Type _) as IH) C :-
    find-hyp ID Type (app [global GREF | Args]),
    inductive-ind GREF INDLem, !,
    if-debug (coq.say "Induction on" INDLem Args),
    inductive-type GREF IInd, !,
    if-debug (coq.say "with Type" IInd),
    do-iInduction.inner ID IP IInd (app [global INDLem]) Args IH C. % Maybe add a hole

  pred do-iInduction.inner i:ident, i:intro_pat, i:iind, i:term, i:list term, i:ihole, o:(ihole -> prop).
  do-iInduction.inner ID IP (iind NConstr TypeTerm) (app INDLem) Args (ihole _ (hole Type _) as IH) C :-
    Type = {{ envs_entails _ lp:P }},
    std.map Args (x\r\ sigma N T I\ decl x N T, coq.name->id N I, r = par I _ T x ) Pars, !,
    replace-params-bo Pars P Phi, !,
    if-debug (coq.say "phi is" Phi),
    Lem = app {std.append INDLem [Phi]},
    if-debug (coq.say "Lem to apply" Lem),
    % Apply induction lemma
    do-iApplyLem Lem IH [] [IntroIH, IHyp],
    % Apply induction hyp to goal
    do-iApplySimpleExact IHyp ID,
    if-debug (coq.say "hole left:" {ihole->string IntroIH}),
    % Introduce created goal
    std.map {std.iota {type-depth TypeTerm } } (x\r\ r = iPure none) Pures,
    if (IP = iAll) (
        IP' = iList {std.map {std.iota NConstr} (x\r\ r = [iFresh])}
      ) (IP' = IP),
    do-iIntros {std.append [iModalIntro| Pures] [IP']} IntroIH C.
  do-iInduction.inner HID IP (iind_param _ _ IND) (app INDLem) [A | Args] IH C :-
    pi p\ do-iInduction.inner HID IP (IND p) (app {std.append INDLem [A]}) Args IH C.


  pred parse_destruct_args i:list argument, o:ident, o:intro_pat.
  parse_destruct_args [str IDS, str Args] (iNamed IDS) IP :- !,
    tokenize Args T, !,
    parse_ipl T [IP].
  parse_destruct_args Args _ _ :-
    coq.ltac.fail 0 "Did not recognize arguments" Args.

  solve (goal _ _ Type Proof [str "debug" | Args]) GS :- !,
    gettimeofday Start,
    [get-option "debug" tt, get-option "start" Start] => (
      parse_destruct_args Args ID IP, !,
      do-iStartProof (hole Type Proof) IH, !,
      do-iInduction ID IP IH (ih\ set-ctx-count-proof ih _), !,
      if-debug (coq.say "Induction done"),
      coq.ltac.collect-goals Proof GL SG, !,
      all (open pm-reduce-goal) GL GL', !,
      all (open show-goal) GL' _, !,
      std.append GL' SG GS
    ).
  solve (goal _ _ Type Proof Args) GS :-
    parse_destruct_args Args ID IP, !,
    do-iStartProof (hole Type Proof) IH, !,
    do-iInduction ID IP IH (ih\ set-ctx-count-proof ih _), !,
    coq.ltac.collect-goals Proof GL SG,
    all (open pm-reduce-goal) GL GL',
    std.append GL' SG GS.
}}.

Tactic Notation "eiIntros" string(x) :=
  elpi eiIntros ltac_string:(x).

Tactic Notation "eiDestruct" string(x) "as" string(y) :=
  elpi eiDestruct ltac_string:(x) ltac_string:(y).

Tactic Notation "eiDestruct" string(x) :=
  elpi eiDestruct ltac_string:(x) "**".

Tactic Notation "eiInduction" string(x) "as" string(y) :=
  elpi eiInduction "debug" ltac_string:(x) ltac_string:(y).

Tactic Notation "eiInduction" string(x) :=
  elpi eiInduction "debug" ltac_string:(x) "**".
