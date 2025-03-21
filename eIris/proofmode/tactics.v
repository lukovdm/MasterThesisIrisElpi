From elpi Require Import elpi.
From iris.proofmode Require Import tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.bi Require Import bi.
From iris.algebra Require Import ofe monoid list.

From stdpp Require Import numbers.

From eIris.proofmode Require Import base inductiveDB.
From eIris.proofmode Require Export reduction.
From eIris.common Extra Dependency "datatypes.elpi" as datatypes.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.
From eIris.proofmode.elpi Extra Dependency "eiris_tactics.elpi" as eiris_tactics.

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

  solve (goal _ _ _ Proof [str "debug" | Args] as G) GS :-
    gettimeofday Start,
    [get-option "debug" tt, get-option "start" Start] => (
      parse_args Args IPS, !,
      eiOfCoqProof G IH, !,
      eiIntros IPS IH (ih\ true), !,
      coq.ltac.collect-goals Proof GL SG,
      all (open pm_reduce) GL GL', !,
      std.append GL' SG GS
    ).
  solve (goal _ _ _ Proof Args as G) GS :-
    parse_args Args IPS, !,
    eiOfCoqProof G IH, !,
    eiIntros IPS IH (ih\ true), !,
    coq.ltac.collect-goals Proof GL SG,
    all (open pm_reduce) GL GL',
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

  solve (goal _ _ _ Proof [str "debug" | Args] as G) GS :-
    gettimeofday Start,
    [get-option "debug" tt, get-option "start" Start] => (
      parse_destruct_args Args ID IP, !,
      eiOfCoqProof G IH, !,
      eiDestruct ID IP IH (ih\ true ), !,
      coq.ltac.collect-goals Proof GL SG,
      all (open pm_reduce) GL GL',
      all (open show-goal) GL' _,
      std.append GL' SG GS
    ).
  solve (goal _ _ _ Proof Args as G) GS :-
    parse_destruct_args Args ID IP, !,
    eiOfCoqProof G IH, !,
    eiDestruct ID IP IH (ih\ true ), !,
    coq.ltac.collect-goals Proof GL SG,
    all (open pm_reduce) GL GL',
    std.append GL' SG GS.
}}.

Tactic Notation "eiIntros" string(x) :=
  elpi eiIntros ltac_string:(x).

Tactic Notation "eiDestruct" string(x) "as" string(y) :=
  elpi eiDestruct ltac_string:(x) ltac_string:(y).

Tactic Notation "eiDestruct" string(x) :=
  elpi eiDestruct ltac_string:(x) "**".

Tactic Notation "eiIntrosDebug" string(x) :=
  elpi eiIntros "debug" ltac_string:(x).

Tactic Notation "eiDestructDebug" string(x) "as" string(y) :=
  elpi eiDestruct "debug" ltac_string:(x) ltac_string:(y).

Tactic Notation "eiDestructDebug" string(x) :=
  elpi eiDestruct "debug" ltac_string:(x) "**".