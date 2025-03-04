From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.bi Require Export bi telescopes.

From eIris.proofmode Require Import base reduction inductiveDB.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.
From eIris.proofmode.elpi Extra Dependency "eiris_tactics.elpi" as eiris_tactics.

From iris.heap_lang Require Import proofmode.

Elpi Tactic eiApply.
Elpi Accumulate Db reduction.db.
Elpi Accumulate Db induction.db.
Elpi Accumulate File eiris_tactics.
Elpi Accumulate lp:{{
  shorten coq.ltac.{ open, thenl, all }.

  pred go-iApply i:list argument, i:hole, o:list sealed-goal.
  go-iApply [str Hyp] H GL' :-
    do-iStartProof H IH, !,
    do-iApplyHyp Hyp IH IHS, !,
    std.map IHS (x\r\ sigma Proof\ x = (ihole _ (hole _ Proof)), coq.ltac.collect-goals Proof r _) GLL,
    std.flatten GLL GL,
    all (open pm-reduce-goal) GL GL'.

  go-iApply [trm Lem] H GL' :-
    do-iStartProof H IH, !,
    do-iApplyLem Lem IH [] IHS, !,
    std.map IHS (x\r\ sigma Proof\ x = (ihole _ (hole _ Proof)), coq.ltac.collect-goals Proof r _) GLL,
    std.flatten GLL GL,
    all (open pm-reduce-goal) GL GL'.

  solve (goal _ _ Type Proof [str "debug" | Args]) GS :-
    gettimeofday Start,
    [get-option "debug" tt, get-option "start" Start] => (
      go-iApply Args (hole Type Proof) GS
    ).
  solve (goal _ _ Type Proof Args) GS :-
    go-iApply Args (hole Type Proof) GS.
}}.


Tactic Notation "eiApply" string(x) :=
  elpi eiApply ltac_string:(x).

Tactic Notation "eiApply!" string(x) :=
  elpi eiApply debug ltac_string:(x).

Tactic Notation "eiApply" constr(x) :=
  elpi eiApply ltac_term:(x).

Tactic Notation "eiApply!" uconstr(x) :=
  elpi eiApply debug ltac_term:(x).
