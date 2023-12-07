From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.

From eIris.proofmode Require Import base reduction.
From eIris.common Extra Dependency "stdpp.elpi" as stdpp.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.

Elpi Tactic eiSplitL.

Ltac helper_eiSplit SIDE HS := eapply tac_sep_split with SIDE HS _ _.

Elpi Accumulate File stdpp.
Elpi Accumulate Db reduction.db.
Elpi Accumulate File iris_ltac.
Elpi Accumulate lp:{{
  type sep_split term -> term -> open-tactic.
    sep_split SIDE HS G GL :- coq.ltac.call "helper_eiSplit" [trm SIDE, trm HS] G GL.

  solve (goal _Ctx _Trigger _Type _Proof [trm SIDE, str HSS] as G) GL :-
    rex.split " " HSS HS,
    std.map HS string->stringterm HTS,
    std.map HTS (x\ r\ r = {{ INamed lp:x }}) HI,
    list->listterm HI TI,
    coq.typecheck TI {{ list _ }} ok, % Fill in any holes created when contructing the term
    sep_split SIDE TI G [G0, G1 | GL0],
    coq.ltac.open tc_solve G0 GL1,
    coq.ltac.open pm_reduce G1 [G3 | GL2],
    coq.ltac.open split G3 GL3,
    std.append { std.append { std.append GL0 GL1 } GL2 } GL3 GL.
}}.
Elpi Typecheck.

Tactic Notation "eiSplitL" string(t) :=
  elpi eiSplitL (Left) ltac_string:(t).

Tactic Notation "eiSplitR" string(t) :=
  elpi eiSplitL (Right) ltac_string:(t).

(* Parse intro patterns of iIntros *)
(* iInduction *)
