From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode.

From eIris.common Extra Dependency "stdpp.elpi" as stdpp.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.

Elpi Tactic eiSplitL.

Ltac helper_eiSplit HS := eapply tac_sep_split with Left HS _ _.

(* TODO: Look at how to use refine instead of eapply here or in another tactic*)
Elpi Accumulate File stdpp.
Elpi Accumulate File iris_ltac.
Elpi Accumulate lp:{{
  type sep_split term -> open-tactic.
    sep_split HS G GL :- coq.ltac.call "helper_eiSplit" [trm HS] G GL.

  solve (goal _Ctx _Trigger _Type _Proof [str HSS] as G) GL :-
    rex.split " " HSS HS,
    std.map HS string->stringterm HTS,
    std.map HTS (x\ r\ r = {{ INamed lp:x }}) HI,
    list->listterm HI TI,
    coq.typecheck TI {{ list ident }} ok, % Fill in any holes created when contructing the term
    sep_split TI G [G0, G1 | GL0],
    coq.ltac.open tc_solve G0 GL1,
    coq.ltac.open pm_reduce G1 [G3 | GL2],
    coq.ltac.open split G3 GL3,
    std.append { std.append { std.append GL0 GL1 } GL2 } GL3 GL.
}}.
Elpi Typecheck.

Tactic Notation "eiSplitL" string(t) :=
  elpi eiSplitL ltac_string:(t).