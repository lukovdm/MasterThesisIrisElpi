From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.

From eIris.proofmode Require Import base.
From eIris.common Extra Dependency "stdpp.elpi" as stdpp.
From eIris.common Extra Dependency "tokenize.elpi" as tokenize.
From eIris.common Extra Dependency "parser.elpi" as parser.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.
From eIris.proofmode.elpi Extra Dependency "eiris_tactics.elpi" as eiris_tactics.

From iris.heap_lang Require Import proofmode.
 
Elpi Tactic eiStartProof.
Elpi Accumulate File stdpp.
Elpi Accumulate File iris_ltac.
Elpi Accumulate File tokenize.
Elpi Accumulate File parser.
Elpi Accumulate File eiris_tactics.
Elpi Accumulate lp:{{
  solve G GL :-
    go_iStartProof G GL.
}}.
Elpi Typecheck.

Tactic Notation "eiStartProof" :=
  elpi eiStartProof.

Section proof. 
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Elpi Trace Browser.

  Lemma and_exist_sep (P : iProp) :
    P -∗ P.
  Proof.
    eiStartProof.
    by iIntros.
  Qed.
  
End proof.
