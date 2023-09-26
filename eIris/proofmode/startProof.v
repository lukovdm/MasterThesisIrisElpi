From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.

From eIris.common Extra Dependency "stdpp.elpi" as stdpp.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.
From eIris.proofmode.elpi Extra Dependency "eiStartProof.elpi" as startProof.

From iris.heap_lang Require Import proofmode.
 
Elpi Tactic eiStartProof.

Elpi Accumulate File stdpp.
Elpi Accumulate File iris_ltac.
Elpi Accumulate File startProof.
Elpi Accumulate lp:{{
  solve G GL :-
    startProof G GL.
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
