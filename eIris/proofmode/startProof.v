From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.

From eIris.proofmode Require Import base reduction inductiveDB.
From eIris.proofmode.elpi Extra Dependency "eiris_tactics.elpi" as eiris_tactics.

From iris.heap_lang Require Import proofmode.
 
Elpi Tactic eiStartProof.
Elpi Accumulate Db reduction.db.
Elpi Accumulate Db induction.db.
Elpi Accumulate File eiris_tactics.
Elpi Accumulate lp:{{
  solve (goal _ _ Type Proof _) _ :-
    do-iStartProof (hole Type Proof) _.
}}.

Tactic Notation "eiStartProof" :=
  elpi eiStartProof.

Section proof. 
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Lemma and_exist_sep (P : iProp) :
    P -∗ P.
  Proof.
    eiStartProof.
    by iIntros.
  Qed.
  
End proof.
