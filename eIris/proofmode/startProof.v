From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.

From eIris.proofmode Require Import base reduction inductiveDB.
From eIris.proofmode.elpi Extra Dependency "eiris_tactics.elpi" as eiris_tactics.
 
Elpi Tactic eiStartProof.
Elpi Accumulate Db reduction.db.
Elpi Accumulate Db induction.db.
Elpi Accumulate File eiris_tactics.
Elpi Accumulate lp:{{
  solve G _ :-
    eiStartProof {eiOfCoqProof G} _.
}}.

Tactic Notation "eiStartProof" :=
  elpi eiStartProof.

