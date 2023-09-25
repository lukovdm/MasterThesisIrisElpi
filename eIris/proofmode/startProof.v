From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.

From eIris.common Extra Dependency "stdpp.elpi" as stdpp.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.

From iris.heap_lang Require Import proofmode.
 
Elpi Tactic eiStartProof.

Elpi Accumulate File stdpp.
Elpi Accumulate File iris_ltac.
Elpi Accumulate lp:{{
  solve (goal _Ctx _Trigger {{ let _ := _ in _ }} _Proof [] as _G) _GL :- !,
    coq.error "iStartProof: goal is a `let`, use `simpl`, `intros x`, `iIntros (x)`, or `iIntros ""%x""".

  solve (goal _Ctx _Trigger {{ envs_entails _ _ }} _Proof [] as G) GL :- !,
    GL = [seal G].

  solve (goal _Ctx _Trigger Type _Proof [] as G) GL :- 
    refine {{ as_emp_valid_2 lp:Type _ (tac_start _ _) }} G GL.
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
