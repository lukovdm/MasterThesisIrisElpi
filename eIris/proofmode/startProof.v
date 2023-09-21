From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.

From eIris.common Extra Dependency "stdpp.elpi" as stdpp.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.

From eIris.proofmode Require Import split.

From iris.heap_lang Require Import proofmode.
 
Elpi Tactic eiStartProof.

Elpi Accumulate File stdpp.
Elpi Accumulate File iris_ltac.
Elpi Accumulate lp:{{
  pred refine.notypeclass i:term, i:goal, o:list sealed-goal.
  refine.notypeclass T (goal _ RawEv Ty Ev _) GS :-
    rm-evar RawEv Ev,
    @no-tc! => @keepunivs! => coq.elaborate-skeleton T Ty TR ok,
    coq.ltac.collect-goals TR GS _,
    RawEv = T,
    Ev = TR.

  pred refine.unify o:term, i:goal, o:list sealed-goal.
  refine.unify T (goal _ RawEv Ty Ev _) GS :-
    coq.say "Pre rm-evar",
    print_constraints,
    rm-evar RawEv Ev, % rm-evar throws away the evar constraint on P, but doesn't affect the name of P.
    coq.say "Post rm-evar",
    print_constraints,
    @keepunivs! => coq.elaborate-skeleton T Ty TR ok, % elaborate skeleton for some reason throws away the name of P and replaces it with elpi_ctx_entry_1_. 
    coq.ltac.collect-goals TR GS _,
    RawEv = T,
    Ev = TR.

  solve (goal _Ctx _Trigger {{ let _ := _ in _ }} _Proof [] as _G) _GL :- !,
    coq.error "iStartProof: goal is a `let`, use `simpl`, `intros x`, `iIntros (x)`, or `iIntros ""%x""".

  solve (goal _Ctx _Trigger {{ envs_entails _ _ }} _Proof [] as G) GL :- !,
    GL = [seal G].

  solve (goal _Ctx _Trigger Type _Proof [] as G) GL :- 
    refine.notypeclass {{ as_emp_valid_2 lp:Type _ _ }} G [G1, G2 | GL0],
    coq.ltac.open tc_solve G1 GL1,
    % coq.sigma.print,
    coq.ltac.open (refine.unify {{ tac_start _ _ }}) G2 GL2,
    std.append GL0 { std.append GL1 GL2 } GL.
    % coq.sigma.print.

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
    (* iStartProof.
    Show Proof. *)
    eiStartProof.
    Show Proof.
    by iIntros.
    Show Proof.
  Qed.
  
End proof.
