From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode.


Elpi Tactic show.
Elpi Accumulate lp:{{

  solve (goal Ctx _Trigger Type Proof Args) _ :-
    coq.say "Args:" Args.
    % coq.say "Goal:" Ctx "|-" Proof ":" Type,
    % coq.say "Proof state:",
    % coq.sigma.print.

}}.
Elpi Typecheck.

Tactic Notation "show" constr(t) :=
  elpi show ltac_term:(t).

Elpi Tactic eiSplitL.

Ltac helper_eiSplit HS := eapply tac_sep_split with Left HS _ _.

Elpi Accumulate File "coq/elpi_test/stdpp.elpi".
Elpi Accumulate File "coq/elpi_test/e_split1.elpi".
Elpi Typecheck.

Tactic Notation "eiSplitL" string(t) :=
elpi eiSplitL ltac_string:(t).

Elpi Trace Browser.

Section proof. 
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Lemma and_exist_sep {A} P R (Ψ: A → iProp) :
    P ∗ (∃ a, Ψ a) ∗ R -∗ ∃ a, Ψ a ∗ P.
  Proof.
    iIntros "[HP [HΨ HR]]" .
    iDestruct "HΨ" as (x) "HΨ" .
    iExists x.
    (* helper_eiSplit [INamed "HΨ"; INamed "HP"].
      - tc_solve.
      - pm_reduce.
        split. *)
    eiSplitL "HΨ HR".
    Unshelve.
      - iFrame.
      - iFrame.
      - assumption.
      - assumption. 
  Fail Qed. (* Something is going wrong, but don't know what *)
  Admitted.
  
End proof.