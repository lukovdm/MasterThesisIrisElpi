From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode.
From eIris.proofmode Require Import split.

Elpi Tactic print_args.
Elpi Accumulate lp:{{

  kind foo type.
  type X int -> foo.
  type Y Z -> foo.

  pred test i:int, o:int.
  test M N :- (N = 1; N = 2), N is M + 1, coq.say "top branch".
  test N N :- coq.say "bottom branch".

  solve (goal _ _ _ _ Args) _ :- coq.say Args.
}}.
Elpi Typecheck.

Elpi Query lp:{{
  X 1 = Y.
}}.

Section proof. 
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Lemma and_exist_sep (P : nat -> iProp) :
    ∀ x, ((∃ y, P x ∗ P y) ∨ P 0) -∗ P 1.
  Proof.
    iStartProof.
    iIntros (x) "[[%y [Hx Hy]] | H0]". 
    eiSplitL "HR".
      - iFrame.
      - iFrame.
  Qed.
  
End proof.
