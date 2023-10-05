From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode.
(* From eIris.proofmode Require Import split. *)

Elpi Tactic print_args.
Elpi Accumulate lp:{{
  solve (goal _ _ _ _ Args) _ :- coq.say Args.
}}.
Elpi Typecheck.

Lemma demo (P : Prop) :
  P -> P.
Proof.
  intros.
  elpi print_args (P) "asdf" 123.

Section proof. 
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Lemma and_exist_sep (P R : iProp) :
    P -∗ R -∗ R ∗ P.
  Proof.
    iIntros "HP HR".
    eiSplitL "HR".
      - iFrame.
      - iFrame.
  Qed.
  
End proof.
