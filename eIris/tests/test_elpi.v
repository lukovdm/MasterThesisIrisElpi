From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode.
From eIris.proofmode Require Import split.

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
