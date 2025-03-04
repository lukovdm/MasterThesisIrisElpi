From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode notation array.

From eIris.proofmode Require Import base reduction inductive intros.

Section SkipQueue.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l nl : loc.

  EI.ind
  Inductive is_lll : loc → loc → list val → iProp :=
      | end_is_lll (n : nat) l vl :
          l ↦ #n -∗ 
          (l +ₗ 1) ↦ NONEV -∗
          (l +ₗ 2) ↦∗ vl -∗ ⌜length vl = n⌝ -∗ 
          is_lll l l vl
      | cons_is_lll (n : nat) l nl tl vl vl' : 
          l ↦ #n -∗ 
          (l +ₗ 1) ↦ #nl -∗ is_lll nl tl vl' -∗
          (l +ₗ 2) ↦∗ vl -∗ ⌜length vl = n⌝ -∗ 
          is_lll l tl (vl ++ vl').
  
  Print is_lll_pre.

  Definition new_lll : val := λ: "l" "n",
    let: "end" := AllocN ("n" + #2) #() in
    ("end" +ₗ #0) <- "n";;
    array_copy_to ("end" +ₗ #2) "l" "n";;
    ("end", "end").

  Definition enqueue : val := λ: "tl" "l" "n",
    let: "end" := new_lll "l" "n" in
    ("tl" +ₗ #1) <- Fst "end";;
    "end".
