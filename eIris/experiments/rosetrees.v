Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Sets.Classical_sets.

From stdpp Require Import gmap numbers countable mapset.

From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode notation.

From eIris.proofmode Require Import inductive tactics inductionTac.

Section Tests.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l tl : loc.

  Iris Inductive is_R_list {A} (R : val → A → iProp) : loc → list A → iProp :=
    | empty_is_R_list l : l ↦ NONEV -∗ is_R_list R l []
    | cons_is_R_list l v tl x xs : 
        l ↦ (v,#tl) -∗ R v x -∗ is_R_list R tl xs -∗ 
        is_R_list R l (x :: xs).

  Arguments is_R_list {A} (R)%_I _ _.

  Global Instance is_R_list_iProper {A} : 
    IProper (□> .> .> bi_wand ==> .> .> bi_wand) (@is_R_list A).
    unfold IProper, iPointwise_relation, iRespectful.
    iIntros (Φ Φ') "HΦ %l %vs Hil".
    iRevert "HΦ".
    iInduction "Hil" as "[Hl %Hvs | * Hl HR IH %Hvs]"; iIntros "#HΦ"; simplify_eq.
    {iApply empty_is_R_list. by iFrame. }
    iApply cons_is_R_list.
    iExists _, _, _, _.
    iFrame.
    iSplitL "HR".
    {by iApply "HΦ". }
    iSplit; try done.
    iDestruct "IH" as "[IH _]".
    by iApply "IH".
  Qed.

  Global Instance exists_IProperTop {A} : IProperTop (bi_wand) (@is_R_list A) (fun F => □> .> .> bi_wand ==> .> .> F)%i_signature.
    unfold IProperTop.
    tc_solve.
  Qed.

  Inductive tree := Node : list tree -> tree.

  Iris Inductive is_tree : loc -> tree -> iProp :=
    | node_is_tree l ts :
        is_R_list (λ v t, ∃ l', ⌜v = #l'⌝ ∗ is_tree l' t) l ts -∗
        is_tree l (Node ts).