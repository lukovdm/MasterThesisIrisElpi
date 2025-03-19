Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Sets.Classical_sets.

From stdpp Require Import gmap numbers countable mapset.

From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode notation.

From eIris.proofmode Require Import inductive tactics inductionTac.

Section RoseTrees.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  Local Definition NIL : val := NONEV.
  Local Definition CONS (v:val) : val := SOMEV (#0, v).
  Local Definition DEL (l:loc) : val := SOMEV (#1, #l).

  Iris Inductive is_list {A} (Φ : val → A → iProp) : loc → list A → iProp :=
    | is_list_nil l : l ↦ NIL -∗ is_list Φ l []
    | is_list_cons v x xs l l' :
      l ↦ CONS (v,#l') -∗ Φ v x -∗ is_list Φ l' xs -∗ is_list Φ l (x :: xs)
    | is_list_del xs l l' :
      l ↦ DEL l' -∗ is_list Φ l' xs -∗ is_list Φ l xs.

  Arguments is_list {A} (Φ)%_I _ _.

  Global Instance is_list_iProper {A} : 
    IProper (□> .> .> bi_wand ==> .> .> bi_wand) (@is_list A).
    unfold IProper, iPointwise_relation, iRespectful.
    iIntros (Φ Φ') "HΦ %l %vs Hil".
    iRevert "HΦ".
    iInduction "Hil" as "[Hl %Hvs | * Hl HPhi IH %Hvs | * Hl IH]"; iIntros "#HΦ"; simplify_eq.
    {iApply is_list_nil. by iFrame. }
    - iApply is_list_cons.
      iExists _, _, _, _.
      iFrame.
      iSplitL "HPhi".
      {by iApply "HΦ". }
      iSplit; try done.
      iDestruct "IH" as "[IH _]".
      by iApply "IH".
    - iApply is_list_del.
      iExists _.
      iFrame.
      iDestruct "IH" as "[IH _]".
      by iApply "IH". 
  Qed.

  Global Instance exists_IProperTop {A} : IProperTop (bi_wand) (@is_list A) (fun F => □> .> .> bi_wand ==> .> .> F)%i_signature.
    unfold IProperTop.
    tc_solve.
  Qed.

  Inductive tree := Node : list tree -> tree.

  Iris Inductive is_tree : loc -> tree -> iProp :=
    | node_is_tree l ts :
        is_list (λ v t, ∃ l', ⌜v = #l'⌝ ∗ is_tree l' t) l ts -∗
        is_tree l (Node ts).
End RoseTrees.