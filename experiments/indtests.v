Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Sets.Classical_sets.

From stdpp Require Import gmap numbers countable mapset.

From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode notation.

From eIris.proofmode Require Import base reduction inductive intros.

Section Tests.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  EI.ind
  Inductive is_R_MLL {A} (R : val -> A -> iProp) : val → list A → iProp :=
      | empty_is_R_MLL : is_R_MLL R NONEV []
      | mark_is_R_MLL v xs l tl : l ↦ (v, #true, tl) -∗ is_R_MLL R tl xs -∗ is_R_MLL R (SOMEV #l) xs
      | cons_is_R_MLL v x xs tl l : l ↦ (v, #false, tl) -∗ R v x -∗ is_R_MLL R tl xs -∗ is_R_MLL R (SOMEV #l) (x :: xs).
    
  Print is_R_MLL_pre.
  Check is_MLL_ind.

  EI.ind
  Inductive is_R_list {A} (R : val → A → iProp) : 
                      val → list A → iProp :=
    | empty_is_R_list : is_R_list R NONEV []
    | cons_is_R_list l v tl x xs : 
        l ↦ (v,tl) -∗ R v x -∗ is_R_list R tl xs -∗ 
        is_R_list R (SOMEV #l) (x :: xs).

  EI.ind 
  Inductive is_list (q : Qp) : val → list val → iProp :=
    | empty_is_list : is_list q NONEV []
    | cons_is_list l v vs tl : l ↦{#q} (v,tl) -∗ is_list q tl vs -∗ is_list q (SOMEV #l) (v :: vs).

  Print is_list_pre.
  Check is_list_pre_mono.
  Print is_list.
  Check is_list_unfold_2.
  Check is_list_unfold_1.
  Check is_list_unfold.
  Check empty_is_list.
  Check cons_is_list.
  Check is_list_iter.
  Check is_list_ind.

  (* islist q ∗ islist q' ∗-∗ islist (q+q') *)
  (* islist q -> [] ∨ q <= 1 *)
  (* islist (DfracOwn q) -> |==> islist (DfracDiscarded) *)
  (* Pers islist DfracDiscarded *)

  EI.ind 
  Inductive is_l : val -> list val → iProp :=
    | empty_is_l : is_l NONEV []
    | cons_is_l l v vs tl : l ↦ (v,tl) -∗ is_l tl vs -∗ is_l (SOMEV #l) (v :: vs).

  Print is_l_pre.
  Check is_l_pre_mono.
  Print is_l.
  Check is_l_unfold_2.
  Check is_l_unfold_1.

  EI.ind 
  Inductive is_P_list : (val → iProp) → val → iProp :=
    | empty_is_P_list P : is_P_list P NONEV
    | cons_is_P_list P l v tl : l ↦ (v,tl) -∗ P v -∗ is_P_list P tl -∗ is_P_list P (SOMEV #l).

  Print is_P_list_pre.
  Check is_P_list_pre_mono.
  Print is_P_list.
  Check is_P_list_unfold_2.
  Check is_P_list_unfold_1.

  EI.ind 
  Inductive is_P2_list {A} (P : val → A → iProp) : val → list A → iProp :=
    | empty_is_P2_list : is_P2_list P NONEV []
    | cons_is_P2_list l v tl x xs : l ↦ (v,tl) -∗ P v x -∗ is_P2_list P tl xs -∗ is_P2_list P (SOMEV #l) (x :: xs).
 
  Print is_P2_list_pre.
  Check is_P2_list_pre_mono.
  Print is_P2_list.
  Check is_P2_list_unfold_2.
  Check is_P2_list_unfold_1.
  Check empty_is_P2_list.

End Tests.


Section Proof.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.
  (* Implicit Types v : val. *)

  EI.ind 
  Inductive is_list (q : Qp) : val → iProp :=
    | empty_is_list : is_list q NONEV
    | cons_is_list l v tl : l ↦{#q} (v,tl) -∗ is_list q tl -∗ is_list q (SOMEV #l).
      
  (* Check is_list_pre. *)

  Lemma ind_test_1 (q q' : Qp) (v : val) :
    is_list q v ∗ is_list q' v ∗-∗ is_list (q+q') v.
  Proof.
    iSplit.
    - eiIntros "[Hq Hq']".
      iRevert "Hq'".
      eiInduction "Hq" as "[%Ha | * Hl' IH %Ha]"; iIntros "Hq'".
      + by iApply empty_is_list.
      + simplify_eq.
        iApply cons_is_list.
        eiDestruct "Hq'" as "[%Hl | * Hl Hilq' %Hv]"; simplify_eq.
        iCombine "Hl' Hl" as "Hl" gives %[_ ?]; simplify_eq.
        iExists _, _, _.
        iFrame.
        iDestruct "IH" as "[IH _]".
        iSplitL.
        * iApply ("IH" with "[$]").
        * by iPureIntro.
    - eiIntros "Hi".
      eiInduction "Hi" as "[%Ha | * [Hq Hq'] [[Hiq Hiq'] _] %Hy]".
      + simplify_eq.
        iSplitL; by iApply empty_is_list.
      + iSplitL "Hq Hiq".
        * iApply cons_is_list.
          iExists _, _, _.
          by iFrame.
        * iApply cons_is_list.
          iExists _, _, _.
          by iFrame.
  Qed.

  (* Lemma ind_test_2 (q : Qp) (v : val) (vs : list val) :
    is_list q v vs -∗ ⌜vs = []⌝ ∨ ⌜(q ≤ 1)%Qp⌝.
  Proof.
    eiIntros "[Hv Hvs | (%l & %v' & %vs' & %tl & Hl & _ & _ & _)]".
    - iLeft.
      iFrame.
    - iRight.
      iEval (iApply pointsto_valid) in "Hl".
      iRevert "Hl".
      iPureIntro.
      intros Hq.
      by apply dfrac_valid in Hq.
  Qed. *)


  (* Elpi Trace Browser. *)
  Lemma intros_1 (Q : Prop) (P : nat -> iProp) :
    ∀ x:nat, ∀ y:nat, ∀ z:nat, □ P x -∗ P x.
  Proof.
    elpi eiIntros "% % % #H @H".
  Qed.

  (* Elpi Trace Browser. *)
  Lemma intros_2 (P : nat -> iProp) :
    □ (∃b, ((P b ∗ P 2) ∨ P 3)) -∗ (∃b, P b) -∗ ∃y, P y.
  Proof.
    elpi eiIntros "#[%b [[H1 H11] | H3]] [%c H2]".
    - by iExists b.
    - by iExists c.
  Qed.
End Proof.
