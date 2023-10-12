From elpi Require Import elpi.
From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.bi Require Import fixpoint.
From iris.algebra Require Import list.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation.
From stdpp Require Import base.

Context `{!heapGS Σ}.
Notation iProp := (iProp Σ).
Implicit Types l : loc.

Fixpoint is_list_fix (hd : val) (vs : list val) : iProp :=
  match vs with
  | [] => ⌜ hd = NONEV ⌝
  | v :: vs => ∃ l tl, ⌜hd = SOMEV #l⌝ ∗ l ↦ (v,tl) ∗ is_list_fix tl vs
  end.

Definition is_list_pre (is_list : val -d> list val -d> iProp) : val -d> list val -d> iProp := λ hd vs,
  match vs with
  | [] => bi_pure (hd = NONEV)
  | v :: vs => ∃ l tl, ⌜hd = SOMEV #l⌝ ∗ l ↦ (v,tl) ∗ ▷ is_list tl vs
  end%I.

Local Instance is_list_pre_contractive : Contractive (is_list_pre).
Proof.
  solve_contractive.
Qed.

Definition is_list_def := fixpoint is_list_pre.

Definition is_list_pre_lgfp (is_list : val → list val → iProp) : val → list val → iProp := λ hd vs,
  match vs with
  | [] => bi_pure (hd = NONEV)
  | v :: vs => ∃ l tl, ⌜hd = SOMEV #l⌝ ∗ l ↦ (v,tl) ∗ is_list tl vs
  end%I.

Local Lemma is_list_pre_lgfp_mono (is_list1 is_list2 : val -d> list val -d> iProp): 
  ⊢ (□ ∀ hd vs, is_list1 hd vs -∗ is_list2 hd vs) → 
    ∀ hd vs, is_list_pre_lgfp is_list1 hd vs -∗ is_list_pre_lgfp is_list2 hd vs.
Proof.
  iIntros "#H"; iIntros (hd vs) "HF1".
  destruct vs as [|v' vs'].
  - done.
  - rewrite /is_list_pre_lgfp.
    iDestruct "HF1" as "[%l [%tl (Hhd & HP & HL2)]]".
    iExists l.
    iExists tl.
    iFrame.
    by iApply "H".
Qed.

Definition is_list_pre_lgfp' : 
  (prodO val (listO val) -d> iProp) →
  prodO val (listO val) -d> iProp :=
    uncurry ∘ is_list_pre_lgfp ∘ curry.

Local Instance is_list_pre_lgfp_mono' : BiMonoPred is_list_pre_lgfp'.
Proof.
  constructor.
  - iIntros (is_list1 is_list2 ??) "#H".
    iIntros ([hd vs]); iRevert (hd vs).
    iApply is_list_pre_lgfp_mono.
    iIntros "!>" (hd vs).
    iApply "H".
  - intros is_list Hne n [hd vs] [hd' vs'] [? ?]; simplify_eq /=.
    rewrite /curry /is_list_pre_lgfp.
    f_equiv.
    destruct vs.
    + 

Definition is_list_lfp_def := bi_least_fixpoint 


