From elpi Require Import elpi.
From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.bi Require Import fixpoint.
From iris.algebra Require Import ofe monoid list.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation.
From stdpp Require Import base finite.

Context `{!heapGS Σ}.
Notation iProp := (iProp Σ).
Implicit Types l : loc.


Definition is_list_pre_lgfp (is_list : val → iProp) : val → iProp := (λ hd,
  ⌜hd = NONEV⌝
  ∨ 
  ∃ l tl v, ⌜hd = SOMEV #l⌝ ∗ l ↦ (v,tl) ∗ is_list tl)%I.

Local Lemma is_list_pre_lgfp_mono (is_list1 is_list2 : val -d> iProp): 
  ⊢ (□ ∀ hd, is_list1 hd -∗ is_list2 hd) → 
    ∀ hd, is_list_pre_lgfp is_list1 hd -∗ is_list_pre_lgfp is_list2 hd.
Proof.
  iIntros "#H"; iIntros (hd) "HF1".
  rewrite /is_list_pre_lgfp.
  iDestruct "HF1" as "[HF1|HF1]".
  - eauto.
  - iDestruct "HF1" as "[%l [%tl [%v (Hhd & HP & HL2)]]]".
    iRight.
    iExists l, tl, v.
    iFrame.
    by iApply "H".
Qed.

(* Definition is_list_pre_lgfp' : 
  (val -d> iProp) →
  val -d> iProp :=
    uncurry ∘ is_list_pre_lgfp ∘ curry.

Local Instance is_list_pre_lgfp_mono' : BiMonoPred is_list_pre_lgfp'.
Proof.
  constructor.
  - iIntros (is_list1 is_list2 ??) "#H".
    iIntros ([hd vs]); iRevert (hd vs).
    iApply is_list_pre_lgfp_mono.
    iIntros "!>" (hd vs).
    iApply "H".
  - intros is_list Hne n [hd vs] [hd' vs'] [Hhd Hvs]; simplify_eq /=.
    rewrite /curry /is_list_pre_lgfp.
    revert Hvs; revert vs'.
    induction vs as [|v vs IH]; intros vs' Hvs; setoid_rewrite list_dist_Forall2 in Hvs. 
    + apply Forall2_nil_inv_l in Hvs. 
      simplify_eq. 
      setoid_rewrite Hhd.
      f_equiv.
    + inversion Hvs; simplify_eq /=.
      setoid_rewrite H1.
      setoid_rewrite Hhd.
      repeat f_equiv.
      by apply list_dist_Forall2.
Qed. *)

Definition is_list_lfp_def := λ hd, bi_least_fixpoint is_list_pre_lgfp' (hd, vs).
Definition is_list_gfp_def := λ hd, bi_greatest_fixpoint is_list_pre_lgfp' (hd, vs).

Lemma is_list_lfp_unfold hd vs :
  is_list_lfp_def hd vs ⊣⊢ is_list_pre_lgfp is_list_lfp_def hd vs.
Proof. by rewrite /is_list_lfp_def least_fixpoint_unfold. Qed.

Lemma is_list_gfp_unfold hd vs :
  is_list_gfp_def hd vs ⊣⊢ is_list_pre_lgfp is_list_gfp_def hd vs.
Proof. by rewrite /is_list_gfp_def greatest_fixpoint_unfold. Qed.
