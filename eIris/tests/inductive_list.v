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

Fixpoint is_list_fix (hd : val) (vs : list val) : iProp :=
  match vs with
  | [] => ⌜ hd = NONEV ⌝
  | v :: vs => ∃ l tl, ⌜hd = SOMEV #l⌝ ∗ l ↦ (v,tl) ∗ is_list_fix tl vs
  end.

Definition is_list_pre (is_list : val -d> list val -d> iProp) : val -d> list val -d> iProp := λ hd vs,
  match vs with
  | [] => ⌜hd = NONEV⌝
  | v :: vs => ∃ l tl, ⌜hd = SOMEV #l⌝ ∗ l ↦□ (v,tl) ∗ ▷ is_list tl vs
  end%I.

Local Instance is_list_pre_contractive : Contractive (is_list_pre).
Proof.
  solve_contractive.
Qed.

Definition is_list_def := fixpoint is_list_pre.

Lemma is_list_def_unfold hd vs :
    is_list_def hd vs ⊣⊢ is_list_pre is_list_def hd vs.
Proof. apply (fixpoint_unfold is_list_pre). Qed.


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
Qed.

Definition is_list_lfp_def := λ hd vs, bi_least_fixpoint is_list_pre_lgfp' (hd, vs).
Definition is_list_gfp_def := λ hd vs, bi_greatest_fixpoint is_list_pre_lgfp' (hd, vs).

Lemma is_list_lfp_unfold hd vs :
  is_list_lfp_def hd vs ⊣⊢ is_list_pre_lgfp is_list_lfp_def hd vs.
Proof. by rewrite /is_list_lfp_def least_fixpoint_unfold. Qed.

Lemma is_list_gfp_unfold hd vs :
  is_list_gfp_def hd vs ⊣⊢ is_list_pre_lgfp is_list_gfp_def hd vs.
Proof. by rewrite /is_list_gfp_def greatest_fixpoint_unfold. Qed.

Section Proofs.
  Definition app : val :=
    rec: "app" "l" "l'" :=
      match: "l" with
        NONE => "l'"
      | SOME "hd" =>
        let: "tmp1" := !"hd" in
        let: "tmp2" := "app" (Snd "tmp1") "l'" in
        "hd" <- ((Fst "tmp1"), "tmp2");;
            "l"
      end.

  Definition cons : val := (λ: "x" "xs",
    let: "p" := ("x", "xs") in
    SOME (Alloc("p"))).

  Definition empty_list : val := NONEV.

  Lemma app_spec_fix xs ys (l l' : val) :
  {{{ is_list_fix l xs ∗ is_list_fix l' ys }}}
    app l l'
  {{{ v, RET v; is_list_fix v (xs ++ ys) }}}.
  Proof.
    iIntros (ϕ) "[Hxs Hys] H".
    iLöb as "IH" forall (l xs l' ys ϕ).
    destruct xs as [| x xs']; iSimplifyEq.
    - wp_rec. wp_let. wp_match. iApply "H". done.
    - iDestruct "Hxs" as (l0 hd0) "(% & Hx & Hxs)". iSimplifyEq.
      wp_rec. wp_let. wp_match. wp_load. wp_let. wp_proj. wp_bind (app _ _)%E.
      iApply ("IH" with "Hxs Hys").
      iNext. iIntros (v) "?". wp_let. wp_proj. wp_store. iSimplifyEq. iApply "H".
      iExists l0, _. iFrame. done.
  Qed.

  Lemma app_spec_banach xs ys (l l' : val) :
  {{{ is_list_def l xs ∗ is_list_def l' ys }}}
    app l l'
  {{{ v, RET v; is_list_def v (xs ++ ys) }}}.
  Proof.
    iIntros (ϕ) "[Hxs Hys] H".
    iLöb as "IH" forall (l xs l' ys ϕ).
    destruct xs as [| x xs']; rewrite is_list_def_unfold; iSimplifyEq.
    - wp_rec. wp_let. wp_match. iApply "H". done.
    - iDestruct "Hxs" as (l0 hd0) "(% & Hx & Hxs)". iSimplifyEq.
      wp_rec. wp_let. wp_match. wp_load. wp_let. wp_proj. wp_bind (app _ _)%E.
      iApply ("IH" with "Hxs Hys").
      iNext. iIntros (v) "?". wp_let. wp_proj. wp_store. iSimplifyEq. iApply "H".
      iApply is_list_def_unfold. simpl.
      iExists l0, _. iFrame. done.
  Qed.

  Lemma app_spec_lfp xs ys (l l' : val) :
  {{{ is_list_lfp_def l xs ∗ is_list_lfp_def l' ys }}}
    app l l'
  {{{ v, RET v; is_list_lfp_def v (xs ++ ys) }}}.
  Proof.
    iIntros (ϕ) "[Hxs Hys] H".
    iLöb as "IH" forall (l xs l' ys ϕ).
    destruct xs as [| x xs']; rewrite is_list_lfp_unfold; iSimplifyEq.
    - wp_rec. wp_let. wp_match. iApply "H". done.
    - iDestruct "Hxs" as (l0 hd0) "(% & Hx & Hxs)". iSimplifyEq.
      wp_rec. wp_let. wp_match. wp_load. wp_let. wp_proj. wp_bind (app _ _)%E.
      iApply ("IH" with "Hxs Hys").
      iNext. iIntros (v) "?". wp_let. wp_proj. wp_store. iSimplifyEq. iApply "H".
      iApply is_list_lfp_unfold. simpl.
      iExists l0, _. iFrame. done.
  Qed.

  Lemma app_spec_gfp xs ys (l l' : val) :
  {{{ is_list_gfp_def l xs ∗ is_list_gfp_def l' ys }}}
    app l l'
  {{{ v, RET v; is_list_gfp_def v (xs ++ ys) }}}.
  Proof.
    iIntros (ϕ) "[Hxs Hys] H".
    iLöb as "IH" forall (l xs l' ys ϕ).
    destruct xs as [| x xs']; rewrite is_list_gfp_unfold; iSimplifyEq.
    - wp_rec. wp_let. wp_match. iApply "H". done.
    - iDestruct "Hxs" as (l0 hd0) "(% & Hx & Hxs)". iSimplifyEq.
      wp_rec. wp_let. wp_match. wp_load. wp_let. wp_proj. wp_bind (app _ _)%E.
      iApply ("IH" with "Hxs Hys").
      iNext. iIntros (v) "?". wp_let. wp_proj. wp_store. iSimplifyEq. iApply "H".
      iApply is_list_gfp_unfold. simpl.
      iExists l0, _. iFrame. done.
  Qed.

End Proofs.

Section Equivalence.
  

  Lemma def_lfp_equiv hd xs :
    is_list_def hd xs ⊣⊢ is_list_lfp_def hd xs.
  Proof.
    iSplit.
    - rewrite is_list_lfp_unfold is_list_def_unfold.
      iRevert (hd).
      iInduction xs as [|x xs] "IH"; iIntros (hd) "H"; try done.
      simpl.
      iDestruct "H" as "[%l [%tl (HP & Hl & Hil)]]".
      iExists l, tl.
      iFrame.
      iApply is_list_lfp_unfold.
      iApply "IH".
      (* How to fix the later, maybe with an iLob earlier? *)
      admit.
    - iIntros "H".
      iInduction xs as [|x xs] "IH" forall (hd) "H".
      { by rewrite is_list_lfp_unfold is_list_def_unfold. }
      iEval (rewrite is_list_def_unfold).
      iEval (rewrite is_list_lfp_unfold) in "H".
      simpl.
      iDestruct "H" as "[%l [%tl (HP & Hl & Hil)]]".
      iExists l, tl.
      iFrame.
      iNext.
      by iApply "IH".
    
      Undo 12.

      iLöb as "IH" forall (hd xs) "H".
      iEval (rewrite is_list_def_unfold).
      iEval (rewrite is_list_lfp_unfold) in "H".
      destruct xs as [|x xs].
      { done. }
      simpl.
      iDestruct "H" as "[%l [%tl (HP & Hl & Hil)]]".
      iExists l, tl.
      iFrame.
      iNext.
      by iApply "IH".