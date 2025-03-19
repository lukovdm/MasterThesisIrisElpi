Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Sets.Classical_sets.

From stdpp Require Import gmap numbers countable mapset.

From iris.proofmode Require Import tactics coq_tactics reduction.
From iris.prelude Require Import options.


From eIris.proofmode Require Import base reduction inductive tactics inductionTac.
From eIris.experiments Require Import twp.

From iris.heap_lang Require Import proofmode notation.

Section BinarySearchTree.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l tl tr ll lr : loc.
  Implicit Types n : Z.
  Open Scope Z_scope.

  Local Definition LEAF : val := NONEV.
  Local Definition NODE (v : val) : val := SOMEV v.

  Iris Inductive is_search_tree : loc → gset Z → iProp :=
    | is_search_tree_empty l :
      l ↦ LEAF -∗ is_search_tree l ∅
    | is_search_tree_node l n ll lr Xl Xr :
      l ↦ NODE (#n, #ll, #lr) -∗ 
      is_search_tree ll Xl -∗ 
      is_search_tree lr Xr -∗
      ⌜set_Forall (λ n', n' < n) Xl⌝ -∗ 
      ⌜set_Forall (λ n', n < n') Xr⌝ -∗
      is_search_tree l ({[ n ]} ∪ Xl ∪ Xr).

End BinarySearchTree.

Section GSetsList.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  Iris Inductive is_gset : val -> @gset nat _ nat_countable -> iProp :=
    | empty_is_gset : is_gset NONEV ∅
    | cons_is_gset l tl s (e : nat) ss : 
      l ↦ (#e, tl) -∗ 
      ⌜e ∈ s⌝ -∗
      ⌜s ∖ {[ e ]} = ss⌝ -∗ 
      is_gset tl ss -∗ 
      is_gset (SOMEV #l) s.

  Definition gset_add : val :=
    rec: "gset_add" "l" "e" :=
      match: "l" with
        NONE => SOME (Alloc("e", NONE))
        | SOME "hd" =>
          let: "x" := !"hd" in
          if: "e" ≠ (Fst "x") then 
            let: "tl" := "gset_add" (Snd "x") "e" in
            "hd" <- (Fst "x", "tl");;
            "l"
          else
            "l"
      end.

  Lemma gset_add_spec (s : gset nat) (e : nat) (hd : val) :
    {{{ is_gset hd s }}}
      gset_add hd (#e)
    {{{ hd', RET hd'; is_gset hd' (s ∪ {[ e ]}) }}}.
  Proof.
    eiIntros "%Phi His".
    iRevert (Phi).
    iInduction "His" as "[%Hhd %Hset | * Hpt %Helem %Hsub IH %Hl]"; eiIntros "%Phi Hphi".
    - wp_rec.
      simplify_eq.
      wp_alloc l as "Hl".
      wp_pures.
      iModIntro.
      iApply "Hphi".
      iApply cons_is_gset.
      iExists l, NONEV, e, ∅.
      iFrame.
      repeat iSplit; try iPureIntro; try done.
      + rewrite union_empty_l.
        by apply elem_of_singleton_2.
      + apply set_eq.
        intros x.
        split; intros H.
        * apply elem_of_difference in H as [He Hne].
          rewrite union_empty_l in He.
          congruence.
        * by eapply not_elem_of_empty in H.
      + by iApply empty_is_gset.
    - wp_rec.
      simplify_eq.
      wp_load.
      wp_pures.
      unfold bool_decide, decide_rel.
      destruct (val_eq_dec #e #a1); wp_pures.
      + eiDestruct "IH" as "[_ His]".
        iModIntro. iApply "Hphi".
        iApply cons_is_gset.
        iExists l, tl, a1, (a0 ∖ {[a1]}). 
        simplify_eq.
        iFrame.
        repeat iSplit; try iPureIntro; try done.
        * by apply elem_of_union_r, elem_of_singleton_2.
        * rewrite difference_union_distr_l_L difference_diag_L.
          apply right_id, _.
      + eiDestruct "IH" as "[IH _]".
        wp_apply "IH".
        eiIntros "%hd' His".
        wp_store.
        iApply "Hphi".
        iModIntro.
        iApply cons_is_gset.
        iExists l, _, _, _.
        iFrame.
        repeat iSplit; try iPureIntro; try done.
        * by apply elem_of_union_l.
        * rewrite difference_union_distr_l_L.
          rewrite (difference_disjoint_L {[ e ]}); [done|].
          apply disjoint_singleton_r, not_elem_of_singleton.
          destruct (Nat.eq_dec e a1); try done.
          simplify_eq.
  Qed.
End GSetsList.


Section Sets.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  Iris Inductive is_set : val -> Ensemble nat -> iProp :=
    | empty_is_set : is_set NONEV (Empty_set nat)
    | cons_is_set l tl s (e : nat) ss : 
      l ↦ (#e, tl) -∗ 
      ⌜Ensembles.Subtract nat s e = ss⌝ -∗ 
      is_set tl ss -∗ 
      is_set (SOMEV #l) s.

  Definition set_add : val :=
    rec: "set_add" "l" "e" :=
      match: "l" with
        NONE => SOME (Alloc("e", NONE))
        | SOME "hd" =>
          let: "x" := !"hd" in
          if: "e" ≠ (Fst "x") then 
            let: "tl" := "set_add" (Snd "x") "e" in
            "hd" <- (Fst "x", "tl");;
            "l"
          else
            "l"
      end.

  Lemma Add_Subtract_comm s e e' :
    e ≠ e' ->
    Subtract nat (Ensembles.Add nat s e) e' = Ensembles.Add nat (Subtract nat s e') e.
  Proof.
    intros Hee'q.
    apply Extensionality_Ensembles; split; intros x H.
    - destruct (Nat.eq_dec x e); simplify_eq; [apply Add_intro2|].
      apply Add_intro1, Subtract_intro;
      apply Subtract_inv in H as [H Heq]; try done.
      apply Constructive_sets.Add_inv in H as [H | Hneq]; try done.
    - destruct (Nat.eq_dec x e); simplify_eq; apply Constructive_sets.Add_inv in H as [H | Hneq]; simplify_eq.
      + apply Subtract_inv in H as [H Hneq].
        apply Subtract_intro; try done.
        apply Add_intro2.
      + by apply Subtract_intro; try apply Add_intro2.
      + apply Subtract_inv in H as [H Hneq].
        apply Subtract_intro; try done.
        by apply Add_intro1.
  Qed.
  
  Lemma set_add_spec (s : Ensemble nat) (e : nat) (hd : val) :
    {{{ is_set hd s }}}
      set_add hd (#e)
    {{{ hd', RET hd'; is_set hd' (Ensembles.Add nat s e) }}}.
  Proof.
    eiIntros "%Phi His".
    iRevert (Phi).
    iInduction "His" as "[%Hhd %Hset | * Hpt %Hsub IH %Hl]"; eiIntros "%Phi Hphi".
    - wp_rec.
      simplify_eq.
      wp_alloc l as "Hl".
      wp_pures.
      iModIntro.
      iApply "Hphi".
      iApply cons_is_set.
      iExists l, NONEV, e, (Empty_set nat).
      iFrame.
      repeat iSplit; try iPureIntro; try done.
      + apply Extensionality_Ensembles.
        split; intros x Hincl.
        * apply Subtract_inv in Hincl as [Hincl Heq].
          inversion Hincl; try done.
          by inversion H.
        * exfalso.
          by eapply Noone_in_empty.
      + by iApply empty_is_set.
    - wp_rec.
      simplify_eq.
      wp_load.
      wp_pures.
      unfold bool_decide, decide_rel.
      destruct (val_eq_dec #e #a1); wp_pures.
      + eiDestruct "IH" as "[_ His]".
        iModIntro. iApply "Hphi".
        iApply cons_is_set.
        iExists _, _, _, (Ensembles.Subtract nat a0 e). 
        simplify_eq.
        iFrame.
        repeat iSplit; try iPureIntro; try done.
        apply Extensionality_Ensembles; split; intros x H.
        * apply Subtract_inv in H as [H Hneq].
          apply Subtract_intro; try done.
          apply Constructive_sets.Add_inv in H as [H | Heq]; try done.
        * apply Subtract_inv in H as [H Hneq].
          apply Subtract_intro; try done.
          by apply Add_intro1.
      + eiDestruct "IH" as "[IH _]".
        wp_apply "IH".
        eiIntros "%hd' His".
        wp_store.
        iApply "Hphi".
        iModIntro.
        iApply cons_is_set.
        iExists _, _, _, _.
        iFrame.
        repeat iSplit; try iPureIntro; try done.
        apply Add_Subtract_comm.
        destruct (Nat.eq_dec e a1); try done.
        simplify_eq.
  Qed.
End Sets.

