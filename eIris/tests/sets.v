Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Sets.Classical_sets.

From stdpp Require Import gmap numbers countable mapset.

From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode notation.

From eIris.proofmode Require Import base reduction inductive intros.

Section SkipQueue.
    Context `{!heapGS Σ}.
    Notation iProp := (iProp Σ).
    Implicit Types l : loc.

    EI.ind
    Inductive is_skipqueue : val → list val → iProp :=
        | empty_is_skipqueue : is_skipqueue NONEV []
        | link_is_skipqueue v vs l tl : l ↦ (v, #true, tl) -∗ is_skipqueue tl vs -∗ is_skipqueue (SOMEV #l) vs
        | cons_is_skipqueue v vs tl l : l ↦ (v, #false, tl) -∗ is_skipqueue tl vs -∗ is_skipqueue (SOMEV #l) (v :: vs).

    Definition skipqueue_push : val :=
      rec: "skipqueue_push" "l" "v" :=
        match: "l" with
          NONE => SOME (Alloc("v", #false, NONE))
          | SOME "hd" =>
            let: "x" := !"hd" in
            let: "tl" := "skipqueue_push" (Snd "x") "v" in
            "hd" <- (Fst (Fst "x"), Snd (Fst "x"), "tl");;
            "l"
        end.
    
    Lemma skipqueue_push_spec (vs : list val) (v : val) (hd : val) :
      {{{ is_skipqueue hd vs }}}
        skipqueue_push hd v
      {{{ hd', RET hd'; is_skipqueue hd' (vs ++ [v])}}}.
    Proof.
      eiIntros "%Phi His".
      iRevert (Phi).
      eiInduction "His" as "[%Ha %Ha0|* Hl IH %Ha %Ha'| * Hl IH %Ha %Ha']"; eiIntros "%Phi Hlater"; simplify_eq.
      - wp_rec.
        wp_alloc l as "Hl".
        wp_pures.
        iModIntro.
        iApply "Hlater".
        iApply cons_is_skipqueue.
        iExists _, _, _, l.
        iFrame.
        repeat iSplit; try iPureIntro; try done.
        by iApply empty_is_skipqueue.
      - wp_rec.
        wp_load.
        wp_pures.
        eiDestruct "IH" as "[IH _]".
        wp_apply "IH".
        eiIntros "%hd' His".
        wp_store.
        iModIntro.
        iApply "Hlater".
        iApply link_is_skipqueue.
        iExists _, _, l, _.
        iFrame.
        iSplit; done.
      - wp_rec.
        wp_load.
        wp_pures.
        eiDestruct "IH" as "[IH _]".
        wp_apply "IH".
        eiIntros "%hd' His".
        wp_store.
        iModIntro.
        iApply "Hlater".
        iApply cons_is_skipqueue.
        iExists _, _, _, _.
        iFrame.
        iSplit; done.
    Qed.

End SkipQueue.

Section GSets.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  EI.ind
  Inductive is_gset : val -> @gset nat _ nat_countable -> iProp :=
    | empty_is_gset : is_gset NONEV ∅
    | cons_is_gset l tl s (e : nat) ss : 
      l ↦ (#e, tl) -∗ 
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

  Lemma gset_add_spec (s : @gset nat _ nat_countable) (e : nat) (hd : val) :
    {{{ is_gset hd s }}}
      gset_add hd (#e)
    {{{ hd', RET hd'; is_gset hd' (s ∪ {[ e ]}) }}}.
  Proof.
    eiIntros "%Phi His".
    iRevert (Phi).
    eiInduction "His" as "[%Hhd %Hset | * Hpt %Hsub IH %Hl %Hs]"; eiIntros "%Phi Hlater".
    - wp_rec.
      simplify_eq.
      wp_alloc l as "Hl".
      wp_pures.
      iModIntro.
      iApply "Hlater".
      iApply cons_is_gset.
      iExists l, NONEV, {[ e ]}, e, ∅.
      iFrame.
      repeat iSplit; try iPureIntro; try done.
      + apply set_eq.
        intros x.
        split; intros H.
        * apply elem_of_difference in H as [He Hne].
          congruence.
        * by eapply not_elem_of_empty in H.
      + by iApply empty_is_gset.
      + apply left_id, _.
    - wp_rec.
      simplify_eq.
      wp_load.
      wp_pures.
      unfold bool_decide, decide_rel.
      destruct (val_eq_dec #e #a2); wp_pures.
      + eiDestruct "IH" as "[_ His]".
        iModIntro. iApply "Hlater".
        iApply cons_is_gset.
        iExists l, tl, (a1 ∪ {[ a2 ]}), a2, (a1 ∖ {[a2]}). 
        simplify_eq.
        iFrame.
        repeat iSplit; try iPureIntro; try done.
        rewrite difference_union_distr_l_L difference_diag_L.
        apply right_id, _.
      + eiDestruct "IH" as "[IH _]".
        wp_apply "IH".
        eiIntros "%hd' His".
        wp_store.
        iApply "Hlater".
        iModIntro.
        iApply cons_is_gset.
        iExists l, _, (a1 ∪ {[ e ]}), _, _.
        iFrame.
        repeat iSplit; try iPureIntro; try done.
        rewrite difference_union_distr_l_L.
        rewrite (difference_disjoint_L {[ e ]}); [done|].
        apply disjoint_singleton_r, not_elem_of_singleton.
        destruct (Nat.eq_dec e a2); try done.
        simplify_eq.
  Qed.
End GSets.


Section Sets.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  EI.ind
  Inductive is_set : val -> Ensemble nat -> iProp :=
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
    eiInduction "His" as "[%Hhd %Hset | * Hpt %Hsub IH %Hl %Hs]"; eiIntros "%Phi Hlater".
    - wp_rec.
      simplify_eq.
      wp_alloc l as "Hl".
      wp_pures.
      iModIntro.
      iApply "Hlater".
      iApply cons_is_set.
      iExists l, NONEV, (Ensembles.Singleton nat e), e, (Empty_set nat).
      iFrame.
      repeat iSplit; try iPureIntro; try done.
      + apply Extensionality_Ensembles.
        split; intros x Hincl.
        * apply Subtract_inv in Hincl as [Hincl Heq].
          by apply Singleton_inv in Hincl.
        * exfalso.
          by eapply Noone_in_empty.
      + by iApply empty_is_set.
      + apply Extensionality_Ensembles.
        split; intros x Hi.
        * apply Singleton_intro.
          apply Constructive_sets.Add_inv in Hi as [H|H]; try done.
        * apply Singleton_inv in Hi.
          simplify_eq.
          apply Add_intro2.
    - wp_rec.
      simplify_eq.
      wp_load.
      wp_pures.
      unfold bool_decide, decide_rel.
      destruct (val_eq_dec #e #a2); wp_pures.
      + eiDestruct "IH" as "[_ His]".
        iModIntro. iApply "Hlater".
        iApply cons_is_set.
        iExists _, _, (Ensembles.Add nat a1 e), _, (Ensembles.Subtract nat a1 e). 
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
        iApply "Hlater".
        iModIntro.
        iApply cons_is_set.
        iExists _, _, (Ensembles.Add nat a1 e), _, _.
        iFrame.
        repeat iSplit; try iPureIntro; try done.
        apply Add_Subtract_comm.
        destruct (Nat.eq_dec e a2); try done.
        simplify_eq.
  Qed.
End Sets.
           
