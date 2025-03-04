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

  (* Elpi Trace Browser. *)
  EI.ind
  Inductive is_MLL : val → list val → iProp :=
      (* | test_is_MLL v vs : is_MLL v vs *)
      | empty_is_MLL : is_MLL NONEV []
      | mark_is_MLL v vs l tl : l ↦ (v, #true, tl) -∗ is_MLL tl vs -∗ is_MLL (SOMEV #l) vs
      | cons_is_MLL v vs tl l : l ↦ (v, #false, tl) -∗ is_MLL tl vs -∗ is_MLL (SOMEV #l) (v :: vs).

  Print is_MLL_pre.
  Check mark_is_MLL.
  Print is_MLL.

  Definition MLL_insert : val :=
    rec: "MLL_insert" "l" "i" "v" :=
      match: "l" with
          NONE => SOME (Alloc("v", #false, NONE))
        | SOME "hd" =>
            let: "x" := !"hd" in
            if: ("i" = #0) then
              SOME (Alloc("v", #false, SOME "hd"))
            else if: Snd (Fst "x") = #false then
              let: "tl" := "MLL_insert" (Snd "x") ("i" - #1) "v" in
              "hd" <- (Fst (Fst "x"), Snd (Fst "x"), "tl");;
              "l"
            else
              let: "tl" := "MLL_insert" (Snd "x") "i" "v" in
              "hd" <- (Fst (Fst "x"), Snd (Fst "x"), "tl");;
              "l"
      end.
  
  Lemma MLL_insert_spec (vs : list val) (v : val) (i : nat) (hd : val) :
    [[{ is_MLL hd vs }]]
      MLL_insert hd #i v
    [[{ hd', RET hd'; is_MLL hd' (take i vs ++ v :: drop i vs) }]].
  Proof.
    eiIntros "%Phi His".
    iRevert (Phi i).
    (* eiInduction "His". *)
    eiInduction "His" as "[%Ha %Ha0|* Hl IH %Ha| * Hl IH %Ha %Ha']"; eiIntros "%Phi %i Hphi"; simplify_eq.
    - wp_rec.
      wp_alloc l as "Hl".
      wp_pures.
      iModIntro.
      iApply "Hphi".
      iApply cons_is_MLL.
      iFrame.
      iExists _.
      repeat iSplit; try done.
      1: by iApply empty_is_MLL.
      by rewrite take_nil drop_nil.
    - wp_rec.
      wp_load.
      wp_pures.
      case_bool_decide; simplify_eq.
      + assert (i = 0) as -> by lia.
        wp_alloc k as "Hk".
        wp_pures.
        iModIntro.
        iApply "Hphi".
        iApply cons_is_MLL.
        iFrame; iExists _; repeat iSplit; try done.
        rewrite drop_0.
        eiDestruct "IH" as "[_ IH]".
        iApply mark_is_MLL.
        by iFrame.
      + wp_pures.
        eiDestruct "IH" as "[IH _]".
        wp_apply "IH".
        eiIntros "%hd' His".
        wp_store.
        iModIntro.
        iApply "Hphi".
        iApply mark_is_MLL.
        by iFrame.
    - wp_rec.
      wp_load.
      wp_pures.
      case_bool_decide; simplify_eq.
      + assert (i = 0) as -> by lia.
        wp_alloc k as "Hk".
        wp_pures.
        iModIntro.
        iApply "Hphi".
        iApply cons_is_MLL.
        iFrame; iExists _; repeat iSplit; try done.
        rewrite drop_0.
        eiDestruct "IH" as "[_ IH]".
        iApply cons_is_MLL.
        by iFrame.
      + wp_pures.
        eiDestruct "IH" as "[IH _]".
        destruct i as [|i]; first done.
        replace (S i - 1)%Z with (Z.of_nat i) by lia.
        wp_apply "IH".
        eiIntros "%hd' His".
        wp_store.
        iModIntro.
        iApply "Hphi".
        iApply cons_is_MLL.
        iFrame.
        iSplit; done.
  Qed.

  Definition MLL_delete : val :=
    rec: "MLL_delete" "l" "i" :=
      match: "l" with
        NONE => #()
        | SOME "hd" =>
          let: "x" := !"hd" in
          if: (Snd (Fst "x") = #false) && ("i" = #0) then
            "hd" <- (Fst (Fst "x"), #true, Snd "x")
          else if: Snd (Fst "x") = #false then
            "MLL_delete" (Snd "x") ("i" - #1)
          else
            "MLL_delete" (Snd "x") "i"
      end.

  Lemma MLL_delete_spec (vs : list val) (i : nat) (hd : val) :
    [[{ is_MLL hd vs }]]
      MLL_delete hd #i
    [[{ RET #(); is_MLL hd (delete i vs) }]].
  Proof.
    eiIntros "%Phi His".
    iRevert (Phi i).
    eiInduction "His" as "[%Ha %Ha0|* Hl IH %Ha| * Hl IH %Ha %Ha']"; eiIntros "%Phi %i Hphi"; simplify_eq.
    - wp_rec.
      wp_pures.
      iModIntro.
      iApply "Hphi".
      by iApply empty_is_MLL.
    - wp_rec.
      wp_load.
      wp_pures.
      iDestruct "IH" as "[IH _]".
      wp_apply "IH" as "?".
      iApply "Hphi".
      iApply mark_is_MLL.
      iExists _, _, _.
      by iFrame.
    - wp_rec.
      wp_load.
      wp_pures.
      case_bool_decide; simplify_eq.
      + assert (i = 0) as -> by lia.
        wp_pures.
        wp_store.
        iModIntro.
        iApply "Hphi".
        iApply mark_is_MLL.
        iExists _, _, _.
        iFrame.
        iDestruct "IH" as "[_ IH]".
        by iFrame.
      + wp_pures.
        iDestruct "IH" as "[IH _]".
        destruct i as [|i]; first done.
        replace (S i - 1)%Z with (Z.of_nat i) by lia.
        wp_apply "IH" as "?".
        iApply "Hphi".
        iApply cons_is_MLL.
        iExists _, _, _.
        by iFrame.
  Qed.

  Definition MLL_lookup : val :=
    rec: "MLL_lookup" "l" "i" :=
      match: "l" with
        NONE => NONEV
        | SOME "hd" =>
          let: "x" := !"hd" in
          if: (Snd (Fst "x") = #false) && ("i" = #0) then
            SOME (Fst (Fst "x"))
          else if: Snd (Fst "x") = #false then
            "MLL_lookup" (Snd "x") ("i" - #1)
          else
            "MLL_lookup" (Snd "x") "i"
      end.

  Lemma MLL_lookup_spec (vs : list val) (i : nat) (hd : val) (x: val) :
    vs !! i = Some x ->
    [[{ is_MLL hd vs }]]
      MLL_lookup hd #i
    [[{ v, RET v; is_MLL hd vs ∗ (⌜v = SOMEV x⌝) }]].
  Proof.
    eiIntros "%Hlookup %Phi His".
    iRevert (Phi i Hlookup).
    eiInduction "His" as "[%Ha %Ha0|* Hl IH %Ha| * Hl IH %Ha %Ha']"; eiIntros "%Phi %i %Hlookup Hphi"; simplify_eq.
    - wp_rec.
      wp_load.
      wp_pures.
      iDestruct "IH" as "[IH _]".
      iApply "IH"; first done.
      iIntros (v') "[IHis IH]".
      iApply "Hphi".
      iSplitL "Hl IHis"; try done.
      iApply mark_is_MLL.
      iExists _, _, _.
      by iFrame.
    - wp_rec.
      wp_load.
      wp_pures.
      case_bool_decide; simplify_eq. 
      + assert (i = 0) as -> by lia.
        wp_pures.
        iModIntro.
        iApply "Hphi".
        iDestruct "IH" as "[_ IH]".
        iSplitL.
        * iApply cons_is_MLL.
          iExists _, _, _, _.
          by iFrame.
        * iPureIntro.
          f_equal.
          by inversion Hlookup.
      + wp_pures.
        iDestruct "IH" as "[IH _]".
        destruct i as [|i]; first done.
        replace (S i - 1)%Z with (Z.of_nat i) by lia.
        iApply "IH"; first by simpl in Hlookup.
        iIntros (v') "[IHis IH]".
        iApply "Hphi".
        iSplitL "Hl IHis"; try done.
        iApply cons_is_MLL.
        iExists _,_,_,_.
        by iFrame.
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
    eiInduction "His" as "[%Hhd %Hset | * Hpt %Helem %Hsub IH %Hl]"; eiIntros "%Phi Hphi".
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
    eiInduction "His" as "[%Hhd %Hset | * Hpt %Hsub IH %Hl]"; eiIntros "%Phi Hphi".
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

