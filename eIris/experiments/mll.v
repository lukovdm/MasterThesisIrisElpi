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

Section SkipQueue.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  Iris Inductive is_MLL : val → list val -> iProp :=
      | empty_is_MLL : is_MLL NONEV []
      | mark_is_MLL v vs l tl : l ↦ (v, #true, tl) -∗ is_MLL tl vs -∗ is_MLL (SOMEV #l) vs
      | cons_is_MLL v vs tl l : l ↦ (v, #false, tl) -∗ is_MLL tl vs -∗ is_MLL (SOMEV #l) (v :: vs).


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
  
  Print Grammar.


  Lemma MLL_insert_spec (vs : list val) (v : val) (i : nat) (hd : val) :
    [[{ is_MLL hd vs }]]
      MLL_insert hd #i v
    [[{ hd', RET hd'; is_MLL hd' (take i vs ++ v :: drop i vs) }]].
  Proof.
    eiIntros "%Phi His".
    iRevert (Phi i).
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