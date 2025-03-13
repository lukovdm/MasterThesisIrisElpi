From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode notation.

From eIris.proofmode Require Import base reduction inductive intros.

Section MLL.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  EI.ind
  Inductive is_MLL : val → list val → iProp :=
    | empty_is_MLL : is_MLL NONEV []
    | mark_is_MLL v vs l tl : l ↦ (v, #true, tl) -∗ is_MLL tl vs -∗ is_MLL (SOMEV #l) vs
    | cons_is_MLL v vs tl l : l ↦ (v, #false, tl) -∗ is_MLL tl vs -∗ is_MLL (SOMEV #l) (v :: vs).

  Print is_MLL.
  Print is_MLL_pre.
  Check is_MLL_ind.
    
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
    eiInduction "His" as "[%Ha %Ha0|* Hl IH %Ha %Ha'| * Hl IH %Ha %Ha']"; eiIntros "%Phi %i Hphi"; simplify_eq.
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
      iExists _, _, _, _.
      iFrame.
      iSplit; done.
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
        iExists _, _, _, _.
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
        iExists _, _, _, _.
        by iFrame.
  Qed.
  