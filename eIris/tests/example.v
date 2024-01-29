Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Constructive_sets.
Require Import Coq.Sets.Classical_sets.

From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode notation.

From eIris.proofmode Require Import base reduction inductive intros.

(* Section SkipQueue.
    Context `{!heapGS Σ}.
    Notation iProp := (iProp Σ).
    Implicit Types l : loc.

    EI.ind
    Inductive is_skipqueue : val → list val → iProp :=
        | empty_is_skipqueue : is_skipqueue NONEV []
        | link_is_skipqueue vs l tl : l ↦ (NONEV, tl) -∗ is_skipqueue tl vs -∗ is_skipqueue (SOMEV #l) vs
        | cons_is_skipqueue v vs tl l : l ↦ (SOMEV v, tl) -∗ is_skipqueue tl vs -∗ is_skipqueue (SOMEV #l) (v :: vs).

End SkipQueue. *)

Section Sets.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  Print loc.

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
    eiInduction "His" as "[%Hhd %Hset | (%l & %tl & %s' & %e' & %ss & Hpt & %Hsub & IH & %Hl & %Hs)]"; eiIntros "%Phi Hlater".
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
        split.
        * intros x Hi.
          apply Singleton_intro.
          apply Constructive_sets.Add_inv in Hi as [H|H]; try done.
        * intros x Hi.
          apply Singleton_inv in Hi.
          simplify_eq.
          apply Add_intro2.
    - wp_rec.
      simplify_eq.
      wp_load.
      wp_pures.
      unfold bool_decide, decide_rel.
      destruct (val_eq_dec #e #e'); wp_pures.
      + eiDestruct "IH" as "[_ His]".
        iModIntro. iApply "Hlater".
        iApply cons_is_set.
        iExists l, tl, (Ensembles.Add nat s' e), e, (Ensembles.Subtract nat s' e). 
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
        iExists l, _, (Ensembles.Add nat s' e), _, _.
        iFrame.
        repeat iSplit; try iPureIntro; try done.
        apply Add_Subtract_comm.
        destruct (Nat.eq_dec e e'); try done.
        simplify_eq.
  Qed.
End Sets.
           
