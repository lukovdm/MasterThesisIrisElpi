From stdpp Require Import gmap numbers countable mapset.

From iris.program_logic Require Export atomic.
From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode notation.

From eIris.proofmode Require Import base reduction inductive tactics inductionTac.

Section DelList.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l nl tl lh lt : loc.

  Local Definition NIL : val := NONEV.
  Local Definition CONS (v:val) : val := SOMEV (#0, v).
  Local Definition DEL (l:val) : val := SOMEV (#1, l).

  Iris Inductive is_del_list : loc → list val → iProp :=
    | is_del_list_nil l : l ↦ NIL -∗ is_del_list l []
    | is_del_list_cons l' v vs l :
      l ↦ CONS (#l',v) -∗ is_del_list l' vs -∗ is_del_list l (v :: vs)
    | is_del_list_del l' vs l : l ↦ DEL #l' -∗ is_del_list l' vs -∗ is_del_list l vs.

End DelList.

Section DelWithTail.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l nl tl lh lt : loc.

  Iris Inductive is_list_with_tl (tl : loc) : loc → list val → iProp :=
    | is_list_with_tl_nil : tl ↦ NIL -∗ is_list_with_tl tl tl []
    | is_list_with_tl_cons v vs l l' :
      l ↦ CONS (v,#l') -∗ is_list_with_tl tl l' vs -∗ is_list_with_tl tl l (v :: vs)
    | is_list_with_tl_del vs l l' :
      l ↦ DEL #l' -∗ is_list_with_tl tl l' vs -∗ is_list_with_tl tl l vs.

  Check is_list_with_tl_pre_mono.


  Definition new_list : val := λ: <>,
    let: "end" := Alloc NONE in
    ("end", "end").

  Definition enqueue : val := λ: "t" "x",
    let: "end" := Alloc NONE  in
    let: "v" := ("x", "end") in
    "t" <- SOME "v";;
    "end".

  Definition dequeue : val :=
    rec: "dequeue" "d" :=
      match: !"d" with
          NONE => "dequeue" "d"
        | SOME "v" =>
            if: Fst "v" = #0 then
              (Snd (Snd "v"), Fst (Snd "v"))
            else
              "dequeue" (Snd (Snd "v"))
      end.

  Definition link_queue : val := λ: "t" "h",
    let: "node" := !"t" in
    let: "lh" := !"h" in
    "node" <- SOME (#1, "lh");;
    #().

  Lemma new_queue_spec:
    {{{ True }}}
      new_list #()
    {{{ lh lt, RET (#lh, #lt);
      is_list_with_tl lh lt [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc l as "Hl /=".
    wp_pures. iModIntro. iApply "HΦ".
    iApply is_list_with_tl_nil. by iFrame.
  Qed.

  Definition lookup : val :=
    rec: "lookup" "l" "i" :=
      match: !"l" with
          NONE => NONEV
        | SOME "v" =>
          if: (Fst "v") = #0 then
            if: "i" = #0 then
              SOME (Fst (Snd "v"))
            else
              "lookup" (Snd (Snd "v")) ("i" - #1)
          else
            "lookup" (Snd "v") "i"
      end.

  Lemma lookup_spec (vs : list val) (i : nat) (tl : loc) (hd : loc) (x: val) :
    vs !! i = Some x ->
    [[{ is_list_with_tl tl hd vs }]]
      lookup #hd #i
    [[{ v, RET v; is_list_with_tl tl hd vs ∗ (⌜v = SOMEV x⌝) }]].
  Proof.
    eiIntros "%Hlookup %Phi His".
    iRevert (Phi i Hlookup).
    iInduction "His" as "[Htl %Hvs %Hltl | %v %vs' %l' Hl IH %Hvs | %l' Hl IH]"; eiIntros "%Phi %i %Hlookup Hphi"; simplify_eq.
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
        * iApply is_list_with_tl_cons.
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
        iApply is_list_with_tl_cons.
        by iFrame.
    - wp_rec.
      wp_load.
      wp_pures.
      iDestruct "IH" as "[IH _]".
      iApply "IH"; first done.
      iIntros (v') "[IHis IH]".
      iApply "Hphi".
      iSplitL "Hl IHis"; try done.
      iApply is_list_with_tl_del.
      iExists _.
      by iFrame.
  Qed.
End DelWithTail.