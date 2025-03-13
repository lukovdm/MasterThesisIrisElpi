From stdpp Require Import gmap numbers countable mapset.

From iris.program_logic Require Export atomic.
From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode notation.

From eIris.proofmode Require Import base reduction inductive intros.

Section Channels.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l nl tl lh lt : loc.


  Local Definition tag_nil : Z := 0.
  Local Definition tag_cons : Z := 1.
  Local Definition tag_link : Z := 2.

  (* #[debug] *)
  EI.ind
  Inductive is_queue : loc → loc → list val → iProp :=
      | nill_is_queue l : l ↦ #tag_nil -∗ is_queue l l []
      | cons_is_queue v vs l nl tl : 
          l ↦ #tag_cons -∗ (l +ₗ 1) ↦ v -∗ (l +ₗ 2) ↦ #nl -∗ 
          is_queue nl tl vs -∗ is_queue l tl (v :: vs)
      | link_is_queue vs l nl tl : 
          l ↦ #tag_cons -∗ (l +ₗ 2) ↦ #nl -∗ 
          is_queue nl tl vs -∗ is_queue l tl vs.

  Print is_queue_pre.

  Definition new_queue : val := λ: <>,
    let: "end" := AllocN #3 #() in
    ("end" +ₗ #0) <- #tag_nil;;
    ("end", "end").

  Definition enqueue : val := λ: "t" "x",
    let: "end" := AllocN #3 #() in
    ("end" +ₗ #0) <- #tag_nil;;

    ("t" +ₗ #1) <- "x";;
    ("t" +ₗ #2) <- "end";;
    ("t" +ₗ #0) <- #tag_cons;;

    "end".

  Definition dequeue : val :=
    rec: "dequeue" "d" :=
      if: !("d" +ₗ #0) = #tag_nil then
        "dequeue" "d"
      else if: !("d" +ₗ #0) = #tag_cons then
        (!("d" +ₗ #2), !("d" +ₗ #1))
      else
        "dequeue" !("d" +ₗ #2).

  Definition link_queue : val := λ: "t" "h",
    let: "node" := !"t" in
    let: "lh" := !"h" in
    ("node" +ₗ #2) <- "lh";;
    ("node" +ₗ #0) <- #tag_link;;
    #().

  Lemma new_queue_spec:
    {{{ True }}}
      new_queue #()
    {{{ lh lt, RET (#lh, #lt);
        is_queue lh lt [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc l as "Hl /="; first by lia.
    wp_pures.
    iDestruct (array_cons with "Hl") as "[Hl0 Hl]".
    iDestruct (array_cons with "Hl") as "[Hl1 Hl]".
    iDestruct (array_cons with "Hl") as "[Hl2 Hl]".
    rewrite !Loc.add_assoc Loc.add_0.
    wp_store.
    wp_pures. iModIntro. iApply "HΦ".
    iApply nill_is_queue. by iFrame.
  Qed.