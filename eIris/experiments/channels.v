From stdpp Require Import gmap numbers countable mapset.

From iris.program_logic Require Export atomic.
From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode notation.

From eIris.proofmode Require Import base reduction inductive tactics inductionTac.

Section Channels.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l nl tl lh lt : loc.

  Local Definition NIL : val := NONEV.
  Local Definition CONS (v:val) : val := SOMEV (#0, v).
  Local Definition LINK (l:loc) : val := SOMEV (#1, #l).

  Iris Inductive is_queue (tl : loc) : loc → list val → iProp :=
      | nill_is_queue : tl ↦ NIL -∗ is_queue tl tl []
      | cons_is_queue v vs l nl : 
          l ↦ CONS (v, #nl) -∗ is_queue tl nl vs -∗ is_queue tl l (v :: vs)
      | link_is_queue vs l nl : 
          l ↦ LINK nl -∗ 
          is_queue tl nl vs -∗ is_queue tl l vs.


  Definition new_queue : val := λ: <>,
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
      new_queue #()
    {{{ lh lt, RET (#lh, #lt);
        is_queue lh lt [] }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc l as "Hl /=".
    wp_pures. iModIntro. iApply "HΦ".
    iApply nill_is_queue. by iFrame.
  Qed.
End Channels.