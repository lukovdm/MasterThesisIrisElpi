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
  Local Definition DEL (l:val) : val := SOMEV (#1, l).

  Iris Inductive is_list_with_tl (tl : loc) : loc → list val → iProp :=
    | is_list_with_tl_nil : tl ↦ NIL -∗ is_list_with_tl tl tl []
    | is_list_with_tl_cons v vs l l' :
      l ↦ CONS (v,#l') -∗ is_list_with_tl tl l' vs -∗ is_list_with_tl tl l (v :: vs)
    | is_list_with_tl_del vs l l' :
      l ↦ DEL #l' -∗ is_list_with_tl tl l' vs -∗ is_list_with_tl tl l vs.


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
End Channels.