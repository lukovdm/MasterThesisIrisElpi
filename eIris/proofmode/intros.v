From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.bi Require Export bi.
From iris.algebra Require Import ofe monoid list.

From stdpp Require Import numbers.

From eIris.proofmode Require Import base reduction inductiveDB inductive.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.
From eIris.proofmode.elpi Extra Dependency "eiris_tactics.elpi" as eiris_tactics.

From iris.heap_lang Require Import proofmode notation.

Elpi Tactic eiIntros.
Elpi Accumulate Db reduction.db.
Elpi Accumulate Db induction.db.
Elpi Accumulate File eiris_tactics.
Elpi Accumulate lp:{{
  shorten coq.ltac.{ open, thenl, all }.

  pred parse_args i:list argument, o:list intro_pat.
  parse_args [tac Intro, str Args] [iCoqIntro Intro | IPS] :- !,
    tokenize Args T, !,
    parse_ipl T IPS.
  parse_args [str Args] IPS :- !,
    tokenize Args T, !,
    parse_ipl T IPS.
  parse_args Args _ :-
    coq.ltac.fail 0 "Did not recognize arguments" Args.

  solve (goal _ _ Type Proof [str "debug" | Args]) GS :-
    gettimeofday Start,
    [get-option "debug" tt, get-option "start" Start] => (
      parse_args Args IPS, !,
      do-iStartProof (hole Type Proof) IH, !,
      do-iIntros IPS IH (ih\ set-ctx-count-proof ih _), !,
      coq.ltac.collect-goals Proof GL SG,
      all (open pm-reduce-goal) GL GL',
      all (open show-goal) GL' _,
      std.append GL' SG GS
    ).
  solve (goal _ _ Type Proof Args) GS :-
    parse_args Args IPS, !,
    do-iStartProof (hole Type Proof) IH, !,
    do-iIntros IPS IH (ih\ set-ctx-count-proof ih _), !,
    coq.ltac.collect-goals Proof GL SG,
    all (open pm-reduce-goal) GL GL',
    std.append GL' SG GS.
}}.
Elpi Typecheck.

Elpi Tactic eiDestruct.
Elpi Accumulate Db reduction.db.
Elpi Accumulate Db induction.db.
Elpi Accumulate File eiris_tactics.
Elpi Accumulate lp:{{
  shorten coq.ltac.{ open, thenl, all }.

  pred parse_destruct_args i:list argument, o:ident, o:intro_pat.
  parse_destruct_args [str IDS, str Args] (iNamed IDS) IP :- !,
    tokenize Args T, !,
    parse_ipl T [IP].
  parse_destruct_args Args _ _ :-
    coq.ltac.fail 0 "Did not recognize arguments" Args.

  solve (goal _ _ Type Proof [str "debug" | Args]) GS :-
    gettimeofday Start,
    [get-option "debug" tt, get-option "start" Start] => (
      parse_destruct_args Args ID IP, !,
      do-iStartProof (hole Type Proof) IH, !,
      do-iDestruct ID IP IH (ih\ set-ctx-count-proof ih _), !,
      coq.ltac.collect-goals Proof GL SG,
      all (open pm-reduce-goal) GL GL',
      all (open show-goal) GL' _,
      std.append GL' SG GS
    ).
  solve (goal _ _ Type Proof Args) GS :-
    parse_destruct_args Args ID IP, !,
    do-iStartProof (hole Type Proof) IH, !,
    do-iDestruct ID IP IH (ih\ set-ctx-count-proof ih _), !,
    coq.ltac.collect-goals Proof GL SG,
    all (open pm-reduce-goal) GL GL',
    std.append GL' SG GS.
}}.
Elpi Typecheck.

Elpi Tactic eiInduction.
Elpi Accumulate Db reduction.db.
Elpi Accumulate Db induction.db.
Elpi Accumulate File eiris_tactics.
Elpi Accumulate lp:{{
  shorten coq.ltac.{ open, thenl, all }.

  pred do-iInduction i:ident, i:intro_pat, i:ihole, o:(ihole -> prop).
  do-iInduction ID IP (ihole _ (hole Type _) as IH) C :-
    find-hyp ID Type (app [global GREF | Args]),
    inductive-ind GREF INDLem, !,
    if-debug (coq.say "Induction on" INDLem Args),
    inductive-type GREF T, !,
    if-debug (coq.say "with Type" T),
    do-iInduction.inner ID IP T (app [global INDLem]) Args IH C.

  pred do-iInduction.inner i:ident, i:intro_pat, i:indt-decl, i:term, i:list term, i:ihole, o:(ihole -> prop).
  do-iInduction.inner ID IP (inductive _Name _In-Or-Co Arity Constructors) (app INDLem) Args (ihole _ (hole Type _) as IH) C :-
    Type = {{ envs_entails _ lp:P }},
    std.map Args (x\r\ sigma N T I\ decl x N T, coq.name->id N I, r = par I _ T x ) Pars, !,
    replace-params-bo Pars P Phi, !,
    if-debug (coq.say "phi is" Phi),
    Lem = app {std.append INDLem [Phi]},
    if-debug (coq.say "Lem to apply" Lem),
    % Apply induction lemma
    do-iApplyLem Lem IH [] [IntroIH, IHyp],
    % Apply induction hyp to goal
    do-iApplySimpleExact IHyp ID,
    % Introduce created goal
    std.map {std.iota {type-depth {coq.arity->term Arity} } } (x\r\ r = iPure none) Pures,
    (pi f\ std.length (Constructors f) NConstr),
    if (IP = iAll) (
        IP' = iList {std.map {std.iota NConstr} (x\r\ r = [iFresh])}
      ) (IP' = IP),
    do-iIntros {std.append [iModalIntro| Pures] [IP']} IntroIH C.
  do-iInduction.inner HID IP (parameter _ _ _ IND) (app INDLem) [A | Args] IH C :-
    pi p\ do-iInduction.inner HID IP (IND p) (app {std.append INDLem [A]}) Args IH C.


  pred parse_destruct_args i:list argument, o:ident, o:intro_pat.
  parse_destruct_args [str IDS, str Args] (iNamed IDS) IP :- !,
    tokenize Args T, !,
    parse_ipl T [IP].
  parse_destruct_args Args _ _ :-
    coq.ltac.fail 0 "Did not recognize arguments" Args.

  solve (goal _ _ Type Proof [str "debug" | Args]) GS :- !,
    gettimeofday Start,
    [get-option "debug" tt, get-option "start" Start] => (
      parse_destruct_args Args ID IP, !,
      do-iStartProof (hole Type Proof) IH, !,
      do-iInduction ID IP IH (ih\ set-ctx-count-proof ih _), !,
      if-debug (coq.say "Induction done"),
      coq.ltac.collect-goals Proof GL SG, !,
      all (open pm-reduce-goal) GL GL', !,
      all (open show-goal) GL' _, !,
      std.append GL' SG GS
    ).
  solve (goal _ _ Type Proof Args) GS :-
    parse_destruct_args Args ID IP, !,
    do-iStartProof (hole Type Proof) IH, !,
    do-iInduction ID IP IH (ih\ set-ctx-count-proof ih _), !,
    coq.ltac.collect-goals Proof GL SG,
    all (open pm-reduce-goal) GL GL',
    std.append GL' SG GS.
}}.
Elpi Typecheck.

Tactic Notation "eiIntros" string(x) :=
  elpi eiIntros ltac_string:(x).

Tactic Notation "eiDestruct" string(x) "as" string(y) :=
  elpi eiDestruct ltac_string:(x) ltac_string:(y).

Tactic Notation "eiDestruct" string(x) :=
  elpi eiDestruct ltac_string:(x) "**".

Tactic Notation "eiInduction" string(x) "as" string(y) :=
  elpi eiInduction ltac_string:(x) ltac_string:(y).

Tactic Notation "eiInduction" string(x) :=
  elpi eiInduction ltac_string:(x) "**".

Section Proof.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  (* #[debug]
  EI.ind 
  Inductive is_list_alt (q : Qp) : val → list val → iProp :=
    | empty_is_list : is_list_alt q NONEV []
    | empty_alt_is_list : is_list_alt q NONEV [NONEV]
    | cons_is_list l v vs tl : l ↦{#q} (v,tl) -∗ is_list_alt q tl vs -∗ is_list_alt q (SOMEV #l) (v :: vs). *)

  (* Lemma intros_ind (q : Qp) (v : val) (vs : list val) :
    is_list_alt q v vs -∗ is_list_alt q v vs.
  Proof.
    eiIntros "H".
    eiDestruct "H"; iApply is_list_alt_unfold_2.
    + by iLeft.
    + iRight. by iLeft.
    + iRight. by iRight.
  Qed. *)

  EI.ind 
  Inductive is_list (q : Qp) : val → list val → iProp :=
    | empty_is_list : is_list q NONEV []
    | cons_is_list l v vs tl : l ↦{#q} (v,tl) -∗ is_list q tl vs -∗ is_list q (SOMEV #l) (v :: vs).

  Print is_list_pre.

  Lemma ind_test_1 (q q' : Qp) (v : val) (vs : list val) :
    is_list q v vs ∗ is_list q' v vs ∗-∗ is_list (q+q') v vs.
  Proof.
    iSplit.
    - eiIntros "[Hq Hq']".
      iRevert "Hq'".
      eiInduction "Hq" as "[IH|[%l' [%v' [%vs' [%tl' (Hl' & IH & %Hx & %Hy)]]]]]"; eiIntros "Hq'".
      + iApply is_list_unfold_2.
        iLeft.
        iFrame.
      + simplify_eq.
        iApply is_list_unfold_2.
        iRight.
        iExists l', v', vs', tl'.
        eiDestruct "Hq'" as "[[%Hl %Hv] | [%l'' [%v'' [%vs'' [%tl'' (Hl & Hilq' & %Hl & %Hv)]]]]]"; simplify_eq.
        iCombine "Hl' Hl" as "Hl" gives %[_ ?]; simplify_eq.
        iFrame.
        iDestruct "IH" as "[IH _]".
        iSplitL.
        * iApply ("IH" with "[$]").
        * iSplit; iPureIntro; done.
    - eiIntros "Hi".
      eiInduction "Hi" as "[IH|[%l [%v' [%vs' [%tl ([Hq Hq'] & [[Hiq Hiq'] _] & %Hx & %Hy)]]]]]".
      + iDestruct "IH" as "[-> ->]".
        iSplitL.
        * iApply is_list_unfold.
          iLeft.
          by iPureIntro.
        * iApply is_list_unfold.
          iLeft.
          by iPureIntro.
      + iSplitL "Hq Hiq".
        * iApply is_list_unfold.
          iRight.
          iExists l, v', vs', tl.
          iFrame.
          by iPureIntro.
        * iApply is_list_unfold.
          iRight.
          iExists l, v', vs', tl.
          iFrame.
          by iPureIntro.
  Qed.

  Lemma ind_test_2 (q : Qp) (v : val) (vs : list val) :
    is_list q v vs -∗ ⌜vs = []⌝ ∨ ⌜(q ≤ 1)%Qp⌝.
  Proof.
    eiIntros "[Hv Hvs | (%l & %v' & %vs' & %tl & Hl & _ & _ & _)]".
    - iLeft.
      iFrame.
    - iRight.
      iEval (iApply pointsto_valid) in "Hl".
      iRevert "Hl".
      iPureIntro.
      intros Hq.
      by apply dfrac_valid in Hq.
  Qed.


  (* Elpi Trace Browser. *)
  Lemma intros_1 (Q : Prop) (P : nat -> iProp) :
    ∀ x:nat, ∀ y:nat, ∀ z:nat, □ P x -∗ P x.
  Proof.
    elpi eiIntros "% % % #H @H".
  Qed.

  (* Elpi Trace Browser. *)
  Lemma intros_2 (P : nat -> iProp) :
    □ (∃b, ((P b ∗ P 2) ∨ P 3)) -∗ (∃b, P b) -∗ ∃y, P y.
  Proof.
    elpi eiIntros "#[%b [[H1 H11] | H3]] [%c H2]".
    - by iExists b.
    - by iExists c.
  Qed.
End Proof.
