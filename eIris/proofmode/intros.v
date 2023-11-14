From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.bi Require Export bi telescopes.

From eIris.proofmode Require Import base.
From eIris.common Extra Dependency "stdpp.elpi" as stdpp.
From eIris.common Extra Dependency "tokenize.elpi" as tokenize.
From eIris.common Extra Dependency "parser.elpi" as parser.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.
From eIris.proofmode.elpi Extra Dependency "eiris_tactics.elpi" as eiris_tactics.

From iris.heap_lang Require Import proofmode.

Elpi Tactic eiIntros.

Elpi Accumulate File stdpp.
Elpi Accumulate File iris_ltac.
Elpi Accumulate File tokenize.
Elpi Accumulate File parser.
Elpi Accumulate File eiris_tactics.
Elpi Accumulate lp:{{
  shorten coq.ltac.{ open, thenl, all }.

  pred parse_args i:list argument, o:list intro_pat.
  parse_args [tac Intro, str Args] [iCoqIntro Intro | IPS] :- !,
    parse_args [str Args] IPS.
  parse_args [str Args] IPS :- !,
    tokenize Args T, !,
    parse_ipl T IPS, !.
  parse_args Args _ :-
    coq.ltac.fail 0 "Did not recognize arguments" Args.

  solve (goal Ctx Trigger Type Proof Args) GL :-
    parse_args Args IPS,
    !,
    do-iStartProof (hole Type Proof) IH,
    go_iIntros IPS IH.
    
}}.
Elpi Typecheck.


Tactic Notation "eiIntros" :=
  elpi eiIntros asdfasf.

Tactic Notation "eiIntros" "(" simple_intropattern_list(l) ")" :=
  elpi eiIntros ltac_tactic:( intros l ) "".

Tactic Notation "eiIntros" string(x) :=
  elpi eiIntros ltac_string:(x).

Tactic Notation "eiIntros" "(" simple_intropattern_list(l) ")" string(x) :=
  elpi eiIntros ltac_tactic:( intros l ) ltac_string:(x).

Section Proof.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Lemma intros_1 (P : iProp) :
    □ P -∗ P .
  Proof.
    eiIntros "#?".
    iAssumption.
  Qed.

  (* Elpi Trace Browser. *)
  Lemma intros_2 (P : nat -> iProp) :
    □ (∃b, ((P b ∗ P 2) ∨ P 3)) -∗ (∃b, P b) -∗ ∃y, P y.
  Proof.
    eiIntros "#[%b [[H1 H11] | H3]] [%c H2]".
    - by iExists b.
    - by iExists c.
  Qed.
End Proof.
