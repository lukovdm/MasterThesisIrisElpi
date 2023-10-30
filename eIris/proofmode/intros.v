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

  type parse_args (list intro_pat) -> open-tactic.
  parse_args [iCoqIntro Intro | IPS] (goal _ _ _ _ [tac Intro, str Args] as G) [SG] :- !,
    tokenize Args T, !,
    parse_ipl T IPS, !,
    coq.ltac.set-goal-arguments [] G (seal G) SG.
  parse_args IPS (goal _ _ _ _ [str Args] as G) [SG] :- !,
    tokenize Args T, !,
    parse_ipl T IPS, !,
    coq.ltac.set-goal-arguments [] G (seal G) SG.

  parse_args IPS (goal _ _ _ _ Args as G) [SG] :-
    coq.say Args,
    coq.ltac.fail 0 "Did not recognize arguments" Args.

  msolve [SG] GL :-
    open (parse_args IPS) SG [SG'],
    !,
    go_iIntros IPS SG' GL.
    
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

  (* Elpi Trace Browser. *)
  Lemma intros_2 (P : nat -> iProp) :
    □ (∃b, ((P b ∗ P 2) ∨ P 3)) -∗ (∃b, P b) -∗ ∃y, P y.
  Proof.
    eiIntros "#[%b [[H1 H11] | H3]] [%c H2]".
    - by iExists b.
    - by iExists c.
  Qed.
End Proof.
