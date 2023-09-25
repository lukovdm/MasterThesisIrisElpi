From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.

From eIris.common Extra Dependency "stdpp.elpi" as stdpp.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.
From eIris.common Extra Dependency "tokenize.elpi" as tokenize.

From iris.heap_lang Require Import proofmode.

Elpi Tactic eiIntros.

Elpi Accumulate File stdpp.
Elpi Accumulate File iris_ltac.
Elpi Accumulate File tokenize.
Elpi Accumulate lp:{{
  % Implementing a reductive descent parser https://homes.cs.washington.edu/~bodik/ucb/cs164/sp12/lectures/08-parsers-in-prolog-sp12.pdf
  kind intro_pat type.
  type iFresh, iDrop, iFrame, iPureIntro, iModalIntro, iSimpl, iDone, iForall, iAll intro_pat.
  type iIdent option string -> intro_pat.
  type iList list (list intro_pat) -> intro_pat.
  type iPure option string -> intro_pat.
  type iIntuitionistic intro_pat -> intro_pat.
  type iSpatial intro_pat -> intro_pat.
  type iModalElim intro_pat -> intro_pat.
  type iRewrite direction -> intro_pat.
  % type iClear sel_pat -> intro_pat.
  % type iClearFrame sel_pat -> intro_pat.

  pred parse_ilist i:list token, o:list token, o:list (list intro_pat).
  parse_ilist [tBracketR | TS] [tBracketR | TS] [[]].
  parse_ilist TS R [[IP] | LL'] :-
    parse_ip TS [tBar | RT] IP,
    parse_ilist RT R LL'.
  parse_ilist TS R [[IP | L] | LL'] :-
    parse_ip TS RT IP,
    parse_ilist RT R [L | LL'].

  pred parse_conj_ilist i:list token, o:list token, o:list intro_pat.
  parse_conj_ilist TS [tParenR | R] [IP] :-
    parse_ip TS [tParenR | R] IP.
  parse_conj_ilist TS R [IP | L'] :-
    parse_ip TS [tAmp | RT] IP,
    parse_conj_ilist RT R L'.

  pred parse_ip i:list token, o:list token, o:intro_pat.
  parse_ip [tName "_" | TS] TS iDrop.
  parse_ip [tName X | TS] TS (iIdent (some X)).
  parse_ip [tAnon | TS] TS (iFresh).
  parse_ip [tFrame | TS] TS (iFrame).
  parse_ip [tBracketL | TS] TS' (iList L) :-
    parse_ilist TS [tBracketR | TS'] L,
    {std.length L} > 0.
  parse_ip [tParenL | TS] TS' IP :-
    parse_conj_ilist TS [tParenR | TS'] L',
    {std.length L'} >= 2,
    foldr {std.drop-last 2 L'} (iList [{std.take-last 2 L'}]) (x\ a\ r\ r = iList [[x, a]]) IP.
  parse_ip [tPure X | TS] TS (iPure X).
  parse_ip [tIntuitionistic | TS] TS (iIntuitionistic X) :-
    parse_ip TS TS' X.
  parse_ip [tSpatial | TS] TS' (iSpatial X) :-
    parse_ip TS TS' X.
  parse_ip [tModal | TS] TS' (iModalElim X) :-
    parse_ip TS TS' X.
  parse_ip [tRewrite D | TS] TS (iRewrite D).
  

  solve (goal _Ctx _Trigger _Type _Proof Args as G) GL :-
    coq.say Args.
}}.
Elpi Typecheck.
Elpi Trace Browser.
Elpi Query lp:{{
    tokenize "(a & b & c & d)" T,
    !,
    coq.say T,
    parse_ip T [] IP.
}}.

Section Proof.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Lemma intros (P : nat -> iProp) :
    ∀x, P x -∗ ∃y, P y.
  Proof.
    elpi eiIntros HP HQ [HP HQ] -> .
    elpi eiIntros x Hx "!> $ [[] | #[HQ HR]] /= !>".
    iIntros (x) "H".
    iExists x.
    iExact "H".
End Proof.
