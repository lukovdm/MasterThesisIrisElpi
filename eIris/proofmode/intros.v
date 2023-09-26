From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.

From eIris.common Extra Dependency "stdpp.elpi" as stdpp.
From eIris.common Extra Dependency "tokenize.elpi" as tokenize.
From eIris.common Extra Dependency "parser.elpi" as parser.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.
From eIris.proofmode.elpi Extra Dependency "eiStartProof.elpi" as startProof.

From iris.heap_lang Require Import proofmode.

Elpi Tactic eiIntros.

Elpi Accumulate File stdpp.
Elpi Accumulate File iris_ltac.
Elpi Accumulate File tokenize.
Elpi Accumulate File parser.
Elpi Accumulate File startProof.
Elpi Accumulate lp:{{
  shorten coq.ltac.{ open, thenl, all }.

  type parse_args (list intro_pat) -> open-tactic.
  parse_args IPS (goal _ _ _ Proof [str Args] as G) [SG] :-
    tokenize Args T, !,
    parse_ipl T IPS, !,
    coq.ltac.set-goal-arguments [] G (seal G) SG.

  type false-error string -> open-tactic.
  false-error S (goal _ _ {{ False }} _ _ as G) GL :- !, coq.ltac.fail 0 S.
  false-error _ G [seal G].

  type go (list intro_pat) -> tactic.
  % go IPS G GL :-
  %   coq.say "---------- go: ",
  %   coq.say IPS,
  %   coq.say G,
  %   coq.say "---------- End",
  %   fail.
  go [] G [G].
  go [iSimpl | IPS] G GL :-
    coq.ltac "simpl" G [G'],
    go IPS G' GL.
  go [iDrop | IPS] G GL :- !,
    open startProof G [G'],
    (
      open (refine {{ @tac_impl_intro_drop _ _ _ _ _ _ _ }}) G' [GRes];
      open (refine {{ @tac_wand_intro_drop _ _ _ _ _ _ _ _ }}) G' [GRes];
      (!, coq.ltac.fail 0 "Could not introduce", fail) % This never hits
      % TODO: Not sure what the forall case is.
    ),
    go IPS GRes GL.
  go [iIdent (some X) | IPS] G GL :- !,
    string->stringterm X ST,
    open startProof G [G'],
    (
      open (refine {{ @tac_impl_intro _ _ _ _ _ _ _ _ _ _ }}) G' [GRes];
      thenl [
        open (refine {{ @tac_wand_intro _ _ lp:ST _ _ _ _ _ }}),
        open (pm_reduce),
        open (false-error {calc ("eiIntro: " ^ X ^ " not fresh")}),
      ] G' [GRes];
      (!, coq.ltac.fail 0 "Could not introduce", fail) % This never hits
    ),
    go IPS GRes GL.
    
  go [IP | IPS] G GL :-
    coq.say { calc ("Skipping: " ^ {std.any->string IP})},
    go IPS G GL.

  msolve [SG] GL :-
    open (parse_args IPS) SG [SG'],
    !,
    go IPS SG' GL.
    
}}.
Elpi Typecheck.
Elpi Trace Browser.

Section Proof.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Lemma intros (P : nat -> iProp) :
    (∀x, P x) -∗ (∀x, P x) -∗ ∃y, P y.
  Proof.
    elpi eiIntros "_ H".
    (* Show Proof. *)
    (* elpi eiIntros x Hx "!> $ [[] | #[HQ HR]] /= !>". *)
    (* iIntros (x) "H". *)
    iSpecialize ("H" $! 0).
    iExists 0.
    iExact "H".
  Qed.
End Proof.
