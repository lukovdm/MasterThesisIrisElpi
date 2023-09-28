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
  parse_args [iCoqIntro Intro | IPS] (goal _ _ _ _ [str Intro, str Args] as G) [SG] :-
    tokenize Args T, !,
    parse_ipl T IPS, !,
    coq.ltac.set-goal-arguments [] G (seal G) SG.
  parse_args IPS (goal _ _ _ _ [str Args] as G) [SG] :-
    tokenize Args T, !,
    parse_ipl T IPS, !,
    coq.ltac.set-goal-arguments [] G (seal G) SG.

  parse_args IPS (goal _ _ _ _ Args as G) [SG] :-
    coq.say Args,
    coq.ltac.fail 0 "Did not regocnize arguments" Args.

  type false-error string -> open-tactic.
  false-error S (goal _ _ {{ False }} _ _ as G) GL :- !, coq.ltac.fail 0 S.
  false-error _ G [seal G].

  pred ident->term i:ident, o:string, o:term.
  ident->term (iNamed S) S T :-
    string->stringterm S ST,
    T = {{ INamed lp:ST }}.
  ident->term (iAnon N) "anon" T :-
    T = {{ IAnon lp:N }}.

  type intro string -> open-tactic.
  intro ID G GL :-
    std.assert! (coq.ltac.id-free? ID G) "eiIntro: name already taken",
    coq.id->name ID N,
    refine (fun N _ _) G GL.

  type go_iExFalso tactic.
  go_iExFalso G GL :-
    open startProof G [G'],
    open (refine.warn {{ tac_ex_falso _ _ _ _ }}) G' GL.

  type go_iDestruct ident -> list (list intro_pat) -> tactic.
  go_iDestruct ID [[]] G GL :-
    thenl [
      go_iExFalso,
      open (coq.ltac.call "iExact" [trm {ident->term ID _}])
    ] G GL.
  go_iDestruct ID IP G [G] :-
    coq.say { calc ("eiIntro: Skipping " ^ {std.any->string IP})}.

  type go_iFresh term -> open-tactic. % Not at all sure this works, in one call it works, but in the next it resets.
  go_iFresh N (goal Ctx Trigger {{ envs_entails (Envs lp:DP lp:DS lp:N) lp:Q }} Proof Args as G) [SG] :-
    SG = seal (goal Ctx Trigger {{ envs_entails (Envs lp:DP lp:DS (Pos.succ lp:N)) lp:Q }} Proof Args).

  type go_iIntros (list intro_pat) -> tactic.
  go_iIntros [] G [G].
  go_iIntros [iCoqIntro X | IPS] G GL :-
    thenl [
      open (coq.ltac.call-ltac1 X),
      go_iIntros IPS
    ] G GL.
  go_iIntros [iSimpl | IPS] G GL :-
    coq.ltac "simpl" G [G'],
    go_iIntros IPS G' GL.
  go_iIntros [iPure (some X) | IPS] G GL :-
    open (intro X) G [G'],
    go_iIntros IPS G' GL.
  go_iIntros [iDrop | IPS] G GL :- !,
    open startProof G [G'],
    (
      open (refine {{ @tac_impl_intro_drop _ _ _ _ _ _ _ }}) G' [GRes];
      open (refine {{ @tac_wand_intro_drop _ _ _ _ _ _ _ _ }}) G' [GRes];
      % TODO: Not sure what the forall case is.
      (!, coq.ltac.fail 0 "eiIntro: Could not introduce", fail)
    ),
    go_iIntros IPS GRes GL.
  go_iIntros [iIdent ID | IPS] G GL :- !,
    ident->term ID X T,
    open startProof G [G'],
    (
      open (refine {{ @tac_impl_intro _ _ lp:T _ _ _ _ _ _ _ }}) G' [GRes];
      thenl [
        open (refine {{ @tac_wand_intro _ _ lp:T _ _ _ _ _ }}),
        open (pm_reduce),
        open (false-error {calc ("eiIntro: " ^ X ^ " not fresh")}),
      ] G' [GRes];
      (!, coq.ltac.fail 0 {calc ("eiIntro: " ^ X ^ " could not introduce")}, fail)
    ),
    go_iIntros IPS GRes GL.
  go_iIntros [iFresh | IPS] G GL :-
    open startProof G [G'],
    open (go_iFresh N) G' [G''],
    coq.say N,
    go_iIntros IPS G'' GL. 
  go_iIntros [iList IPS | IPSS] G GL :-
    open startProof G [StartedGoal],
    open (go_iFresh N) StartedGoal [FreshGoal],
    go_iIntros [iIdent (iAnon N)] FreshGoal [IntroGoal],
    go_iDestruct (iAnon N) IPS IntroGoal GL.
  go_iIntros [IP | IPS] G GL :-
    coq.say { calc ("eiIntro: Skipping " ^ {std.any->string IP})},
    go_iIntros IPS G GL.

  msolve [SG] GL :-
    open (parse_args IPS) SG [SG'],
    !,
    go_iIntros IPS SG' GL.
    
}}.
Elpi Typecheck.
Elpi Trace Browser.


Tactic Notation "eiIntros" string(x) :=
  elpi eiIntros ltac_string:(x).

Tactic Notation "eiIntros" :=
  elpi eiIntros "**".

Tactic Notation "eiIntros" "(" simple_intropattern_list(x) ")" :=
  let pureintro := intros x in
  elpi eiIntros pureintro "".

Section Proof.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Lemma intros (P : nat -> iProp) :
    False -∗ (P 0 ∨ P 1) -∗ ∃y, P y.
  Proof.
    eiIntros "[]".
    (* eiIntros (a). *)
    eiIntros "?".
    eiIntros "? ? ?".
    eiIntros "? ? ?".
    let i := iFresh in
    let j := iFresh in
    elpi eiIntros asdf asdf (i) (j).
    iIntros "[H1|H2]".
    Show Proof.
    iDestruct "H1" as "[H1 | H2]".
    (* iSpecialize ("H" $! 0). *)
    iExists a.
    iExact "H1".
  Qed.
End Proof.
