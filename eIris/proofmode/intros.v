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
  parse_args [iCoqIntro Intro | IPS] (goal _ _ _ _ [tac Intro, str Args] as G) [SG] :-
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

  type ident_for_pat intro_pat -> ident -> tactic.
  ident_for_pat (iIdent ID) ID G [G].
  ident_for_pat _ (iAnon NT) G GL :-
    open (go_iFresh NT) G GL.

  type ident_for_pat.default intro_pat -> ident -> ident -> tactic.
  ident_for_pat.default (iIdent ID) _ ID G [G].
  ident_for_pat.default _ (iAnon NT) (iAnon NT) G GL.
  ident_for_pat.default _ _ (iAnon NT) G GL :-
    open (go_iFresh NT) G GL.

  type go_iExFalso tactic.
  go_iExFalso G GL :-
    open startProof G [G'],
    open (refine {{ @tac_ex_falso _ _ _ _ }}) G' GL.

  type go_iClear ident -> tactic.
  go_iClear ID G GL :-
    ident->term ID IDS IDT,
    open (refine {{ @tac_clear _ _ lp:IDT _ _ _ _ _ _ }}) G [G1, G2, G3],
    (open pm_reflexivity G1 []; coq.ltac.fail 0 "iClear:" IDS "not found"),
    (
      thenl [
        open pm_reduce,
        open tc_solve
      ] G2 []; 
      coq.ltac.fail 0 "iClear:" IDS "not affine and the goal not absorbing"
    ),
    thenl [
      open pm_reduce,
      open simpl,
    ] G3 GL.

  type go_iAndDestruct ident -> ident -> ident -> tactic.
  go_iAndDestruct HID H1ID H2ID G GL :-
    ident->term HID ID HIDT,
    ident->term H1ID _ H1IDT,
    ident->term H2ID _ H2IDT,
    open (refine {{ @tac_and_destruct _ _ lp:HIDT _ lp:H1IDT lp:H2IDT _ _ _ _ _ _ _ }}) G [G1, G2, G3],
    (open pm_reflexivity G1 []; coq.ltac.fail 0 "iAndDestruct:" ID "not found"),
    (
      thenl [
        open pm_reduce,
        open tc_solve
      ] G2 []; 
      coq.ltac.fail 0 "iAndDestruct: cannot destruct"
    ),
    thenl [
      open pm_reduce,
      open simpl,
      open (false-error "iAndDestruct: left or right not fresh")
    ] G3 GL.

  type go_iOrDestruct ident -> ident -> ident -> tactic.
  go_iOrDestruct HID H1ID H2ID G GL :-
    ident->term HID ID HIDT,
    ident->term H1ID _ H1IDT,
    ident->term H2ID _ H2IDT,
    open (refine {{ @tac_or_destruct _ _ lp:HIDT _ lp:H1IDT lp:H2IDT _ _ _ _ _ _ _ }}) G [G1, G2, G3],
    (open pm_reflexivity G1 []; coq.ltac.fail 0 "iOrDestruct:" ID "not found"),
    (open tc_solve G2 []; coq.ltac.fail 0 "iOrDestruct: cannot destruct"),
    thenl [
      open pm_reduce,
      open (false-error "iAndDestruct: left or right not fresh"),
      open split
    ] G3 GL.

  type go_iExistDestruct ident -> option string -> ident -> tactic.
  go_iExistDestruct ID X HID G GL :-
    ident->term ID _ IDT,
    ident->term HID _ HIDT, !, % only works with refine.warn not with just refine % TODO: figure out why
    open (refine.warn {{ @tac_exist_destruct _ _ _ lp:IDT _ lp:HIDT _ _ _ _ _ _ }}) G GL.% [G1, G2, G3, G4]
    % Why does into Exists have a name?

  type go_iExact ident -> tactic.
  go_iExact ID G [] :-
    ident->term ID _ IDT,
    open (refine {{ @tac_assumption _ _ lp:IDT _ _ _ _ _ _ }}) G [G1, G2, G3],
    (open pm_reflexivity G1 []; coq.ltac.fail 0 "iExact:" ID "not found"),
    (open tc_solve G2 []; coq.ltac.fail 0 "iExact:" ID "does not match goal"),
    (
      thenl [
        open pm_reduce,
        open tc_solve
      ] G3 [];
      coq.ltac.fail 0 "iExact: remaining hypotheses not affine and the goal not absorbing"
    ).

  pred go_iDestruct i:ident, o:intro_pat, i:sealed-goal, o:list sealed-goal.
  go_iDestruct ID (iIdent ID) G [G].
  go_iDestruct (iAnon _) iFresh G [G]. 
  go_iDestruct ID iDrop G GL :-
    go_iClear ID G GL.
  go_iDestruct ID (iList [[]]) G GL :-
    thenl [
      go_iExFalso,
      go_iExact ID
    ] G GL.
  go_iDestruct ID (iList [[iPure none, IP]]) G GL :- !,
    ident_for_pat.default IP ID HID G [G'],
    go_iExistDestruct ID none HID G' GL.
    % This case now also handles the pure and case with typeclasses,
    % however, that is not neccessary as we can just backtrack in here
    % And take the next case if iExistsDestruct fails.
  go_iDestruct ID (iList [[IP1, IP2]]) G GL :-
    ident_for_pat.default IP1 ID ID1 G [G'],
    ident_for_pat IP2 ID2 G' [G''],
    thenl [
      go_iAndDestruct ID ID1 ID2,
      go_iDestruct ID1 IP1,
      go_iDestruct ID2 IP2
    ] G'' GL.
  go_iDestruct ID (iList [[IP1], [IP2]]) G GL :-
    ident_for_pat.default IP1 ID ID1 G [G'],
    ident_for_pat IP2 ID2 G' [G''],
    go_iOrDestruct ID ID1 ID2 G'' [G1, G2],
    go_iDestruct ID1 IP1 G1 GL1,
    go_iDestruct ID2 IP2 G2 GL2,
    std.append GL1 GL2 GL.
  go_iDestruct ID IP G [G] :-
    coq.say { calc ("eiDestruct: Skipping " ^ {std.any->string IP})}.

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
    open simpl G [G'],
    go_iIntros IPS G' GL.
  go_iIntros [iDone | IPS] G GL :-
    (open done G [G']; G' = G),
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
    go_iDestruct (iAnon N) (iList IPS) IntroGoal GL.
  go_iIntros [IP | IPS] G GL :-
    coq.say { calc ("eiIntro: Skipping " ^ {std.any->string IP})},
    go_iIntros IPS G GL.

  msolve [SG] GL :-
    open (parse_args IPS) SG [SG'],
    !,
    go_iIntros IPS SG' GL.
    
}}.
Elpi Typecheck.


Tactic Notation "eiIntros" :=
  elpi eiIntros "**".

Tactic Notation "eiIntros" "(" simple_intropattern_list(l) ")" :=
  elpi eiIntros ltac_tactic:( intros l ) "".

Tactic Notation "eiIntros" string(x) :=
  elpi eiIntros ltac_string:(x).

Tactic Notation "eiIntros" "(" simple_intropattern_list(l) ")" string(x) :=
  elpi eiIntros ltac_tactic:( intros l ) ltac_string:(x).

Section Proof.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).

  Elpi Trace Browser.
  Elpi Bound Steps 1000.
  Lemma intros (P : nat -> iProp) :
    (∃b, P b) -∗ ∃y, P y.
  Proof.
    eiIntros "[% H]".
    iExists a.
    iExact "H1".
  Qed.
End Proof.
