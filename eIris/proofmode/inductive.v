From elpi Require Import elpi.
From iris.proofmode Require Import proofmode tactics coq_tactics reduction intro_patterns.
From iris.prelude Require Import options.
From iris.bi Require Import fixpoint.
From iris.algebra Require Import ofe monoid list.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation.
From stdpp Require Import base finite.

From eIris.proofmode Require Import proper.
From eIris.proofmode Require Import intros.

From eIris.proofmode Require Import base.
From eIris.common Extra Dependency "stdpp.elpi" as stdpp.
From eIris.common Extra Dependency "tokenize.elpi" as tokenize.
From eIris.common Extra Dependency "parser.elpi" as parser.
From eIris.proofmode.elpi Extra Dependency "iris_ltac.elpi" as iris_ltac.
From eIris.proofmode.elpi Extra Dependency "eiris_tactics.elpi" as eiris_tactics.

Context `{!heapGS Σ}.
Notation iProp := (iProp Σ).

#[arguments(raw)] Elpi Command EI.ind.
Elpi Accumulate lp:{{
  pred print-contructors i:list indc-decl.
  print-contructors [].
  print-contructors [constructor Name Arity | CS] :-
    coq.say Name "of type" { coq.term->string { coq.arity->term Arity } },
    print-contructors CS.

  pred constructor->term i:indc-decl, o:term.
  constructor->term (constructor _ Arity) T :- coq.arity->term Arity T.

  pred type-to-fun i:term, o:term.
  type-to-fun (prod N T F) (fun N FT FB) :- !,
    type-to-fun T FT, (pi x\ type-to-fun (F x) (FB x)).
  type-to-fun X X :- !.

  pred init-prod-to-bi-exist i:term, o:term.
  init-prod-to-bi-exist (prod N T F) {{ bi_exist lp:Fun}} :- !,
    (pi x\ init-prod-to-bi-exist (F x) (F' x)),
    Fun = (fun N T F').
  init-prod-to-bi-exist X X.

  pred last-rec-to-and i:term, i:list term, i:term, o:term.
  last-rec-to-and A B {{ bi_exist lp:{{ fun N T F}} }} {{ bi_exist lp:{{ fun N T F' }} }} :- !,
    (pi x\ last-rec-to-and A B (F x) (F' x)).
  last-rec-to-and A B {{ bi_sep lp:L lp:R }} {{ bi_sep lp:L lp:R' }} :- !,
    last-rec-to-and A B R R'.
  last-rec-to-and A B {{ bi_or lp:L lp:R }} {{ bi_or lp:L' lp:R' }} :- !,
    last-rec-to-and A B L L',
    last-rec-to-and A B R R'.
  last-rec-to-and F [] (app [F]) {{ True }}.

  pred last-rec-to-and.aux i:term, i:term, o:term.
  last-rec-to-and.aux A T {{ (⌜lp:A = lp:T⌝)%I }}.

  last-rec-to-and F [L | LS] (app [F, T | TS]) TS' :- !,
    std.fold2 LS TS {{ (⌜lp:L = lp:T⌝)%I }} (l\ t\ a\ r\ sigma TMP\ TMP = {{ (⌜lp:l = lp:t⌝)%I }}, r = {{ (lp:a ∗ lp:TMP)%I }}) TS'.

  pred top-wand-to-sepand i:term, o:term.
  top-wand-to-sepand {{ bi_emp_valid lp:T }} T' :- !,
    top-wand-to-sepand T T'.
  top-wand-to-sepand {{ bi_exist lp:{{ fun N T F}} }} {{ bi_exist lp:{{ fun N T F' }} }} :- !,
    (pi x\ top-wand-to-sepand (F x) (F' x)).
  top-wand-to-sepand {{ bi_wand lp:L lp:R }} {{ bi_sep lp:L lp:R' }} :- !,
    top-wand-to-sepand R R'.
  top-wand-to-sepand X X :- !.

  pred if-debug i:prop.
  if-debug P :- get-option "debug" tt, !, coq.say "[" {gettimeofday} "]", P.
  if-debug _ .

  pred constr-body-disj i:(term -> list indc-decl), o:(term -> term).
  constr-body-disj Constructors ConstrBo :-
    if-debug ((pi x\ print-contructors (Constructors x))),
    (pi f\ std.map (Constructors f)
      (x\ r\ sigma TMP1 TMP2\ 
        constructor->term x TMP1, 
        init-prod-to-bi-exist TMP1 TMP2, 
        top-wand-to-sepand TMP2 r) % You can't spill here otherwise the TMP1 and TMP2 will be bound in the outer scope.
      (ConstrBiTerms f)),
    if-debug ((pi f\ coq.say "------ Constructor Bi Terms" {std.map (ConstrBiTerms f) coq.term->string} (ConstrBiTerms f))),
    (pi f\ std.fold 
      { std.drop-last 1 (ConstrBiTerms f) } 
      { std.last (ConstrBiTerms f) }
      (x\ a\ r\ r = {{ bi_or lp:a lp:x }}) 
      (ConstrBo f)),
    if-debug (coq.say "------ Constructor body disjunction" {coq.term->string (ConstrBo {{ True }})} ConstrBo).

  pred constr-body i:term, i:(term -> list indc-decl), o:term, o:term.
  constr-body TypeTerm Constructors EBo Ty :-
    constr-body-disj Constructors ConstrBo,
    (pi b\ (type-to-fun ({{ uPred (iResUR Σ) }}) b :- !) => type-to-fun TypeTerm (FunTerm b)), % TODO: A proper PROP should be added not the hacky heap-lang one
    (pi b\
      % Save the variables of functions in a list
      (pi N T T1 F F1 A \ fold-map (fun N T F) A (fun N T1 F1) A :- !,
                                  fold-map T A T1 _, pi x\ fold-map (F x) [x | A] (F1 x) _) => 
      % When we hit our placeholder for the function body we replace it with the function body with the last application replaced by equalities for the arguments
      (pi L L' F B \ fold-map b L B L :- !, std.rev L [F | L'], last-rec-to-and F L' (ConstrBo F) B) => 
          fold-map {{fun F : lp:TypeTerm => lp:{{ FunTerm b }} }} [] Bo _),
    if-debug (coq.say "------- Body" { coq.term->string Bo } Bo),
    Ty = {{ lp:TypeTerm -> lp:TypeTerm }}, !,
    @keepunivs! => std.assert-ok! (coq.elaborate-skeleton Bo Ty EBo) "Type check body failed".

  pred type-to-proper i:term, o:term.
  type-to-proper Type EBo :-
    coq.say Type,
    (pi N T F A T1 F1 A1 \ fold-map (prod N T F) A (prod N T1 F1) (some {{ (.> lp:A1)%i_signature }}) :-
          fold-map T A T1 _, !, (pi x\ fold-map (F x) A (F1 x) (some A1))) =>
      (pi A \ fold-map {{ uPred (iResUR Σ) }} A {{ uPred (iResUR Σ) }} (some {{ bi_wand }}) :- !) =>
        fold-map Type none Type (some R),
      
    @keepunivs! => std.assert-ok! (coq.elaborate-skeleton {{ IProper (□> lp:R ==> lp:R) }} {{ (lp:Type -> lp:Type) -> Prop }} EBo) "Type check proper failed".

  % main is, well, the entry point
  main [indt-decl (inductive Name _In-Or-Co Arity Constructors)] :- 
    attributes A,
    coq.parse-attributes A [
      att "debug" bool,
    ] Opts,

    Opts => if-debug (coq.say "------ Creating inductive" Name),
    coq.arity->term Arity TypeTerm,
    Opts => if-debug (coq.say "------ With type" { coq.term->string TypeTerm }),

    Opts => constr-body TypeTerm Constructors EBo Ty,

    coq.env.add-const {calc (Name ^ "_pre")} EBo Ty ff C,
    Opts => if-debug (coq.say "const" C),

    Opts => type-to-proper TypeTerm Relation,
    coq.env.add-const {calc (Name ^ "_proper")} Relation _ ff R,
    Opts => if-debug (coq.say "Relation" R).
}}.
Elpi Typecheck.

Elpi Export EI.ind.

Elpi Tactic IProper_solver.
Elpi Accumulate File stdpp.
Elpi Accumulate File iris_ltac.
Elpi Accumulate File tokenize.
Elpi Accumulate File parser.
Elpi Accumulate File eiris_tactics.
Elpi Accumulate lp:{{
  shorten coq.ltac.{ open, thenl, all }.

  type go_iPoseLem term -> tactic.
  go_iPoseLem Lem G GL :-
    open go_iStartProof G [GoalStarted],
    open (go_iFresh N) GoalStarted [GoalFresh],
    @no-tc! => open (refine {{ tac_pose_proof _ lp:N _ _ (into_emp_valid_proj _ _ _ lp:Lem) _}}) GoalFresh [G1, G2],
    open (coq.ltac.call "iIntoEmpValid" []) G1 TCGL,
    all (open tc_solve) TCGL [],
    thenl [
      open pm_reduce,
      open (false-error "iPoseLem: not fresh"),
    ] G2 GL.

  pred unfold-pred i:string, i:goal, o:list sealed-goal.
  unfold-pred S (goal _Ctx _Trigger Type _Proof _Args as G) GL :- 
    coq.locate S (const IP),
    coq.env.const IP (some Bo) _,
    ((copy (global (const IP)) Bo :- !) => copy Type Type'),
    coq.reduction.lazy.bi-norm Type' NewType, % normal form becomes an infinite loop (why?), thus we use beta-iota
    refine.warn {{ _ : lp:NewType }} G GL.

  pred do-step i:sealed-goal, o:list sealed-goal.
  do-step G GL :-
    open (do-step.conn C) G GL.
    % do-step.aux C G GL.

  pred do-step.conn o:term, i:goal, o:list sealed-goal.
  do-step.conn C (goal _Ctx _Trigger Type _Proof _Args as G) [seal G] :-
    bi-top-level-conn Type C,
    coq.say C.

  pred do-step.aux i:term, i:sealed-goal, o:list sealed-goal.
  do-step.aux T G GL :- coq.say "do-step.aux" T G GL, fail.
  do-step.aux _ G GL :-
    Lem = {{@iProper iProp _ (□> bi_wand ==> □> bi_wand ==> bi_wand) bi_or}},
    go_iPoseLem Lem G GL.

  pred bi-top-level-conn i:term, o:term.
  bi-top-level-conn {{ envs_entails _ lp:P }} C :- !, bi-top-level-conn P C.
  bi-top-level-conn (app [HD | _]) C :- !, bi-top-level-conn HD C.
  bi-top-level-conn (primitive P) (primitive P) :- !.
  bi-top-level-conn P _ :- coq.say "Can't find top level connective in" P.

  
  msolve [SG] GL :- !,
    thenl! [
      open (unfold-pred "is_list_proper"),
      open (unfold-pred "is_list_pre"),
      open (unfold-pred "IProper"),
      open (unfold-pred "iPointwise_relation"),
      open (unfold-pred "iPersistant_relation"),
      open (unfold-pred "iRespectful"),
      open (coq.ltac.call "_iIntros0" [ trm {{ IAll }} ])
    ] SG [G],
    do-step G GL.
}}.
Elpi Typecheck.
Elpi Export IProper_solver.

Section Tests.
  Implicit Types l : loc.

  EI.ind 
  Inductive is_list : val → list val → iProp :=
    | empty_is_list : is_list NONEV []
    | cons_is_list l v vs tl : l ↦ (v,tl) -∗ is_list tl vs -∗ is_list (SOMEV #l) (v :: vs).

  Print is_list_pre.
  Print is_list_proper.

  Elpi Trace Browser.
  Local Lemma is_list_pre_proper_mono :
    is_list_proper is_list_pre.
  Proof.
    elpi IProper_solver.

    iApply (@iProper iProp _ (□> bi_wand ==> □> bi_wand ==> bi_wand) bi_or).
    3: { iAssumption. }
    - unfold iPersistant_relation.
      iModIntro.
      iIntros.

      iApply (@iProper iProp _ (.> bi_wand ==> bi_wand) (@bi_exist iProp _)).
      2: { iAssumption. }
      unfold iPointwise_relation.
      iIntros.

      iApply (@iProper iProp _ (.> bi_wand ==> bi_wand) (@bi_exist iProp _)).
      2: { iAssumption. }
      unfold iPointwise_relation.
      iIntros.

      iApply (@iProper iProp _ (.> bi_wand ==> bi_wand) (@bi_exist iProp _)).
      2: { iAssumption. }
      unfold iPointwise_relation.
      iIntros.

      iApply (@iProper iProp _ (.> bi_wand ==> bi_wand) (@bi_exist iProp _)).
      2: { iAssumption. }
      unfold iPointwise_relation.
      iIntros.

      iApply (@iProper iProp _ (bi_wand ==> bi_wand ==> bi_wand) bi_sep).
      3: { iAssumption. }
      + iIntros.
        iAssumption.
      + iIntros "?".
        iApply (@iProper iProp _ (bi_wand ==> bi_wand ==> bi_wand) bi_sep).
        3: { iAssumption. }
        * iAssumption.
        * iIntros "?".
          iAssumption.
    - unfold iPersistant_relation.
      iModIntro.
      iIntros "?".
      iAssumption.
  Qed.

  Local Lemma is_list_pre_mono (is_list1 is_list2 : val -d> list val -d> iProp): 
    ⊢ (□ ∀ hd vs, is_list1 hd vs -∗ is_list2 hd vs) → 
      ∀ hd vs, is_list_pre is_list1 hd vs -∗ is_list_pre is_list2 hd vs.
  Proof.
    iIntros "#H"; iIntros (hd vs) "HF1".
    rewrite /is_list_pre.
    destruct vs as [|v' vs'].
  Admitted.

  PrintCommand
  Definition is_list_pre : (val -d> list val -d> iProp) -d> val -d> list val -d> iProp := λ is_list hd vs,
    match vs with
    | [] => ⌜hd = NONEV⌝
    | v :: vs => ∃ l tl, ⌜hd = SOMEV #l⌝ ∗ l ↦ (v,tl) ∗ ▷ is_list tl vs
    end%I.

End Tests.

(* Proper als alternatief voor BiMonoPred, A New Look at Generalized Rewriting in TypeTheory MATTHIEU SOZEAU *)
(* wands beter begrijpen en bewijs rechts onder op hoek *)
(* Pas monopred aan naar andere definitie en kijk wat er kapot gaat *)
