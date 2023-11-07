From elpi Require Import elpi.
From iris.proofmode Require Import proofmode tactics coq_tactics reduction intro_patterns class_instances spec_patterns.
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
  type-to-fun (prod N T F) (fun N T FB) :- !,
    (pi x\ type-to-fun (F x) (FB x)).
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
  last-rec-to-and F [L | LS] (app [F, T | TS]) TS' :-
    {std.length LS} = {std.length TS}, !,
    std.fold2 LS TS {{ (⌜lp:L = lp:T⌝)%I }} (l\ t\ a\ r\ sigma TMP\ TMP = {{ (⌜lp:l = lp:t⌝)%I }}, r = {{ (lp:a ∗ lp:TMP)%I }}) TS'.
  last-rec-to-and _ [_ | _] (app [T | TS]) _ :-
    coq.error "EI.Ind: " {coq.term->string (app [T | TS])} "has to many or to few arguments".

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

  type show-goal open-tactic.
  show-goal (goal _Ctx _Trigger Type Proof _ as G) [seal G] :-
    coq.say "Goal:" {coq.term->string Proof} ":" {coq.term->string Type}.

  type go_iModIntro tactic.
  go_iModIntro G GL :-
    open go_iStartProof G [GoalStarted],
    @no-tc! => open (refine {{ tac_modal_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ }}) GoalStarted [G1, G2, G3, G4, G5, G6],
    open tc_solve G1 [],
    open tc_solve G2 [],
    open tc_solve G3 [],
    open pm_reduce G4 [G4'],
    open tc_solve G4' [],
    open (coq.ltac.call "iSolveSideCondition" []) G5 [],
    open pm_prettify G6 GL.

  type go_iPoseProper term -> term -> ident -> tactic.
  go_iPoseProper R F (iAnon N) G GL :-
    open go_iStartProof G [GoalStarted],
    open (go_iFresh N) GoalStarted [GoalFresh],
    ident->term (iAnon N) _ NT,
    @no-tc! => open (refine.warn {{ tac_pose_proof _ lp:NT _ _ (into_emp_valid_proj _ _ _ (iproper_top_to_iproper _ _ _ _ _ (_ : IProperTop lp:R lp:F _))) _}}) GoalFresh [G1, G2, G3],
    open (coq.ltac.call "iIntoEmpValid" []) G1 TCGL,
    all (open tc_solve) TCGL [],
    open tc_solve G2 [],
    thenl [
      open pm_reduce,
      open (false-error "iPoseLem: not fresh"),
    ] G3 GL.

  type go_iSpecializeWand ident -> tactic.
  go_iSpecializeWand ID G GL :-
    open go_iStartProof G [GoalStarted],
    ident->term ID _IDS IDT,
    @no-tc! => open (refine.norm {{ tac_specialize_assert_no_am _ lp:IDT _ false [] _ _ _ _ _ _ _ _ _}}) GoalStarted [G1, G2, G3, G4],
    coq.say "specialize pre reflexivity",
    open show-goal G1 _,
    open pm_reflexivity G1 [],
    coq.say "specialize pre tc_solve 1",
    open show-goal G2 _,
    open tc_solve G2 [],
    coq.say "specialize pre tc_solve 2",
    open show-goal G3 _,
    open tc_solve G3 [],
    coq.say "specialize pre reduce",
    open show-goal G4 _,
    open pm_reduce G4 [G5],
    open (refine {{ conj _ _ }}) G5 GL.

  type go_iApplySimpleHyp ident -> tactic.
  go_iApplySimpleHyp ID G GL :-
    open go_iStartProof G [GoalStarted],
    ident->term ID _IDS IDT,
    @no-tc! => open (refine.warn {{ tac_apply _ lp:IDT _ _ _ _ _ _ _ }}) GoalStarted [G1, G2, G3],
    coq.say "apply pre reflexivity",
    open show-goal G1 _,
    open pm_reflexivity G1 [],
    coq.say "apply pre tc_solve",
    open show-goal G2 _,
    open tc_solve G2 [],
    coq.say "apply pre reduce",
    open show-goal G3 _,
    open pm_reduce G3 GL.

  type go_iApplyProper term -> term -> tactic.
  go_iApplyProper R F G GL :-
    coq.say "Starting go_iApplyProper" R F,
    go_iPoseProper R F ID G [GPosed],
    coq.say "Posed Lemma" ID,
    open show-goal GPosed _,
    go_iApplyProper.aux ID GPosed GL.
  go_iApplyProper.aux ID G GL :- 
    coq.say "simpleApplyHyp" ID,
    open show-goal G _,
    go_iApplySimpleHyp ID G GL.
  go_iApplyProper.aux ID G GL :-
    coq.say "specialize " ID,
    open show-goal G _,
    go_iSpecializeWand ID G GL',
    go_iApplyProper.aux ID {std.last GL'} GL'',
    std.append {std.drop-last 1 GL'} GL'' GL.

  pred unfold-id i:string, i:goal, o:list sealed-goal.
  unfold-id S G GL :- 
    coq.locate S (const IP),
    unfold-gref (const IP) G GL.

  pred unfold-gref i:gref, i:goal, o:list sealed-goal.
  unfold-gref (const IP) (goal _Ctx _Trigger Type _Proof _Args as G) GL :-
    coq.env.const IP (some Bo) _,
    ((copy (global (const IP)) Bo :- !) => copy Type Type'),
    coq.reduction.lazy.bi-norm Type' NewType,
    refine {{ _ : lp:NewType }} G GL.

  pred do-step i:sealed-goal, o:list sealed-goal.
  do-step G GL :-
    open (do-step.conn C LF RF) G _,
    do-step.aux C LF RF G GL.

  pred do-step.conn o:term, o:term, o:term, i:goal, o:list sealed-goal.
  do-step.conn R LF RF (goal _Ctx _Trigger Type _Proof _Args as G) [seal G] :-
    top-relation Type R, !,
    relation-on Type LF RF.

  pred do-step.aux i:term, i:term, i:term, i:sealed-goal, o:list sealed-goal.
  do-step.aux {{ @iRespectful }} _ _ G GL :- !,
    coq.say "==>",
    list->listterm [ {{ IPure (IGallinaAnon) }}, {{ IPure (IGallinaAnon) }}, {{ IIntuitionistic (IFresh) }} ] Args,
    open (coq.ltac.call "_iIntros0" [ trm Args ]) G GL.
  do-step.aux {{ @iPointwise_relation }} _ _ G GL :- !,
    coq.say ".>",
    list->listterm [ {{ IPure (IGallinaAnon) }} ] Args,
    open (coq.ltac.call "_iIntros0" [ trm Args ]) G GL.
  do-step.aux {{ @iPersistent_relation }} _ _ G GL :- !,
    coq.say "□>",
    go_iModIntro G GL.
  do-step.aux R (app FS) _ G GL :- 
    std.exists { std.iota {std.length FS} } (n\ std.take n FS F),
    coq.say "Apply relation" R "with" {coq.term->string (app F)},
    go_iApplyProper R (app F) G GL.
  do-step.aux _ (global (const F)) _ G GL :-
    coq.say "Unfolding" F,
    open (unfold-gref (const F)) G GL.
  do-step.aux T F _ _ _ :- !,
    coq.say "No case for relation" T "with " {coq.term->string F} "😢 stopping".

  pred top-relation i:term, o:term.
  top-relation {{ envs_entails _ lp:P }} C :- !, top-relation P C.
  top-relation (app [HD | _]) C :- !, top-relation HD C.
  top-relation (primitive P) (primitive P) :- !.
  top-relation (global P) (global P) :- !.
  top-relation P _ :- coq.error "Can't find top level connective in" P.

  pred relation-on i:term, o:term, o:term.
  relation-on {{ envs_entails _ lp:{{ (app AS) }} }} L R :- !, 
    std.take-last 2 AS [L, R].

  msolve [SG] GL :- !,
    thenl! [
      open (unfold-id "is_list_proper"),
      open (unfold-id "IProper"),
      open (go_iStartProof),
    ] SG [G],
    coq.ltac.repeat! do-step G GL.
}}.
Elpi Typecheck.
Elpi Export IProper_solver.

Tactic Notation "iSpecializePat" open_constr(H) constr(pat) :=
  let pats := spec_pat.parse pat in iSpecializePat_go H pats.

Section Tests.
  Implicit Types l : loc.

  EI.ind 
  Inductive is_list : val → list val → iProp :=
    | empty_is_list : is_list NONEV []
    | cons_is_list l v vs tl : l ↦ (v,tl) -∗ is_list tl vs -∗ is_list (SOMEV #l) (v :: vs).

  (* Print is_list_pre.
  Print is_list_proper. *)

  Elpi Trace Browser.
  Local Lemma is_list_pre_proper_mono :
    is_list_proper is_list_pre.
  Proof.
    elpi IProper_solver.
(*     
    (* Start proof *)
    unfold is_list_proper, IProper.

    (* Respectfull *)
    iIntros "% % #?".

    (* Pointwise *)
    iIntros "%".

    (* Pointwise *)
    iIntros "%".

    (* Relation *)
    try iApply (iProper (□> .> .> bi_wand ==> .> .> bi_wand) is_list_pre).
    unfold is_list_pre.

    (* Relation *)
    iApply (iProper (_ ==> _ ==> bi_wand) bi_or).
     *)
    (* notypeclasses refine (tac_pose_proof _ (IAnon 2) _ _ (into_emp_valid_proj _ _ _ (iproper_top_to_iproper _ _ _ _ _ (_ : IProperTop bi_wand bi_or _))) _);
    [iIntoEmpValid; tc_solve
    |tc_solve
    |pm_reduce].
    notypeclasses refine (tac_specialize_assert _ (IAnon 2) _ false false [] _ _ _ _ _ _ _ _ _).
    { pm_reflexivity. }
    { tc_solve. }
    { tc_solve. }
    pm_reduce; notypeclasses refine (conj _ _);
    [|
      notypeclasses refine (tac_apply _ (IAnon 2) _ _ _ _ _ _ _); [pm_reflexivity
      |tc_solve
      |pm_reduce]
    ]. *)
    
    - (* Box *)
      iModIntro.

      (* Relation *)
      try iApply (iProper (_ ==> bi_wand) bi_exist).

      (* Pointwise *)
      iIntros "%".

      (* Relation *)
      try iApply (iProper (_ ==> bi_wand) bi_exist).

      (* Pointwise *)
      iIntros "%".

      (* Relation *)
      try iApply (iProper (_ ==> bi_wand) bi_exist).

      (* Pointwise *)
      iIntros "%".

      (* Relation *)
      try iApply (iProper (_ ==> bi_wand) bi_exist).

      (* Pointwise *)
      iIntros "%".

      (* Relation *)
      try iApply (iProper (_ ==> _ ==> bi_wand) bi_sep).

      + (* Assumption *)
        iIntros "?".
        iAssumption.

      + (* Relation *)
        try iApply (iProper (_ ==> _ ==> bi_wand) bi_sep).

        * (* Assumption *) iAssumption.

        * (* Assumption *)
          iIntros "?".
          iAssumption.

    - (* Box *)
      iModIntro.

      (* Assumption *)
      iIntros "?".
      iAssumption.
  Qed.

  EI.ind 
  Inductive is_P_list : (val → iProp) → val → iProp :=
    | empty_is_P_list P : is_P_list P NONEV
    | cons_is_P_list P l v tl : l ↦ (v,tl) -∗ P v -∗ is_P_list P tl -∗ is_P_list P (SOMEV #l).

  Print is_P_list_pre.
  Print is_P_list_proper.

  Local Lemma is_P_list_pre_proper_mono :
    is_P_list_proper is_P_list_pre.
  Proof.
    (* elpi IProper_solver. *)
    (* Start proof *)
    unfold is_P_list_proper, IProper.

    (* Respectfull *)
    iIntros "% % #?".

    (* Pointwise *)
    iIntros "%".

    (* Pointwise *)
    iIntros "%".

    (* Relation *)
    try iApply (iProper (□> .> .> bi_wand ==> .> .> bi_wand) is_P_list_pre).
    unfold is_P_list_pre.

    (* Relation *)
    iApply (iProper (_ ==> _ ==> bi_wand) bi_or).
    
    - (* Box *)
      iModIntro.

      (* Relation *)
      try iApply (iProper (_ ==> bi_wand) bi_exist).

      (* Pointwise *)
      iIntros "%".

      (* Relation *)
      try iApply (iProper (_ ==> bi_wand) bi_exist).

      (* Pointwise *)
      iIntros "%".

      (* Relation *)
      try iApply (iProper (_ ==> bi_wand) bi_exist).

      (* Pointwise *)
      iIntros "%".

      (* Relation *)
      try iApply (iProper (_ ==> bi_wand) bi_exist).

      (* Pointwise *)
      iIntros "%".

      (* Relation *)
      try iApply (iProper (_ ==> _ ==> bi_wand) bi_sep).

      + (* Assumption *)
        iIntros "?".
        iAssumption.

      + (* Relation *)
        try iApply (iProper (_ ==> _ ==> bi_wand) bi_sep).

        * (* Assumption *)iIntros "?". iAssumption.

        * (* Relation *)
          try iApply (iProper (_ ==> _ ==> bi_wand) bi_sep).
          
          -- iAssumption.
          --(* Assumption *)
            iIntros "?".
            iAssumption.

    - (* Box *)
      iModIntro.

      (* Assumption *)
      iIntros "?".
      iAssumption.
  Qed.
End Tests.
