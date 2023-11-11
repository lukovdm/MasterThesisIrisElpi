From elpi Require Import elpi.
From iris.proofmode Require Import base environments proofmode tactics coq_tactics reduction intro_patterns class_instances spec_patterns.
From iris.prelude Require Import options.
From iris.bi Require Import  bi telescopes fixpoint.
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

#[arguments(raw)] Elpi Command EI.ind.
Elpi Accumulate lp:{{
  pred print-contructors i:list indc-decl.
  print-contructors [].
  print-contructors [constructor Name Arity | CS] :-
    coq.say Name "of type" { coq.term->string { coq.arity->term Arity } },
    print-contructors CS.

  pred constructor->term i:indc-decl, o:term.
  constructor->term (constructor _ Arity) T :- coq.arity->term Arity T.

  pred find-PROP i:term, o:term.
  find-PROP (prod _ _ F) O :- !,
    (pi x\ find-PROP (F x) O).
  find-PROP O O :- !.

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
    find-PROP TypeTerm PROP,
    constr-body-disj Constructors ConstrBo,
    (pi b\ (type-to-fun PROP b :- !) => type-to-fun TypeTerm (FunTerm b)), % TODO: A proper PROP should be added not the hacky heap-lang one
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
    find-PROP Type PROP,
    coq.say Type,
    (pi N T F A T1 F1 A1 \ fold-map (prod N T F) A (prod N T1 F1) (some {{ (.> lp:A1)%i_signature }}) :-
          fold-map T A T1 _, !, (pi x\ fold-map (F x) A (F1 x) (some A1))) =>
      (pi A \ fold-map PROP A PROP (some {{ bi_wand }}) :- !) =>
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

  kind hole type.
  type hole term -> term -> hole. % A pair of of Type, Proof

  kind ihole type.
  type ihole term -> hole -> ihole. % the anonymous iris hyp counter and the hole

  pred ihole->string i:ihole, o:string.
  ihole->string (ihole N (hole T P)) S :-
    S is {coq.term->string N} ^ " ⊢ " ^ {coq.term->string P} ^ " : \n" ^ {coq.term->string T}.

  pred increase-ctx-count i:term, o:term.
  increase-ctx-count N NS :-
    coq.reduction.vm.norm {{ Pos.succ lp:N }} _ NS.

  pred get-ctx-count i:term, o:term.
  get-ctx-count {{ envs_entails (Envs _ _ lp:N) _ }} N.
  get-ctx-count T _ :-
    coq.error "get-ctx-count: type not of shape envs entails: " T.

  pred set-ctx-count i:term, i:term, o:term.
  set-ctx-count 
    {{ @envs_entails lp:PROP (@Envs lp:PROPE lp:EI lp:ES _) lp:P }}
    NS
    {{ @envs_entails lp:PROP (@Envs lp:PROPE lp:EI lp:ES lp:NS) lp:P }}.
  set-ctx-count T N _ :-
    coq.error "set-ctx-count: type not of shape envs entails: " N T.

  pred addN i:term, i:open-tactic, i:goal, o:list sealed-goal.
  addN N T (goal Ctx Trigger Type Proof Args) GL :-
    pm-reduce Type Type',
    set-ctx-count Type' N NType,
    T (goal Ctx Trigger NType Proof Args) GL.

  pred pm-reduce i:term, o:term.
  pm-reduce T O :-
    Consts = [
      % base
      {{ @base.negb }}, {{ @base.beq }}, {{ @base.Pos_succ }}, {{ @base.ascii_beq }}, {{ @base.string_beq }}, {{ @base.positive_beq }}, {{ @base.ident_beq }},
      % environments
      {{ @env_lookup }}, {{ @env_lookup_delete }}, {{ @env_delete }}, {{ @env_app }}, {{ @env_replace }}, {{ @env_dom }}, {{ @env_intuitionistic }}, 
      {{ @env_spatial }}, {{ @env_counter }}, {{ @env_spatial_is_nil }}, {{ @envs_dom }}, {{ @envs_lookup }}, {{ @envs_lookup_delete }}, 
      {{ @envs_delete }}, {{ @envs_snoc }}, {{ @envs_app }}, {{ @envs_simple_replace }}, {{ @envs_replace }}, {{ @envs_split }}, 
      {{ @envs_clear_spatial }}, {{ @envs_clear_intuitionistic }}, {{ @envs_incr_counter }}, {{ @envs_split_go }}, 
      {{ @envs_split }}, {{ @env_to_prop_go }}, {{ @env_to_prop }}, {{ @env_to_prop_and_go }}, {{ @env_to_prop_and }},
      % PM list and option functions
      {{ @pm_app }}, {{ @pm_option_bind }}, {{ @pm_from_option }}, {{ @pm_option_fun }}
    ],
    std.map Consts (x\r\ sigma TMP\ x = global (const TMP), r = coq.redflags.const TMP) Deltas,
    coq.redflags.add coq.redflags.betaiotazeta Deltas RF,
    @redflags! RF => coq.reduction.cbv.norm T O.

  pred do-iStartProof i:hole, o:ihole.
  do-iStartProof (hole {{ let _ := _ in _ }} _) _ :- !,
    coq.error "iStartProof: goal is a `let`, use `simpl`, `intros x`, `iIntros (x)`, or `iIntros ""%x""".
  do-iStartProof (hole Type Proof) (ihole N (hole NType NProof)) :- 
    coq.elaborate-skeleton {{ as_emp_valid_2 lp:Type _ (tac_start _ _) }} Type Proof ok,
    Proof = {{ as_emp_valid_2 _ _ (tac_start _ lp:NProof) }},
    coq.typecheck NProof NType ok,
    NType = {{ envs_entails (Envs _ _ lp:N) _}}.

  pred do-iModIntro i:hole, o:hole.
  do-iModIntro (hole Type Proof) (hole ModType ModProof) :-
    @no-tc! => coq.elaborate-skeleton {{ tac_modal_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ }} Type Proof ok,
    Proof = {{ tac_modal_intro _ _ _ _ _ _ _ _ _ _ _ lp:TC1 lp:TC2 lp:TC3 lp:PM4 lp:SC5 lp:ModProof }},
    coq.ltac.collect-goals TC1 [G1] _,
    open tc_solve G1 [],
    coq.ltac.collect-goals TC2 [G2] _,
    open tc_solve G2 [],
    coq.ltac.collect-goals TC3 [G3] _,
    open tc_solve G3 [],
    coq.ltac.collect-goals PM4 [G4] _,
    open pm_reduce G4 [G4'],
    open tc_solve G4' [],
    coq.ltac.collect-goals SC5 [G5] _,
    open (coq.ltac.call "iSolveSideCondition" []) G5 [],
    coq.typecheck ModProof ModType ok.

  pred do-iPoseProper i:ihole, i:term, i:term, o:ident, o:ihole.
  do-iPoseProper (ihole N (hole Type Proof)) R F (iAnon N) (ihole NS (hole PosedType PosedProof)) :-
    increase-ctx-count N NS,
    ident->term (iAnon N) _ NT,
    @no-tc! => coq.elaborate-skeleton 
                  {{ tac_pose_proof _ lp:NT _ _ (into_emp_valid_proj _ _ _ (iproper_top_to_iproper _ _ _ _ _ (_ : IProperTop lp:R lp:F _))) _}} 
                  Type Proof ok,
    Proof = {{ tac_pose_proof _ _ _ _ (into_emp_valid_proj _ _ lp:IEVProof (iproper_top_to_iproper _ _ _ _ _ (lp:IPTProof : IProperTop _ _ _))) lp:PosedProof }},
    coq.ltac.collect-goals IEVProof [G1] _,
    open (coq.ltac.call "iIntoEmpValid" []) G1 TCGL,
    all (open tc_solve) TCGL [],
    coq.ltac.collect-goals IPTProof [G2] _,
    open tc_solve G2 [],
    coq.typecheck PosedProof NormType ok,
    pm-reduce NormType PosedType.

  pred go_iSpecializeWand i:ihole, i:ident, o:ihole, o:ihole.
  go_iSpecializeWand (ihole N (hole Type Proof)) ID 
    (ihole N (hole LType LProof)) (ihole N (hole RType RProof)) :-
      ident->term ID _IDS IDT,
      @no-tc! => coq.elaborate-skeleton {{ tac_specialize_assert_no_am _ lp:IDT _ false [] _ _ _ _ _ _ _ _ _}} 
                  Type Proof ok,
      Proof = {{ tac_specialize_assert_no_am _ _ _ _ _ _ _ _ _ _ lp:RefP lp:TC1P lp:TC2P lp:ConjP}},
      coq.ltac.collect-goals RefP [G1] _,
      open pm_reflexivity G1 [],
      coq.ltac.collect-goals TC1P [G2] _,
      open tc_solve G2 [],
      coq.ltac.collect-goals TC2P [G3] _,
      open tc_solve G3 [],
      coq.typecheck ConjP RedType ok,
      pm-reduce RedType ConjType,
      coq.elaborate-skeleton {{ conj _ _ }} ConjType ConjP ok,
      ConjP = {{ conj lp:LProof lp:RProof }},
      coq.typecheck LProof LType' ok,
      pm-reduce LType' LType,
      coq.typecheck RProof RType' ok,
      pm-reduce RType' RType.

  pred do-iApplySimpleHyp i:ihole, i:ident, o:ihole.
  do-iApplySimpleHyp (ihole N (hole Type Proof)) ID (ihole N (hole ApType ApProof)) :-
    ident->term ID _IDS IDT,
    @no-tc! => coq.elaborate-skeleton {{ tac_apply _ lp:IDT _ _ _ _ _ _ _ }} Type Proof ok,
    Proof = {{ tac_apply _ _ _ _ _ _ lp:RefProof lp:TCProof lp:ApProof }},
    coq.ltac.collect-goals RefProof [G1] _,
    open pm_reflexivity G1 [],
    coq.ltac.collect-goals TCProof [G2] _,
    open tc_solve G2 [],
    coq.typecheck ApProof RedType ok,
    pm-reduce RedType ApType.

  pred do-iApplyProper i:ihole, i:term, i:term, o:list ihole.
  do-iApplyProper IH R F IHS :-
    coq.say "do-iApplyProper",
    do-iPoseProper IH R F ID IHPosed,
    coq.say "Posed Lemma" {ihole->string IHPosed},
    do-iApplyProper.aux IHPosed ID IHS.
  do-iApplyProper.aux IH ID [IH'] :- 
    coq.say "simpleApplyHyp",
    do-iApplySimpleHyp IH ID IH'.
  do-iApplyProper.aux IH ID [IHL | IHS] :-
    coq.say "specialize",
    go_iSpecializeWand IH ID IHL IHR,
    do-iApplyProper.aux IHR ID IHS.

  pred unfold-id i:string, i:term, o:term.
  unfold-id S I O :- 
    coq.locate S (const IP),
    unfold-gref (const IP) I O.

  pred unfold-gref i:gref, i:term, o:term.
  unfold-gref (const IP) I O :-
    coq.env.const IP (some Bo) _,
    ((copy (global (const IP)) Bo :- !) => copy I I'),
    coq.reduction.lazy.bi-norm I' O.

  pred do-steps i:ihole.
  do-steps (ihole _ (hole Type _) as IH) :-
    coq.say "\n================= Goal =================" {ihole->string IH} "",
    do-steps.conn Type R LF RF,
    do-steps.do IH R LF RF.

  pred do-steps.open i:goal, o:list sealed-goal.
  do-steps.open (goal _ _ Type Proof _) _ :-
    pm-reduce Type Type',
    get-ctx-count Type' N,
    do-steps (ihole N (hole Type' Proof)).

  pred do-steps.conn i:term, o:term, o:term, o:term.
  do-steps.conn Type R LF RF:-
    top-relation Type R, !,
    relation-on Type LF RF.

  pred top-relation i:term, o:term.
  top-relation {{ envs_entails _ lp:{{ app PS }} }} C :- C = app {std.take 2 PS}.

  pred relation-on i:term, o:term, o:term.
  relation-on {{ envs_entails _ lp:{{ app AS }} }} L R :- 
    std.take-last 2 AS [L, R].

  pred do-steps.do i:ihole, i:term, i:term, i:term.
  do-steps.do (ihole N (hole _ Proof)) {{ @iRespectful _ }} _ _ :- !,
    coq.say "==>",
    list->listterm [ {{ IPure (IGallinaAnon) }}, {{ IPure (IGallinaAnon) }}, {{ IIntuitionistic (IFresh) }} ] Args,
    coq.ltac.collect-goals Proof [G] _,
    open (addN N (coq.ltac.call "_iIntros0" [ trm Args ])) G [GIntro], !,
    open do-steps.open GIntro _.
  do-steps.do (ihole N (hole _ Proof)) {{ @iPointwise_relation _ }} _ _ :- !,
    coq.say ".>",
    list->listterm [ {{ IPure (IGallinaAnon) }} ] Args,
    coq.ltac.collect-goals Proof [G] _,
    open (addN N (coq.ltac.call "_iIntros0" [ trm Args ])) G [GIntro], !,
    open do-steps.open GIntro _.
  do-steps.do (ihole N H) {{ @iPersistent_relation _ }} _ _ :- !,
    coq.say "□>",
    do-iModIntro H ModH, !,
    do-steps (ihole N ModH).
  do-steps.do (ihole N (hole _ Proof)) _ _ _ :-
    coq.say "Applying assumption" {coq.term->string F},
    list->listterm [ {{ IDone }} ] Args,
    coq.ltac.collect-goals Proof [G] _,
    open (coq.ltac.call "_iIntros0" [ trm Args ]) G []. %Should have an addN but crashes for some reason
  do-steps.do (ihole N (hole _ Proof)) _ F F :-
    coq.say "Applying assumption" {coq.term->string F},
    list->listterm [ {{ IFresh }}, {{ IDone }} ] Args,
    coq.ltac.collect-goals Proof [G] _,
    open (coq.ltac.call "_iIntros0" [ trm Args ]) G []. %Should have an addN but crashes for some reason
  do-steps.do IH R (app [F | FS]) _ :- 
    std.exists { std.iota {calc ({std.length FS} + 1) } } (n\ std.take n FS FS'),
    coq.say "Apply relation" {coq.term->string R} "with" {coq.term->string (app [F | FS'])},
    do-iApplyProper IH R (app [F | FS']) HS, !,
    std.map HS (x\r\ do-steps x) _.
  do-steps.do (ihole N (hole Type Proof)) _ (app [global (const F) | _ ]) _ :-
    coq.say "Unfolding" F,
    unfold-gref (const F) Type UnfoldedType, !,
    do-steps (ihole N (hole UnfoldedType Proof)).
  do-steps.do (ihole N (hole Type Proof)) _ (global (const F)) _ :-
    coq.say "Unfolding" F,
    unfold-gref (const F) Type UnfoldedType, !,
    do-steps (ihole N (hole UnfoldedType Proof)).
  do-steps.do _ T F _ :- !,
    coq.say "No case for relation" {coq.term->string T} "with " {coq.term->string F} "😢 stopping".

  solve (goal _Ctx _Trigger Type Proof []) _ :- 
    unfold-id "is_list_proper" Type UnfoldedType,
    unfold-id "IProper" UnfoldedType UnfoldedType',
    coq.typecheck Proof UnfoldedType' ok,
    do-iStartProof (hole UnfoldedType' Proof) IH,
    do-steps IH.
}}.
Elpi Typecheck.
Elpi Export IProper_solver.

Section Tests.
  Context `{!heapGS Σ}.
  Notation iProp := (iProp Σ).
  Implicit Types l : loc.

  EI.ind 
  Inductive is_list : val → list val → iProp :=
    | empty_is_list : is_list NONEV []
    | cons_is_list l v vs tl : l ↦ (v,tl) -∗ is_list tl vs -∗ is_list (SOMEV #l) (v :: vs).

  (* Print is_list_pre.
  Print is_list_proper. *)

  (* Elpi Trace Browser. *)
  Local Lemma is_list_pre_proper_mono :
    is_list_proper is_list_pre.
  Proof.
    elpi IProper_solver.
    Show Proof.
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
    elpi IProper_solver.
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
