From elpi Require Import elpi.
From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.bi Require Import fixpoint.
From iris.algebra Require Import ofe monoid list.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation.
From stdpp Require Import base finite.

From eIris.proofmode Require Import proper.
From eIris.proofmode Require Import intros.

Context `{!heapGS Σ}.
Notation iProp := (iProp Σ).

Elpi Command PrintCommand.
Elpi Accumulate lp:{{

  % main is, well, the entry point
  main Arguments :- coq.say "PrintCommand" Arguments.

}}.
Elpi Typecheck.

Elpi Export PrintCommand.

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
    std.fold2 LS TS { last-rec-to-and.aux L T } (l\ t\ a\ r\ sigma TMP\ last-rec-to-and.aux l t TMP, r = {{ (lp:a ∗ lp:TMP)%I }}) TS'.

  pred top-wand-to-sepand i:term, o:term.
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
        top-wand-to-sepand TMP2 r)
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

Section Tests.
  Implicit Types l : loc.

  EI.ind 
  Inductive is_list : val → list val → iProp :=
    | empty_is_list : is_list NONEV []
    | cons_is_list l v vs tl : (l ↦ (v,tl) -∗ is_list tl vs -∗ is_list (SOMEV #l) (v :: vs))%I.

  Print is_list_pre.
  Print is_list_proper.

  Elpi Trace Browser.
  Local Lemma is_list_pre_proper_mono :
    IProper (□> .> .> bi_wand ==> .> .> bi_wand) is_list_pre.
  Proof.
    rewrite /is_list_pre.
    unfold IProper, iPointwise_relation, iPersistant_relation, iRespectful.
    iIntros.
    iIntros (Φ Ψ) "#H %hd %vs [ [%l [%v [%vs' [%tl (Hl & Hx & Hhd & Hvs)]]]] | [Hhd Hvs] ]".
    - iLeft.
      iExists l, v, vs', tl.
      iFrame.
      by iApply "H".
    - iRight.
      by iFrame.
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
