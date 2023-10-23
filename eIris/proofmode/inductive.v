From elpi Require Import elpi.
From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.bi Require Import fixpoint.
From iris.algebra Require Import ofe monoid list.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation.
From stdpp Require Import base finite.

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

  % main is, well, the entry point
  main [indt-decl (inductive Name _In-Or-Co Arity Constructors)] :- 
    coq.say "------ Creating inductive" Name,
    coq.arity->term Arity TypeTerm,
    coq.say "------ With type" { coq.term->string TypeTerm },
    (pi x\ print-contructors (Constructors x)),
    (pi f\ std.map (Constructors f)
      (x\ r\ sigma TMP1 TMP2\ 
        constructor->term x TMP1, 
        init-prod-to-bi-exist TMP1 TMP2, 
        top-wand-to-sepand TMP2 r)
      (ConstrBiTerms f)),
    (pi f\ coq.say "------ Constructor Bi Terms" {std.map (ConstrBiTerms f) coq.term->string} (ConstrBiTerms f)),
    (pi f\ std.fold 
      { std.drop-last 1 (ConstrBiTerms f) } 
      { std.last (ConstrBiTerms f) }
      (x\ a\ r\ r = {{ bi_or lp:a lp:x }}) 
      (ConstrBo f)),
    coq.say "------ Constructor body disjunction" {coq.term->string (ConstrBo {{ True }})} ConstrBo,
    (pi b\ (type-to-fun ({{ uPred (iResUR Σ) }}) b :- !) => type-to-fun TypeTerm (FunTerm b)), % TODO: A proper PROP should be added not the hacky heap-lang one
    (pi b\
      (pi N T T1 F F1 A \ fold-map (fun N T F) A (fun N T1 F1) A :- !,
                                  fold-map T A T1 _, pi x\ fold-map (F x) [x | A] (F1 x) _) =>
      (pi L L' F B \ fold-map b L B L :- !, std.rev L [F | L'], last-rec-to-and F L' (ConstrBo F) B) =>
          fold-map {{fun F : lp:TypeTerm => lp:{{ FunTerm b }} }} [] Bo _),
    coq.say "------- Body" { coq.term->string Bo } Bo,
    Ty = {{ lp:TypeTerm -> lp:TypeTerm }}, !,
    @keepunivs! => std.assert-ok! (coq.elaborate-skeleton Bo Ty EBo) "Type check failed",
    coq.env.add-const {calc (Name ^ "_pre")} EBo Ty ff C,
    coq.say "const" C.
}}.
Elpi Typecheck.

Elpi Export EI.ind.

Section Tests.
  Implicit Types l : loc.

  Elpi Trace Browser.

  EI.ind 
  Inductive is_list : val → list val → iProp :=
    | empty_is_list : is_list NONEV []
    | cons_is_list l v vs tl : (l ↦ (v,tl) -∗ is_list tl vs -∗ is_list (SOMEV #l) (v :: vs))%I.

  Print is_list_pre.

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
