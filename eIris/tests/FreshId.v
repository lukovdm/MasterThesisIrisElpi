From elpi Require Import elpi.

Lemma lem (P : Prop) : (forall x, x = 10) -> P.
Proof.
Admitted.

Elpi Tactic fresh1.
Elpi Accumulate lp:{{
  solve (goal _ _ Type _ _ as G) GL :-
    P = {{ lem _ _ }},
    coq.elaborate-skeleton P Type P' ok,
    P' = {{ lem _ lp:IP }},
    coq.typecheck IP IPT ok,
    IPT = (prod N' Ty _),
    coq.name->id N' S,
    coq.ltac.fresh-id S Ty ID,
    coq.id->name ID N,
    IP = (fun N _ _),
    refine P' G GL.
}}.
Elpi Typecheck.

Goal forall x z y, x = 1 + y + z.
intros x x0.
Elpi Trace Browser.
elpi fresh1.
Abort.