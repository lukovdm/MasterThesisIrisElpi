From elpi Require Import elpi.

Elpi Tactic show.
Elpi Accumulate lp:{{

  solve (goal Ctx _Trigger Type Proof _) _ :-
    coq.say "Goal:" Ctx "|-" Proof ":" Type.

}}.
Elpi Typecheck.

Elpi Tactic blind.
Elpi Accumulate lp:{{
  solve (goal _ Trigger _ _ _) [] :- Trigger = {{0}}.
  solve (goal _ Trigger _ _ _) [] :- Trigger = {{I}}.
}}.
Elpi Typecheck.

About conj. (* remak the implicit arguments *)

Elpi Tactic split.
Elpi Accumulate lp:{{
  solve (goal _ _ {{ _ /\ _ }} _ _ as G) GL :- !,
    % conj has 4 arguments, but two are implicits
    % (_ are added for them and are inferred from the goal)
    refine {{ conj _ _ }} G GL.

  solve _ _ :-
    % This signals a failure in the Ltac model. A failure
    % in Elpi, that is no more cluases to try, is a fatal
    % error that cannot be catch by Ltac combinators like repeat.
    coq.ltac.fail _ "not a conjunction".
}}.
Elpi Typecheck.

Lemma test_split : exists t : Prop, True /\ True /\ t.
Proof.
eexists.
repeat elpi split. (* The failure is catched by Ltac's repeat *)
(* Remark that the last goal is left untouched, since
   it did not match the pattern {{ _ /\ _ }}. *)
all: elpi blind.
Show Proof.
Qed.
