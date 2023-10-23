From elpi Require Import elpi.

#[arguments(raw)] Elpi Command PrintCommand.
Elpi Accumulate lp:{{

  % main is, well, the entry point
  main Arguments :- coq.say "PrintCommand" Arguments.

}}.
Elpi Typecheck.
Elpi Export PrintCommand.

Definition siProp := nat -> Prop.

Definition f : siProp -> siProp.
Admitted.

Declare Scope siPropScope.
Delimit Scope siPropScope with S.
Bind Scope siPropScope with siProp.

About f.

Notation "'bar'" := (fun _ n => True) : core .
Notation "'bar'" := (f) : siPropScope .

Local Open Scope core.

PrintCommand
Inductive foo : siProp :=
    | test : bar foo.
