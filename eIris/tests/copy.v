From elpi Require Import elpi.

Elpi Command test. 
Elpi Trace Browser.
Elpi Accumulate lp:{{
    pred not2 i:prop.
    not2 P :- P, !, fail.
    not2 _ :- true.

    pred foo.
    foo :- not (true).
    foo :- true.
}}.
Elpi Query lp:{{
    T = {{ fun (n: nat) => n + 1 }},
    T = fun _ _ F,
    pi x\ F x = app [_, _, P]
}}.