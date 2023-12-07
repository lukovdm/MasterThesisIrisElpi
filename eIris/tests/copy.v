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
    T = {{ forall (n: nat), n + 1 }}.
}}.