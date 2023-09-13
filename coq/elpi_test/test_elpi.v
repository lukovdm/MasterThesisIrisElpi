From elpi Require Import elpi.
From iris.proofmode Require Export tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.heap_lang Require Import proofmode.

Elpi Program tutorial lp:{{ }}.
Elpi Accumulate File "coq/elpi_test/stdpp.elpi".
Elpi Query lp:{{
    list->listterm [{{ INamed "a" }}, {{ INamed "b" }}] LT,
    L = {{ [INamed "a"; INamed "b"] }},
    std.assert! (L = LT) "list->listterm doesn't work".
}}.
