From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.
From eIris.algebra Require Import OFE.

Record chain {T : OFE.type} := {
  chain_car :> nat -> T;
  chain_cauchy : forall n m, n <= m -> equ n (chain_car m) (chain_car n);
}.

HB.mixin Record COFE_of_OFE T of OFE T := {
    lim : forall c : chain, T;
    limCOMPL : forall n c, equ n (lim c) (c n);
}.
