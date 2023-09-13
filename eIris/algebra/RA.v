From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record RA_of_TYPE M := {
  valid : M -> Prop;
  core : M -> option M;
  op : M -> M -> M;
  lte : M -> M -> Prop;
  lteDEF : forall a b, lte a b <-> exists c, b = op a c;
  opA : associative op;
  opC : commutative op;
  coreID : forall a a', core a = Some a' -> op a' a = a;
  coreIDEM : forall a a', core a = Some a' -> core a' = Some a';
  coreMONO : forall a b a', core a = Some a' -> lte a' b -> 
      (exists b', core b = Some b' /\ lte a' b')
    ;
  validOP : forall a b, valid (op a b) -> valid a;
}.
HB.structure Definition RA := { M of RA_of_TYPE M }.

Infix "⋅" := op (at level 50, left associativity).
Notation "✓ x" := (valid x) (at level 20).

(* TODO: How to make multiple instances of the same type with different op, ex. nat +, nat max*)

