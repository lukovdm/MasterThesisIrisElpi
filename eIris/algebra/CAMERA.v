From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.
From eIris.algebra Require Import OFE.
From eIris.algebra Require Import RA.

(* Somehow use ofe for equivalence in the assoc, etc rules *)
HB.mixin Record CAMERA_of_OFE_and_RA M of OFE M & RA M := {
  validN : nat -> M -> Prop;
  (*  validNE : non_expansive valid; *)
  opNE : non_expansive (@op M);
  coreNE : non_expansive (@core M);
  lteN : nat -> M -> M -> Prop;
  lteNDEF : forall a b n, lteN n a b <-> exists c, b ≡{n}≡ a ⋅ c;
  EXTEND n (a b1 b2 : M) : 
    validN n a -> a ≡{n}≡ b1 ⋅ b2 -> 
      exists c1 c2, a = c1 ⋅ c2 /\ c1 ≡{n}≡ b1 /\ c2 ≡{n}≡ b2;
  validNOP : forall n a b, validN n (op a b) -> validN n a;
  validLIMIT a : valid a <-> forall n, validN n a;
}.
HB.structure Definition CAMERA_OR := { M of OFE M & RA M & CAMERA_of_OFE_and_RA M }.

(* make instance of CAMERA, start with N *)
(* Look at instace of excl, option, gmap *)

Notation "x ≼{ n } y" := (lteN n x y) (at level 70, n at next level, format "x  ≼{ n }  y").
Global Hint Extern 0 (_ ≼{_} _) => reflexivity : core.
Notation "✓{ n } x" := (validN n x) (at level 20, n at next level, format "✓{ n }  x").