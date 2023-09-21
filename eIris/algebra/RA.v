From stdpp Require Import finite.
From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.
Require Import Lia.

From eIris Require Import EQU.

HB.mixin Record RA_of_TYPE M of EQUIV M := {
  valid : M -> Prop;
  core : M -> option M;
  op : M -> M -> M;
  lte : M -> M -> Prop;
  lteDEF a b : lte a b <-> exists c, b = op a c;
  opA : Assoc (≡🪥@{M}) op;
  opC : Comm (≡🪥@{M}) op;
  coreID a a' : core a = Some a' -> op a' a = a;
  coreIDEM a a' : core a = Some a' -> core a' = Some a';
  coreMONO a b a' : core a = Some a' -> lte a' b -> 
    (exists b', core b = Some b' /\ lte a' b');
  validOP a b : valid (op a b) -> valid a;
}.
HB.structure Definition RA := { M of RA_of_TYPE M }.

Infix "⋅" := op (at level 50, left associativity).
Notation "✓ x" := (valid x) (at level 20).

(* TODO: How to make multiple instances of the same type with different op, ex. nat +, nat max*)

Section NatRA.

  Definition nat_valid (n : nat) := True.
  Definition nat_core (n : nat) := Some 0.

  Local Notation "✓N x" := (nat_valid x) (at level 20).

  Fact nat_lteDEF a b : a <= b <-> exists c, b = a + c.
  Proof.
    split; intros.
      - exists (b - a). lia.
      - destruct H. lia.
  Qed.

  Fact nat_opA : Assoc (=) plus.
  Proof. unfold Assoc. intros. lia. Qed.

  Fact nat_opC : Comm (=) plus.
  Proof. unfold Comm. intros. lia. Qed.

  Fact nat_coreID a a' : nat_core a = Some a' -> a' + a = a.
  Proof. unfold nat_core. intros. inversion H. lia. Qed.
    
  Fact nat_coreIDEM a a' : nat_core a = Some a' -> nat_core a' = Some a'.
  Proof. done. Qed.

  Fact nat_coreMONO a b a' : nat_core a = Some a' -> a' <= b -> 
    (exists b', nat_core b = Some b' /\ a' <= b').
  Proof. unfold nat_core. intros. injection H. intros. subst. by exists 0. Qed.
    
  Fact nat_validOP a b : ✓N (a + b) -> ✓N a.
  Proof. done. Qed.
  
  HB.instance Definition _ := RA_of_TYPE.Build nat nat_valid nat_core plus le 
    nat_lteDEF nat_opA nat_opC nat_coreID nat_coreIDEM nat_coreMONO nat_validOP.

End NatRA.

