From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.
From eIris.algebra Require Import OFE.
From eIris.algebra Require Import RA.

(* TODO: Somehow use ofe for equivalence in the assoc, etc rules *)
HB.mixin Record CAMERA_of_OFE_and_RA M of OFE M & RA M := {
  validN : nat -> M -> Prop;
  lteN : nat -> M -> M -> Prop;
  lteNDEF : forall n a b, lteN n a b <-> exists c, b ≡{n}≡ a ⋅ c;

  (* TODO: validNE : non_expansive valid; *)
  opNE : non_expansive (@op M);
  coreNE : non_expansive (@core M);
  
  EXTEND n (a b1 b2 : M) : 
    validN n a -> a ≡{n}≡ b1 ⋅ b2 -> 
      exists c1 c2, a = c1 ⋅ c2 /\ c1 ≡{n}≡ b1 /\ c2 ≡{n}≡ b2;
  validNOP : forall n a b, validN n (a ⋅ b) -> validN n a;
  validLIMIT a : ✓ a <-> forall n, validN n a;
}.
HB.structure Definition CAMERA := { M of OFE M & RA M & CAMERA_of_OFE_and_RA M }.

(* TODO: make instance of CAMERA, start with N *)
(* TODO: Look at instace of excl, option, gmap *)

Notation "x ≼{ n } y" := (lteN n x y) (at level 70, n at next level, format "x  ≼{ n }  y").
Global Hint Extern 0 (_ ≼{_} _) => reflexivity : core.
Notation "✓{ n } x" := (validN n x) (at level 20, n at next level, format "✓{ n }  x").

(* 
HB.factory Record CAMERA_of_TYPE M := {
  core : M -> option M;
  op : M -> M -> M;
  lte : M -> M -> Prop;
  validN : nat -> M -> Prop;

  (* TODO: validNE : non_expansive valid; *)
  opNE : non_expansive (@op M);
  coreNE : non_expansive (@core M);

  lteDEF : forall a b, lte a b <-> exists c, b = op a c;
  
  opA : associative op;
  opC : commutative op;

  coreID : forall a a', core a = Some a' -> op a' a = a;
  coreIDEM : forall a a', core a = Some a' -> core a' = Some a';
  coreMONO : forall a b a', core a = Some a' -> lte a' b -> 
      (exists b', core b = Some b' /\ lte a' b')
    ;

  EXTEND n (a b1 b2 : M) : 
    validN n a -> a ≡{n}≡ b1 ⋅ b2 -> 
      exists c1 c2, a = c1 ⋅ c2 /\ c1 ≡{n}≡ b1 /\ c2 ≡{n}≡ b2;
  validNOP : forall n a b, validN n (op a b) -> validN n a;
  validLIMIT a : valid a <-> forall n, validN n a;
  
}. *)

Section NatCAMERA.
  Definition nat_validN (n x : nat) := valid x.
  Definition nat_lteN (n x y : nat) := lte x y.

  Fact nat_opNE : non_expansive (@op nat).
  Proof.
    intros n x y H. 
    unfold equ; simpl; unfold arrow_equ. 
    intros.
    unfold equ in *; simpl in *; unfold nat_equ in *.
    by subst.
  Qed.

  Fact nat_coreNE : non_expansive (@core nat).
  Proof. done. Qed.

  Fact nat_lteNDEF (n a b : nat) : nat_lteN n a b <-> exists c, b ≡{n}≡ a ⋅ c.
  Proof.
    unfold nat_lteN; simpl.
    apply nat_lteDEF.
  Qed.

  Fact nat_EXTEND n (a b1 b2 : nat) : 
    nat_validN n a -> a ≡{n}≡ b1 ⋅ b2 -> 
      exists c1 c2, a = c1 ⋅ c2 /\ c1 ≡{n}≡ b1 /\ c2 ≡{n}≡ b2.
  Proof.
    intros H1 H2.
    by exists b1, b2.
  Qed.

  Fact nat_validNOP n a b : nat_validN n (a ⋅ b) -> nat_validN n a.
  Proof. done. Qed.

  Fact nat_validLIMIT a : ✓ a <-> forall n, nat_validN n a.
  Proof. done. Qed.

  HB.instance Definition _ := CAMERA_of_OFE_and_RA.Build nat nat_validN nat_lteN 
    nat_lteNDEF nat_opNE nat_coreNE nat_EXTEND nat_validNOP nat_validLIMIT.

End NatCAMERA.

