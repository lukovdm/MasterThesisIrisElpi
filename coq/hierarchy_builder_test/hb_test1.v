From Coq Require Import ssreflect ssrfun Relations.
From HB Require Import structures.

HB.mixin Record RA_of_TYPE M := {
  valid : M -> Prop;
  core : M -> option M;
  opp : M -> M -> M;
  lte : M -> M -> Prop;
  lteINCL : forall a b, exists c, b = opp a c;
  oppA : associative opp;
  oppC : commutative opp;
  coreID : forall a, (exists a', core a = Some a' /\ opp a' a = a);
  coreIDEM : forall a, (exists a', core a = Some a' /\ core a' = Some a');
  coreMONO : forall a b, 
    (exists a', core a = Some a' /\ lte a' b -> 
      (exists b', core b = Some b' /\ lte a' b')
    );
  validOPP : forall a b, valid (opp a b) -> valid a;
}.
HB.structure Definition RA := { M of RA_of_TYPE M }.

(* This does not work with the error, (equ n) is not a Type, but I don't know why *)
(*
HB.mixin Record OFE_of_TYPE T := {
  equ : nat -> T -> T -> Prop;
  equREFL : forall n, reflexive (equ n);
  equTRANS : forall n, transitive (equ n);
  equSYMM : forall n, symmetric (equ n);
  equMONO : forall n m, n >= m -> inclusion (equ n) (equ m);
}. *)

HB.mixin Record OFE_of_TYPE T := {
  equ : nat -> T -> T -> Prop;
  equREFL : forall n x, equ n x x;
  equTRANS : forall n x y z, equ n x y -> equ n y z -> equ n x z;
  equSYMM : forall n x y, equ n x y -> equ n y x;
  equMONO : forall n m, n >= m -> forall x y, equ n x y -> equ m x y;
  equLIMIT : forall x y, x = y <-> forall n, equ n x y;
}.
HB.structure Definition OFE := { T of OFE_of_TYPE T }.

Definition non_expansive {T1 T2 : OFE.type} (f : T1 -> T2) := 
  forall n x y, equ n x y -> equ n (f x) (f y).

Definition option_equ {T : OFE.type} (n : nat) (x y : option T) :=
  match x with
  | Some x => (
    match y with
    | Some y => equ n x y
    | None => False
    end)
  | None => (
    match y with
    | Some y => False
    | None => True
    end)
  end.

Lemma option_equ_refl {T : OFE.type} : 
  forall n (x : option T), option_equ n x x.
Proof.
  intros. 
  destruct x.
  - simpl. apply equREFL.
  - done.  
Qed.

Lemma option_equ_trans {T : OFE.type} : 
  forall n (x : option T) (y : option T) (z : option T), 
    option_equ n x y -> option_equ n y z -> option_equ n x z.
Proof.
  intros.
  destruct x, y, z; try done.
  simpl in *.
  eapply equTRANS.
  - apply H.
  - apply H0.
Qed.

Lemma option_equ_symm {T : OFE.type} : 
  forall n (x : option T) (y : option T), option_equ n x y -> option_equ n y x.
Proof.
  intros.
  destruct x, y; try done.
  simpl in *.
  eauto using equSYMM.
Qed.

Lemma option_equ_mono {T : OFE.type} : 
  forall n m, n >= m -> 
    forall (x : option T) (y : option T), option_equ n x y -> option_equ m x y.
Proof.
  intros.
  destruct x, y; try done.
  simpl in *.
  eauto using equMONO.
Qed.

Lemma option_equ_limit {T : OFE.type} : 
  forall (x : option T) (y : option T), x = y <-> forall n, option_equ n x y.
Proof.
  intros.
  split.
  - intros.
    subst.
    apply option_equ_refl.
  - intros.
    destruct x, y; try done; simpl in *.
    + f_equal.
      by apply equLIMIT.
    + by specialize (H 0).
    + by specialize (H 0).
Qed.

HB.instance Definition option_OFE (T : OFE.type) :=
  OFE_of_TYPE.Build (option T) 
    option_equ option_equ_refl option_equ_trans 
    option_equ_symm option_equ_mono option_equ_limit.

(* Is this the way to define chains? *)
Definition is_chain {T : OFE.type} (c : nat -> T) := 
  forall n m, n <= m -> equ n (c m) (c n).

(* This does not work since we can't define lim like this, 
   however, I also don't know how to do it otherwise. *)
(* HB.mixin Record COFE_of_OFE T of OFE T := {
    lim : forall c : nat -> T, is_chain T c -> c -> T;
    limCOMPL : forall n c, equ n (lim c _) (c n);
}. *)

HB.mixin Record CAMERA_of_OFE M of OFE M := {
  valid : M -> Prop; (* Should be SProp, but don't understand that yet *)
  (* validNE : non_expansive valid; *) 
  (* does not work since Prop is not OFE, but maybe SProp is? *)
  core : M -> option M;
  coreNE : non_expansive core;
  opp : M -> M -> M;
  lte : M -> M -> Prop;
  lteINCL : forall a b, exists c, b = opp a c;
  lteINCLN : forall a b n, exists c, equ n b (opp a c);
  oppA : associative opp;
  oppC : commutative opp;
  coreID : forall a, (exists a', core a = Some a' /\ opp a' a = a);
  coreIDEM : forall a, (exists a', core a = Some a' /\ core a' = Some a');
  coreMONO : forall a b, 
    (exists a', core a = Some a' /\ lte a' b -> 
      (exists b', core b = Some b' /\ lte a' b')
    );
  validOPP : forall a b, valid (opp a b) -> valid a;
  EXTEND : forall n a b1 b2, (* n is element of valid a /\ *) equ n a (opp b1 b2) -> exists c1 c2, equ n a (opp c1 c2) /\ equ n c1 b1 /\ equ n c2 b2;
}.