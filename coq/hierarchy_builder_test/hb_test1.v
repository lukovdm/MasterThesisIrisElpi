From Coq Require Import ssreflect ssrfun Relations.
From HB Require Import structures.

HB.mixin Record RA_of_TYPE M := {
  valid : M -> Prop;
  core : M -> option M;
  op : M -> M -> M;
  lte : M -> M -> Prop;
  lteINCL : forall a b, exists c, b = op a c;
  opA : associative op;
  opC : commutative op;
  coreID : forall a, (exists a', core a = Some a' /\ op a' a = a);
  coreIDEM : forall a, (exists a', core a = Some a' /\ core a' = Some a');
  coreMONO : forall a b, 
    (exists a', core a = Some a' /\ lte a' b -> 
      (exists b', core b = Some b' /\ lte a' b')
    );
  validOP : forall a b, valid (op a b) -> valid a;
}.
HB.structure Definition RA := { M of RA_of_TYPE M }.

(* This does not work with the error, (equ n) is not a Type, but I don't know why *)
Fail HB.mixin Record OFE_of_TYPE T := {
  equ : nat -> T -> T -> Prop;
  equREFL : forall n, reflexive (equ n);
  equTRANS : forall n, transitive (equ n);
  equSYMM : forall n, symmetric (equ n);
  equMONO : forall n m, n >= m -> inclusion (equ n) (equ m);
}.

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
Fail HB.mixin Record COFE_of_OFE T of OFE T := {
    lim : forall c : nat -> T, is_chain T c -> c -> T;
    limCOMPL : forall n c, equ n (lim c _) (c n);
}. 

HB.mixin Record CAMERA_of_OFE M of OFE M := {
  valid : M -> Prop; (* Should be SProp, but don't understand that yet *)
  (* validNE : non_expansive valid; *)
  (* does not work since Prop is not OFE, but maybe SProp is? *)
  core : M -> option M;
  coreNE : non_expansive core;
  op : M -> M -> M;
  (* opNE : non_expansive op; *)
  (* Don't yet know how to define non_expansive for M -> M -> M *)
  lte : M -> M -> Prop;
  lteINCL : forall a b, exists c, b = op a c;
  lteINCLN : forall a b n, exists c, equ n b (op a c);
  opA : associative op;
  opC : commutative op;
  coreID : forall a, (exists a', core a = Some a' /\ op a' a = a);
  coreIDEM : forall a, (exists a', core a = Some a' /\ core a' = Some a');
  coreMONO : forall a b, 
    (exists a', core a = Some a' /\ lte a' b -> 
      (exists b', core b = Some b' /\ lte a' b')
    );
  validop : forall a b, valid (op a b) -> valid a;
  EXTEND : forall n a b1 b2, (* n is element of valid a /\ *) 
    equ n a (op b1 b2) -> 
      exists c1 c2, equ n a (op c1 c2) /\ equ n c1 b1 /\ equ n c2 b2;
}.
HB.structure Definition CAMERA := { M of OFE M & CAMERA_of_OFE M }.


(* I have no clue how to use non_expansive here, 
   as we haven't proven yet that this record is also an ofe.
   That only happens in the to_OFE definition below.
   You might also be able to prove either coreNE or one of the others
   from the ofe axioms, but haven't figured that out yet *)
  Fail HB.factory Record CAMERA_of_RA M of RA M := {
    equ : nat -> M -> M -> Prop;
    equREFL : forall n x, equ n x x;
    equTRANS : forall n x y z, equ n x y -> equ n y z -> equ n x z;
    equSYMM : forall n x y, equ n x y -> equ n y x;
    equMONO : forall n m, n >= m -> forall x y, equ n x y -> equ m x y;
    equLIMIT : forall x y, x = y <-> forall n, equ n x y;

    coreNE : non_expansive core;
    lteINCLN : forall a b n, exists c, equ n b (op a c);
    EXTEND : forall n a b1 b2, (* n is element of valid a /\ *) 
      equ n a (op b1 b2) -> 
        exists c1 c2, equ n a (op c1 c2) /\ equ n c1 b1 /\ equ n c2 b2;
  }.

  Fail HB.builders Context M (m : CAMERA_of_RA M).

    Fail HB.instance
    Definition to_OFE :=
      OFE_of_TYPE.Build M equ equREFL equTRANS equSYMM equMONO equLIMIT.

    Fail HB.instance
    Definition to_CAMERA_of_OFE :=
      CAMERA_of_OFE.Build M valid core coreNE op lte lteINCL lteINCLN 
        opA opC coreID coreIDEM coreMONO validOP EXTEND.
  Fail HB.end.
(* End of part I have questions about *)

HB.graph "iris_hierarchy.dot".

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Local Open Scope hb_scope.
Infix "." := (@op _) (at level 50, left associativity) : hb_scope.

Section camera.
Variable (M : CAMERA.type).
(* I have no clue why this fails, it feels like it is 
   just giving random errors now *)
Implicit Types x y z : M.

(* op *)
Fail Lemma opA x y z : @op M x (@op M y z) = @op M (@op M x y) z.

