From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.

HB.mixin Record RA_of_TYPE M := {
  ν : M -> Prop;
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
  νOP : forall a b, ν (op a b) -> ν a;
}.
HB.structure Definition RA := { M of RA_of_TYPE M }.

HB.mixin Record OFE_of_TYPE T := {
  equ : nat -> T -> T -> Prop;
  equREFL : forall n x, equ n x x;
  equTRANS : forall n x y z, equ n x y -> equ n y z -> equ n x z;
  equSYMM : forall n x y, equ n x y -> equ n y x;
  equMONO : forall n m, n >= m -> forall x y, equ n x y -> equ m x y;
  equLIMIT : forall x y, x = y <-> forall n, equ n x y;
}.
HB.structure Definition OFE := { T of OFE_of_TYPE T }.

Notation "x ≡{ n }≡ y" := (equ n x y)
  (at level 70, n at next level, format "x  ≡{ n }≡  y").
Notation "(≡{ n }≡)" := (equ n) (only parsing).
Global Hint Extern 0 (_ ≡{_}≡ _) => apply equREFL : core.
Global Hint Extern 0 (_ ≡{_}≡ _) => apply equSYMM; assumption : core.

Definition non_expansive {T1 T2 : OFE.type} (f : T1 -> T2) := 
  forall n x y, x ≡{ n }≡ y -> (f x) ≡{n}≡ (f y).

Section option_OFE. 
  Context {T : OFE.type}.
  
  Definition option_equ (n : nat) (x y : option T) :=
    match x, y with
    | Some x, Some y => x ≡{n}≡ y
    | None, None => True
    | _, _ => False
    end.
  Hint Unfold option_equ : core.

  Fact option_equ_refl : forall n (x : option T),
    option_equ n x x.
  Proof.
    intros n []; auto.
  Qed.

  Fact option_equ_trans : 
    forall n (x : option T) (y : option T) (z : option T), 
      option_equ n x y -> option_equ n y z -> option_equ n x z.
  Proof.
    intros n [] [] [] Hxy Hyzl; try done.
    simpl in *.
    eauto using equTRANS.
  Qed.

  Fact option_equ_symm : 
    forall n (x : option T) (y : option T), option_equ n x y -> option_equ n y x.
  Proof.
    intros n [] []; try done.
    simpl in *.
    eauto using equSYMM.
  Qed.

  Fact option_equ_mono : 
    forall n m, n >= m -> 
      forall (x : option T) (y : option T), option_equ n x y -> option_equ m x y.
  Proof.
    intros n m Hgte [] [] Hn; try done.
    simpl in *.
    eauto using equMONO.
  Qed.

  Fact option_equ_limit : 
    forall (x : option T) (y : option T), x = y <-> forall n, option_equ n x y.
  Proof.
    intros x y; split.
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

  HB.instance 
  Definition option_OFE := OFE_of_TYPE.Build (option T) 
    option_equ option_equ_refl option_equ_trans 
    option_equ_symm option_equ_mono option_equ_limit.

End option_OFE.

Section arrow_OFE.
  Context {T1 T2 : OFE.type}.

  Definition arrow_equ (n : nat) (f g : T1 -> T2) :=
    forall x, (f x) ≡{n}≡ (g x).

    Fact arrow_equ_refl n (f : T1 -> T2) : 
      arrow_equ n f f.
    Proof.
      intros x.
      apply equREFL.
    Qed.

    Fact arrow_equ_trans : 
      forall n (f : T1 -> T2) (g : T1 -> T2) (h : T1 -> T2), 
        arrow_equ n f g -> arrow_equ n g h -> arrow_equ n f h.
    Proof.
      intros n f g h H1 H2 x.
      by eapply equTRANS.
    Qed.

    Fact arrow_equ_symm : 
      forall n (f : T1 -> T2) (g : T1 -> T2), 
      arrow_equ n f g -> arrow_equ n g f.
    Proof.
      intros n f g H x.
      by eapply equSYMM.
    Qed.

    Fact arrow_equ_mono : 
      forall n m, n >= m -> 
        forall (f : T1 -> T2) (g : T1 -> T2), 
          arrow_equ n f g -> arrow_equ m f g.
    Proof.
      intros n m Hnm f g Hfg x.
      eapply equMONO; eauto.
    Qed.

    Fact arrow_equ_limit : 
      forall (f : T1 -> T2) (g : T1 -> T2), f = g <-> forall n, arrow_equ n f g.
    Proof.
      intros f g; split.
      - intros.
        subst.
        apply arrow_equ_refl.
      - intros.
        unfold arrow_equ in *.
        Fail rewrite <- equLIMIT in H. 
    Admitted.
End arrow_OFE.

(* Add OFE on A -> B with OFE A B *)

Record chain {T : OFE.type} := {
  chain_car :> nat -> T;
  chain_cauchy : forall n m, n <= m -> equ n (chain_car m) (chain_car n);
}.

HB.mixin Record COFE_of_OFE T of OFE T := {
    lim : forall c : chain, T;
    limCOMPL : forall n c, equ n (lim c) (c n);
}. 

HB.mixin Record CAMERA_of_OFE M of OFE M := {
  ν : M -> Prop; (* Should be SProp, but don't understand that yet *)
  (* νNE : non_expansive ν; *)
  (* does not work since Prop is not OFE, but maybe SProp is? *)
  core : M -> option M;
  coreNE : non_expansive core;
  op : M -> M -> M;
  (* opNE : non_expansive op; *)
  (* Don't yet know how to define non_expansive for M -> M -> M *)
  lte : M -> M -> Prop;
  lteINCL : forall a b, lte a b -> exists c, b = op a c;
  lteINCLN : forall a b n, lte a b -> exists c, equ n b (op a c);
  opA : associative op;
  opC : commutative op;
  coreID : forall a, (exists a', core a = Some a' /\ op a' a = a);
  coreIDEM : forall a, (exists a', core a = Some a' /\ core a' = Some a');
  coreMONO : forall a b, 
    (exists a', core a = Some a' /\ lte a' b -> 
      (exists b', core b = Some b' /\ lte a' b')
    );
  νop : forall a b, ν (op a b) -> ν a;
  EXTEND n a b1 b2 : (* n is element of ν a /\ *) 
    ν a -> equ n a (op b1 b2) -> 
      exists c1 c2, a = op c1 c2 /\ equ n c1 b1 /\ equ n c2 b2;
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
    EXTEND : forall n a b1 b2, (* n is element of ν a /\ *) 
      equ n a (op b1 b2) -> 
        exists c1 c2, equ n a (op c1 c2) /\ equ n c1 b1 /\ equ n c2 b2;
  }.

  Fail HB.builders Context M (m : CAMERA_of_RA M).

    Fail HB.instance
    Definition to_OFE :=
      OFE_of_TYPE.Build M equ equREFL equTRANS equSYMM equMONO equLIMIT.

    Fail HB.instance
    Definition to_CAMERA_of_OFE :=
      CAMERA_of_OFE.Build M ν core coreNE op lte lteINCL lteINCLN 
        opA opC coreID coreIDEM coreMONO νOP EXTEND.
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

