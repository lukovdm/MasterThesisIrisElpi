From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.
From Coq.Logic Require Import FunctionalExtensionality.
(* From iris.prelude Require Import options. *)

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

HB.mixin Record OFE_of_TYPE T := {
  equ : nat -> T -> T -> Prop;
  equREFL : forall n x, equ n x x;
  equTRANS : forall n x y z, equ n x y -> equ n y z -> equ n x z;
  equSYMM : forall n x y, equ n x y -> equ n y x;
  equMONO : forall n m, n >= m -> forall x y, equ n x y -> equ m x y;
  equLIMIT : forall x y, x = y <-> forall n, equ n x y;
}.
HB.structure Definition OFE := { T of OFE_of_TYPE T }.

Notation "x ≡{ n }≡ y" := (@equ _ n x y)
  (at level 70, n at next level, format "x  ≡{ n }≡  y").
Notation "(≡{ n }≡)" := (equ n) (only parsing).
Global Hint Extern 0 (_ ≡{_}≡ _) => apply equREFL : core.
Global Hint Extern 0 (_ ≡{_}≡ _) => apply equSYMM; assumption : core.

Infix "⋅" := op (at level 50, left associativity).

Notation "✓ x" := (valid x) (at level 20).

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
        eapply functional_extensionality.
        intros x.
        by rewrite equLIMIT.
    Qed.

    HB.instance 
    Definition arrow_OFE := OFE_of_TYPE.Build (T1 -> T2)
      arrow_equ arrow_equ_refl arrow_equ_trans 
      arrow_equ_symm arrow_equ_mono arrow_equ_limit.
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
}.
HB.structure Definition CAMERA_OR := { M of OFE M & RA M & CAMERA_of_OFE_and_RA M }.

Notation "x ≼{ n } y" := (lteN n x y) (at level 70, n at next level, format "x  ≼{ n }  y").
Global Hint Extern 0 (_ ≼{_} _) => reflexivity : core.
Notation "✓{ n } x" := (validN n x) (at level 20, n at next level, format "✓{ n }  x").

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
  lteINCL : forall a b, lte a b <-> exists c, b = op a c;
  lteN : nat -> M -> M -> Prop;
  lteNDEF : forall a b n, lteN n a b <-> exists c, b ≡{n}≡ op a c;
  opA : associative op;
  opC : commutative op;
  coreID : forall a, (exists a', core a = Some a' /\ op a' a = a);
  coreIDEM : forall a, (exists a', core a = Some a' /\ core a' = Some a');
  coreMONO : forall a b, 
    (exists a', core a = Some a' /\ lte a' b -> 
      (exists b', core b = Some b' /\ lte a' b')
    );
  validOP : forall a b, valid (op a b) -> valid a;
  EXTEND n a b1 b2 : (* n is element of valid a /\ *) 
    valid a -> equ n a (op b1 b2) -> 
      exists c1 c2, a = op c1 c2 /\ equ n c1 b1 /\ equ n c2 b2;
}.
HB.structure Definition CAMERA_O := { M of OFE M & CAMERA_of_OFE M }.

HB.graph "iris_hierarchy.dot".

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Local Open Scope hb_scope.

Section camera.
Variable (M : CAMERA_OR.type).
Implicit Types x y z : M.

(* op *)
Lemma opA_aux x y z : @op M x (@op M y z) = @op M (@op M x y) z.
Proof.
  apply opA.
Qed.
