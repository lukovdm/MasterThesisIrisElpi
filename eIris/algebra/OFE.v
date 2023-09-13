From Coq Require Import ssreflect ssrfun.
From HB Require Import structures.
From Coq.Logic Require Import FunctionalExtensionality.

HB.mixin Record OFE_of_TYPE T := {
  equ : nat -> T -> T -> Prop;
  equREFL : forall n x, equ n x x;
  equTRANS : forall n x y z, equ n x y -> equ n y z -> equ n x z;
  equSYMM : forall n x y, equ n x y -> equ n y x;
  equMONO : forall n m, n >= m -> forall x y, equ n x y -> equ m x y;
  equLIMIT : forall x y, x = y <-> forall n, equ n x y;
}.
HB.structure Definition OFE := { T of OFE_of_TYPE T }.

(* TODO: Make instance for OFE of basic types using just equality *)
(* TODO later: Make automatic instance for inductive types using elpi *)

Notation "x ≡{ n }≡ y" := (@equ _ n x y)
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
    forall x, f x ≡{n}≡ g x.

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
  