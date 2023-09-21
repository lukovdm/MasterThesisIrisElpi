From HB Require Import structures.
From stdpp Require Import finite.
From Coq Require Export Morphisms RelationClasses List Bool Setoid Peano Utf8.

HB.mixin Record EQUIV_of_TYPE R := {
  equiv : relation R;
  equivREFL : Reflexive equiv;
  equivSYM : Symmetric equiv;
  equivTRANS : Transitive equiv;
}.

HB.structure Definition EQUIV := { R of EQUIV_of_TYPE R }.

Declare Scope eIris_scope.
Delimit Scope eIris_scope with eIris.
Global Open Scope eIris_scope.

Infix "≡🪥" := equiv (at level 70, no associativity) : eIris_scope.
Infix "≡🪥@{ A }" := (@equiv A _)
  (at level 70, only parsing, no associativity) : eIris_scope.

Notation "(≡🪥)" := equiv (only parsing) : eIris_scope.
Notation "( X ≡🪥.)" := (equiv X) (only parsing) : eIris_scope.
Notation "(.≡🪥 X )" := (λ Y, Y ≡🪥 X) (only parsing) : eIris_scope.
Notation "(≢🪥)" := (λ X Y, ¬X ≡🪥 Y) (only parsing) : eIris_scope.
Notation "X ≢🪥 Y":= (¬X ≡🪥 Y) (at level 70, no associativity) : eIris_scope.
Notation "( X ≢🪥.)" := (λ Y, X ≢🪥 Y) (only parsing) : eIris_scope.
Notation "(.≢🪥 X )" := (λ Y, Y ≢🪥 X) (only parsing) : eIris_scope.

Notation "(≡🪥@{ A } )" := (@equiv A) (only parsing) : eIris_scope.
Notation "(≢🪥@{ A } )" := (λ X Y, ¬X ≡🪥@{A} Y) (only parsing) : eIris_scope.
Notation "X ≢🪥@{ A } Y":= (¬X ≡🪥@{ A } Y)
  (at level 70, only parsing, no associativity) : eIris_scope.

HB.factory Record EQUIV_of_LEIBNIZ R := {}.
HB.builders Context R (r : EQUIV_of_LEIBNIZ R).
  Definition equiv : relation R := (=).

  Fact equivREFL : Reflexive equiv.
  Proof. done. Qed.

  Fact equivSYM : Symmetric equiv.
  Proof. unfold Symmetric. by symmetry. Qed.

  Fact equivTrans : Transitive equiv.
  Proof. unfold Transitive. by intros x y z -> ->. Qed.

  HB.instance
  Definition to_EQUIV_of_TYPE :=
    EQUIV_of_TYPE.Build R equiv equivREFL equivSYM equivTrans.
HB.end.

HB.instance Definition bool_EQUIV := EQUIV_of_LEIBNIZ.Build bool.
HB.instance Definition nat_EQUIV := EQUIV_of_LEIBNIZ.Build nat.
HB.instance Definition unit_EQUIV := EQUIV_of_LEIBNIZ.Build unit.
Section option_EQUIV. 
  Context {T : EQUIV.type}.
  HB.instance Definition option_EQUIV := EQUIV_of_LEIBNIZ.Build (option T).
End option_EQUIV.
