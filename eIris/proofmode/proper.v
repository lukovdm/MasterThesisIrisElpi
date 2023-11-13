From iris.bi Require Export bi fixpoint.
From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.
Require Import Program.Tactics.

Section iRelation_Definition.

  Definition iRelation {PROP : bi} {A} := A → A → PROP.
  Global Arguments iRelation {_} _%I : simpl never.

End iRelation_Definition.

Section iRelation_Classes.
  Class iReflexive {PROP : bi} {A} (R : iRelation A) := 
    iReflexivity : ⊢@{ PROP } ∀ x, R x x.

  Class iTransitive {PROP : bi} {A} (R : iRelation A) :=
    iTransitivity : ⊢@{ PROP } ∀ x y z, R x y → R y z → R x z.

  Program Instance bi_impl_iReflexive {PROP : bi} : @iReflexive PROP _ bi_impl.
  Program Instance bi_impl_iTransitive {PROP : bi} : @iTransitive PROP _ bi_impl.
  Admit Obligations.

  Program Instance bi_wand_iReflexive {PROP : bi} : @iReflexive PROP _ bi_wand.
  Program Instance bi_wand_iTransitive {PROP : bi} : @iTransitive PROP _ bi_wand.
  Admit Obligations.
End iRelation_Classes.

Declare Scope i_signature_scope.
Delimit Scope i_signature_scope with i_signature.

Section iProper_Definition.
  Context {PROP : bi}.

  Class IProper {A} (R : iRelation A) (m : A) := iProper : ⊢@{ PROP } R m m.
  Global Arguments IProper {_%I} R%i_signature.
  Global Arguments iProper {_%I} (R%i_signature).

  Class IProperTop {A} {B} (R : @iRelation PROP A) (m : B) f := iProperTop : IProper (f R) m.
  Global Arguments IProperTop {_ _}%I R%i_signature m f%i_signature.
  Global Arguments iProperTop {_ _}%I R%i_signature m f%i_signature.

  Global Instance iReflexive_iProper {A} (R : iRelation A) `(@iReflexive PROP A R) (x : A) : IProper R x.
    unfold IProper.
    iApply iReflexivity.
  Defined.

  Definition iRespectful {A B} (R : iRelation A) (R' : iRelation B) : @iRelation PROP (A → B)%type 
    := λ f g, (∀ x y, R x y -∗ R' (f x) (g y))%I.
  Global Arguments iRespectful {_ _}%I R%i_signature R'%i_signature.

  Definition iPointwise_relation {A B} (R : iRelation B) : @iRelation PROP (A → B)%type 
    := λ f g, (∀ a, R (f a) (g a))%I.
  Global Arguments iPointwise_relation {_ _}%I R%i_signature.

  Inductive n_ip_relation : ∀ A, nat -> @iRelation PROP A -> Type :=
    | z_ip_relation {A} (R : iRelation A) : @n_ip_relation A 0 R
    | s_ip_relation {A B} (n : nat) (R : iRelation B) : n_ip_relation B (n - 1) R -> n_ip_relation (A -> B) n (@iPointwise_relation A B R).
  
  Definition iPersistent_relation {A} (R : iRelation A) : @iRelation PROP A
    := λ x y, (□ (R x y))%I.
  Global Arguments iPersistent_relation {_}%I R%i_signature.

End iProper_Definition.

Notation " R ==> R' " := (iRespectful R%i_signature R'%i_signature) (right associativity, at level 55) : i_signature_scope.
Notation " .> R " := (iPointwise_relation R%i_signature) (right associativity, at level 51) : i_signature_scope.
Notation " □> R " := (iPersistent_relation R%i_signature) (right associativity, at level 51) : i_signature_scope.

Section BiMonoProper.
  Class BiMonoProper {PROP : bi} {A : ofe} (F : (A → PROP) → (A → PROP)) := {
    bi_mono_proper :
      @IProper PROP _ (□> .> bi_wand ==> .> bi_wand) F;
    bi_mono_proper_ne Φ : NonExpansive Φ → NonExpansive (F Φ)
  }.
  Global Arguments BiMonoProper {_} _%I F%I.
End BiMonoProper.

Section Experiments.
  Context {PROP : bi}.
  Global Instance sep_IProper : @IProper PROP _ (bi_wand ==> bi_wand ==> bi_wand) bi_sep.
    unfold IProper, iRespectful.
    iIntros (x y) "Hxy %x' %y' Hxy' [Hx Hx']".
    iSplitL "Hxy Hx".
      - by iApply "Hxy".
      - by iApply "Hxy'".
  Defined.

  Global Instance sep_IProperTop : IProperTop (@bi_wand PROP) (bi_sep) (fun F => bi_wand ==> bi_wand ==> F)%i_signature.
    unfold IProperTop.
    tc_solve.
  Defined.

  Global Instance exists_IProper {A} : IProper (.> bi_wand ==> bi_wand) (@bi_exist PROP A).
    unfold IProper, iPointwise_relation, iRespectful.
    iIntros (x y) "Hxaya [%y' Hxy]".
    iExists y'.
    by iApply "Hxaya".
  Defined.

  Global Instance exists_IProperTop {A} : IProperTop (bi_wand) (@bi_exist PROP A) (fun F => .> bi_wand ==> F)%i_signature.
    unfold IProperTop.
    tc_solve.
  Defined.

  Global Instance or_IProper : IProper (□> bi_wand ==> □> bi_wand ==> bi_wand) (@bi_or PROP).
  Proof.
    unfold IProper, iRespectful.
    iIntros (x y) "#Hxy %x' %y' #Hxy' [Hx | Hx']".
    - iLeft.
      by iApply "Hxy".
    - iRight.
      by iApply "Hxy'".
  Defined.

  Global Instance or_IProperTop : @IProperTop PROP _ _ (@bi_wand PROP) (@bi_or PROP) (fun F => □> bi_wand ==> □> bi_wand ==> F)%i_signature.
    unfold IProperTop.
    tc_solve.
  Defined.

  Instance IProper_BiMonoPred {A : ofe} 
    (F : (A → PROP) → (A → PROP)) 
    `(BiMonoProper PROP A F) : BiMonoPred F.
    constructor.
    - iIntros (Φ Ψ HneΦ HneΨ) "#H %x HF".
      assert (@IProper PROP _ (□> .> bi_wand ==> .> bi_wand) F).
      { apply bi_mono_proper. }
      unfold IProper in H0.
      iApply H0; done.
    - apply bi_mono_proper_ne.
  Defined.

End Experiments.
