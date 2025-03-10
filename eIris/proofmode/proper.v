Require Import Program.Tactics.
From stdpp Require Import coPset.
From iris.bi Require Export bi.
From iris.proofmode Require Import proofmode tactics coq_tactics reduction.
From iris.prelude Require Import options.

Section iRelation_Definition.

  Definition iRelation {PROP : bi} {A} := A → A → PROP.
  Global Arguments iRelation {_} _%I : simpl never.

  Definition iFlip {PROP : bi} {A B} : (A → B → PROP) → B → A → PROP := 
    λ F y x, F x y.
  Global Arguments iFlip {_} {_ _}.

End iRelation_Definition.

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

  Definition iRespectful {A B} (R : iRelation A) (R' : iRelation B) : @iRelation PROP (A → B)%type 
    := λ f g, (∀ x y, R x y -∗ R' (f x) (g y))%I.
  Global Arguments iRespectful {_ _}%I R%i_signature R'%i_signature.

  Definition iPointwise_relation {A B} (R : iRelation B) : @iRelation PROP (A → B)%type 
    := λ f g, (∀ a, R (f a) (g a))%I.
  Global Arguments iPointwise_relation {_ _}%I R%i_signature.

  Definition iPersistent_relation {A} (R : iRelation A) : @iRelation PROP A
    := λ x y, (□ (R x y))%I.
  Global Arguments iPersistent_relation {_}%I R%i_signature.

End iProper_Definition.

Notation " R ==> R' " := (iRespectful R%i_signature R'%i_signature) (right associativity, at level 55) : i_signature_scope.
Notation " .> R " := (iPointwise_relation R%i_signature) (right associativity, at level 51) : i_signature_scope.
Notation " □> R " := (iPersistent_relation R%i_signature) (right associativity, at level 51) : i_signature_scope.

Section Experiments.
  Context {PROP : bi}.
  Global Instance sep_IProper : @IProper PROP _ (bi_wand ==> bi_wand ==> bi_wand) bi_sep.
    unfold IProper, iRespectful.
    iIntros (x y) "Hxy %x' %y' Hxy' [Hx Hx']".
    iSplitL "Hxy Hx".
      - by iApply "Hxy".
      - by iApply "Hxy'".
  Qed.

  Global Instance sep_IProperTop : IProperTop (@bi_wand PROP) (bi_sep) (fun F => bi_wand ==> bi_wand ==> F)%i_signature.
    unfold IProperTop.
    tc_solve.
  Qed.

  Global Instance exists_IProper {A} : IProper (.> bi_wand ==> bi_wand) (@bi_exist PROP A).
    unfold IProper, iPointwise_relation, iRespectful.
    iIntros (x y) "Hxaya [%y' Hxy]".
    iExists y'.
    by iApply "Hxaya".
  Qed.

  Global Instance exists_IProperTop {A} : IProperTop (bi_wand) (@bi_exist PROP A) (fun F => .> bi_wand ==> F)%i_signature.
    unfold IProperTop.
    tc_solve.
  Qed.

  Global Instance forall_IProper {A} : IProper (.> bi_wand ==> bi_wand) (@bi_forall PROP A).
    unfold IProper, iPointwise_relation, iRespectful.
    iIntros (p q) "Hxaya Hxy %z".
    iApply "Hxaya".
    change p with (fun x => p x).
    done.
  Qed.

  Global Instance forall_IProperTop {A} : IProperTop (bi_wand) (@bi_forall PROP A) (fun F => .> bi_wand ==> F)%i_signature.
    unfold IProperTop.
    tc_solve.
  Qed.

  Global Instance or_IProper : IProper (□> bi_wand ==> □> bi_wand ==> bi_wand) (@bi_or PROP).
  Proof.
    unfold IProper, iRespectful.
    iIntros (x y) "#Hxy %x' %y' #Hxy' [Hx | Hx']".
    - iLeft.
      by iApply "Hxy".
    - iRight.
      by iApply "Hxy'".
  Qed.

  (* Global Instance or_IProper' `{!BiAffine PROP} : IProper (bi_wand ==> bi_wand ==> bi_wand) (@bi_or PROP).
  Proof.
    unfold IProper, iRespectful.
    iIntros (x y) "Hxy %x' %y' Hxy' [Hx | Hx']".
    - iLeft.
      by iApply "Hxy".
    - iRight.
      by iApply "Hxy'".
  Qed. *)

  Global Instance or_IProperTop : @IProperTop PROP _ _ (@bi_wand PROP) (@bi_or PROP) (fun F => □> bi_wand ==> □> bi_wand ==> F)%i_signature.
    unfold IProperTop.
    tc_solve.
  Qed.

  Global Instance wand_IProper : IProper (iFlip bi_wand ==> bi_wand ==> bi_wand) (@bi_wand PROP).
    unfold IProper, iRespectful, iFlip.
    iIntros (P Q) "HQP %R %S HRS HPR HQ".
    iApply "HRS". 
    iApply "HPR". 
    by iApply "HQP".
  Qed.

  Global Instance wand_IProperTop : @IProperTop PROP _ _ (@bi_wand PROP) (@bi_wand PROP) (fun F => iFlip bi_wand ==> bi_wand ==> F)%i_signature.
    unfold IProperTop.
    tc_solve.
  Qed.

  Global Instance fupd_IProper `(BiFUpd PROP) (A B : coPset) : IProper (bi_wand ==> bi_wand) (@fupd PROP bi_fupd_fupd A B).
    unfold IProper, iRespectful.
    iIntros "%P %Q HPQ HABP".
    by iApply "HPQ".
  Qed.

  Global Instance fudp_IProperTop `(BiFUpd PROP) (A B : coPset) : @IProperTop PROP _ _ (@bi_wand PROP) (@fupd PROP bi_fupd_fupd A B) (fun F => bi_wand ==> F)%i_signature.
    unfold IProperTop.
    tc_solve.
  Qed.

  Global Instance big_opL_IProper {A} : IProper (□> .> .> bi_wand ==> .> bi_wand) (@big_opL PROP bi_sep _ A).
    unfold IProper, iRespectful, iPointwise_relation.
    iIntros (P Q) "#HPQ %a".
    iRevert (P Q) "HPQ".
    iInduction a as [ |y ys] "IH"; iIntros (P Q) "#HPQ Hbo".
    - iSimpl in "Hbo".
      by iSimpl.
    - iSimpl in "Hbo".
      iDestruct "Hbo" as "[HP Hbo]".
      iSimpl.
      iSplitL "HP".
      + by iApply "HPQ".
      + iApply "IH".
        2: {done. }
        iModIntro.
        iIntros (a a').
        iApply "HPQ".
  Qed.

  Global Instance big_opL_IProperTop {A} : @IProperTop PROP _ _ (@bi_wand PROP) (@big_opL PROP bi_sep _ A) (fun F => □> .> .> bi_wand ==> .> F)%i_signature.
    unfold IProperTop.
    tc_solve.
  Qed.

End Experiments.
