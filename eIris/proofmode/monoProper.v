From iris.bi Require Import bi fixpoint.

From eIris.proofmode Require Import telescopes proper.


Global Arguments teleC_arg_consO {_} _.

Section teleC_arg_OFE.
  Context {TT : teleC}.
  
  (* Local Instance teleC_dist : Dist teleC := λ n x1 x2,
    match x1, x2 with
    | TeleCO, TeleCO => True
    | TeleCC C1 t1, TeleCC C2 t2 => C1 = C2 ∧ t1 ≡{n}≡ t2
    | @TeleCS A1 b1, @TeleCS A2 b2 => ∀ x y, A1 = A2 ∧ b1 x ≡{n}≡ b2 y
    | _, _ => False
    end. *)

  (* Local Instance teleC_arg_dist : Dist (teleC_arg TT) := λ n x1 x2, *)

End teleC_arg_OFE.
    

Section BiMonoProper.
  Class BiMonoProper {PROP : bi} {TT : teleC} (F : (teleC_arg TT → PROP) → (teleC_arg TT → PROP)) := {
    bi_mono_proper :
      @IProper PROP _ (□> .> bi_wand ==> .> bi_wand) F;
      bi_mono_proper_ne Φ : NonExpansive Φ → NonExpansive (F Φ)
  }.
  Global Arguments BiMonoProper {_} _%I F%I.

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
End BiMonoProper.
