From iris.bi Require Import bi fixpoint.

From eIris.proofmode Require Import telescopes proper.

Section Args_Cons_OFE.
  (** * SigmaT type *)
  (** Ofe for [teleC_arg_cons]. The first component must be discrete and use Leibniz
  equality, while the second component might be any OFE. *)
  Import EqNotations.

  Context {A : Type} {P : A → ofe}.
  Implicit Types x : teleC_arg_cons P.

  (**
    The distance for [{ a : A & P }] uses Leibniz equality on [A] to
    transport the second components to the same type,
    and then step-indexed distance on the second component.
    Unlike in the topos of trees, with (C)OFEs we cannot use step-indexed equality
    on the first component.
  *)
  Local Instance teleC_arg_cons_dist : Dist (teleC_arg_cons P) := λ n x1 x2,
    ∃ Heq : teleC_arg_head P x1 = teleC_arg_head P x2, rew Heq in teleC_arg_tail P x1 ≡{n}≡ teleC_arg_tail P x2.

  (**
    Usually we'd give a direct definition, and show it equivalent to
    [∀ n, x1 ≡{n}≡ x2] when proving the [equiv_dist] OFE axiom.
    But here the equivalence requires UIP — see [sigT_equiv_eq_alt].
    By defining [equiv] in terms of [dist], we can define an OFE
    without assuming UIP, at the cost of complex reasoning on [equiv].
  *)
  Local Instance teleC_arg_cons_equiv : Equiv (teleC_arg_cons P) := λ x1 x2,
    ∀ n, x1 ≡{n}≡ x2.

  (** Unfolding lemmas.
      Written with [↔] not [=] to avoid https://github.com/coq/coq/issues/3814. *)
  Definition teleC_arg_cons_equiv_eq x1 x2 : (x1 ≡ x2) ↔ ∀ n, x1 ≡{n}≡ x2 :=
      reflexivity _.

  Definition teleC_arg_cons_dist_eq x1 x2 n : (x1 ≡{n}≡ x2) ↔
    ∃ Heq : teleC_arg_head P x1 = teleC_arg_head P x2, (rew Heq in teleC_arg_tail P x1) ≡{n}≡ teleC_arg_tail P x2 :=
      reflexivity _.

  Definition teleC_arg_cons_dist_proj1 n {x y} : x ≡{n}≡ y → teleC_arg_head P x = teleC_arg_head P y := proj1_ex.
  Definition teleC_arg_cons_equiv_proj1 {x y} : x ≡ y → teleC_arg_head P x = teleC_arg_head P y := λ H, proj1_ex (H 0).

  Definition teleC_arg_cons_ofe_mixin : OfeMixin (teleC_arg_cons P).
  Proof.
    split => // n.
    - split; hnf; setoid_rewrite teleC_arg_cons_dist_eq.
      + intros. by exists eq_refl.
      + move => [xa x] [ya y] /=. destruct 1 as [-> Heq].
        by exists eq_refl.
      + move => [xa x] [ya y] [za z] /=.
        destruct 1 as [-> Heq1].
        destruct 1 as [-> Heq2]. exists eq_refl => /=. by trans y.
    - setoid_rewrite teleC_arg_cons_dist_eq.
      move => m [xa x] [ya y] /=. destruct 1 as [-> Heq].
      exists eq_refl. by eapply dist_dist_later.
  Qed.

  Canonical Structure teleC_arg_consO : ofe := Ofe (teleC_arg_cons P) teleC_arg_cons_ofe_mixin.

  Lemma teleC_arg_cons_equiv_eq_alt `{!∀ a b : A, ProofIrrel (a = b)} x1 x2 :
    x1 ≡ x2 ↔
    ∃ Heq : teleC_arg_head P x1 = teleC_arg_head P x2, rew Heq in teleC_arg_tail P x1 ≡ teleC_arg_tail P x2.
  Proof.
    setoid_rewrite equiv_dist; setoid_rewrite teleC_arg_cons_dist_eq; split => Heq.
    - move: (Heq 0) => [H0eq1 _].
      exists H0eq1 => n. move: (Heq n) => [] Hneq1.
      by rewrite (proof_irrel H0eq1 Hneq1).
    - move: Heq => [Heq1 Heqn2] n. by exists Heq1.
  Qed.

  (** [teleC_arg_head] is non-expansive and proper. *)
  Global Instance teleC_arg_head_ne : NonExpansive (teleC_arg_head P : teleC_arg_consO → leibnizO A).
  Proof. solve_proper. Qed.

  Global Instance teleC_arg_head_proper : Proper ((≡) ==> (≡)) (teleC_arg_head P : teleC_arg_consO → leibnizO A).
  Proof. apply ne_proper, teleC_arg_head_ne. Qed.

  (** [teleC_arg_tail] is "non-expansive"; the properness lemma [teleC_arg_tail_ne] requires UIP. *)
  Lemma teleC_arg_tail_ne n (x1 x2 : teleC_arg_consO) (Heq : x1 ≡{n}≡ x2) :
    rew (teleC_arg_cons_dist_proj1 n Heq) in teleC_arg_tail P x1 ≡{n}≡ teleC_arg_tail P x2.
  Proof. by destruct Heq. Qed.

  Lemma teleC_arg_tail_proper `{!∀ a b : A, ProofIrrel (a = b)} (x1 x2 : teleC_arg_consO) (Heqs : x1 ≡ x2):
    rew (teleC_arg_cons_equiv_proj1 Heqs) in teleC_arg_tail P x1 ≡ teleC_arg_tail P x2.
  Proof.
    move: x1 x2 Heqs => [a1 x1] [a2 x2] Heqs.
    case: (proj1 (teleC_arg_cons_equiv_eq_alt _ _) Heqs) => /=. intros ->.
    rewrite (proof_irrel (teleC_arg_cons_equiv_proj1 Heqs) eq_refl) /=. done.
  Qed.

  Implicit Types (c : chain teleC_arg_consO).

  Global Instance teleC_arg_cons_discrete x : Discrete (teleC_arg_tail P x) → Discrete x.
  Proof.
    move: x => [xa x] ? [ya y] [] /=; intros -> => /= Hxy n.
    exists eq_refl => /=. apply equiv_dist, (discrete _), Hxy.
  Qed.

  Global Instance teleC_arg_cons_ofe_discrete : (∀ a, OfeDiscrete (P a)) → OfeDiscrete teleC_arg_consO.
  Proof. intros ??. apply _. Qed.
End Args_Cons_OFE.
Global Arguments teleC_arg_consO {_} _.

Section teleC_arg_OFE.
  Context {TT : teleC}.
  
  Local Instance teleC_dist : Dist teleC := λ n x1 x2,
    match x1, x2 with
    | TeleCO, TeleCO => True
    | TeleCC C1 t1, TeleCC C2 t2 => C1 = C2 ∧ t1 ≡{n}≡ t2
    | @TeleCS A1 b1, @TeleCS A2 b2 => ∀ x y, A1 = A2 ∧ b1 x ≡{n}≡ b2 y
    | _, _ => False
    end.

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
