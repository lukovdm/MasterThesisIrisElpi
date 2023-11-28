From stdpp Require Import base tactics.
From stdpp Require Import options.

From iris.prelude Require Import options.
From iris.bi Require Export bi.

Local Set Universe Polymorphism.
Local Set Polymorphic Inductive Cumulativity.

(** Without this flag, Coq minimizes some universes to [Set] when they
    should not be, e.g. in [texist_exist].
    See the [texist_exist_universes] test. *)
Local Unset Universe Minimization ToSet.

(** Telescopes *)
Inductive teleC : Type :=
  | TeleCO : teleC
  | TeleCC (X : ofe) (t : teleC) : teleC
  | TeleCS {X : Type} (binder : X → teleC) : teleC.

Check TeleCC.

Global Arguments TeleCS {_} _.

(** The telescope version of Coq's function type *)
Fixpoint teleC_fun (TT : teleC) (T : Type) : Type :=
  match TT with
  | TeleCO => T
  | TeleCC C t => C -> teleC_fun t T
  | TeleCS b => ∀ x, teleC_fun (b x) T
  end.

Notation "TT -tc> A" :=
  (teleC_fun TT A) (at level 99, A at level 200, right associativity).

(** An eliminator for elements of [tele_fun].
    We use a [fix] because, for some reason, that makes stuff print nicer
    in the proofs in iris:bi/lib/telescopes.v *)
Definition teleC_fold {X Y} {TT : teleC} (step : ∀ {A : Type}, (A → Y) → Y) (base : X → Y)
  : (TT -tc> X) → Y :=
  (fix rec {TT} : (TT -tc> X) → Y :=
     match TT as TT return (TT -tc> X) → Y with
     | TeleCO => λ x : X, base x
     | TeleCC C t => λ f, step (λ x, rec (f x))
     | TeleCS b => λ f, step (λ x, rec (f x))
     end) TT.
Global Arguments teleC_fold {_ _ !_} _ _ _ /.

(** A duplication of the type [sigT] to avoid any connection to other universes
 *)
Record teleC_arg_cons {X : Type} (f : X → Type) : Type := TeleCArgCons
  { teleC_arg_head : X;
    teleC_arg_tail : f teleC_arg_head }.
Global Arguments TeleCArgCons {_ _} _ _.

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

(** A sigma-like type for an "element" of a telescope, i.e. the data it
  takes to get a [T] from a [TT -t> T]. *)
Fixpoint teleC_arg@{u} (t : teleC@{u}) : Type@{u} :=
  match t with
  | TeleCO => unit
  | TeleCC C t => C * (teleC_arg t)
  | TeleCS f => teleC_arg_cons (λ x, teleC_arg (f x))
  end.
Global Arguments teleC_arg _ : simpl never.

Fixpoint teleC_argO (t : teleC) : ofe :=
  match t with
  | TeleCO => unit
  | TeleCC C t => prodO C (teleC_argO t)
  | TeleCS f => teleC_arg_cons (λ x, teleC_argO (f x))
  end.
Global Arguments teleC_argO _ : simpl never.

Compute teleC_arg (TeleCC ofe (TeleCS (fun (x : nat) => TeleCS (fun _ : vec bool x => TeleCO)))).

(* Coq has no idea that [unit] and [teleC_arg_cons] have anything to do with
   telescopes. This only becomes a problem when concrete telescope arguments
   (of concrete telescopes) need to be typechecked. To work around this, we
   annotate the notations below with extra information to guide unification.
 *)

(* The cast in the notation below is necessary to make Coq understand that
   [TargCO] can be unified with [teleC_arg TeleCO]. *)
Notation TargCO := (tt : teleC_arg TeleCO) (only parsing).
(* The casts and annotations are necessary for Coq to typecheck nested [TargCS] [TargCC]
   as well as the final [TargCO] in a chain of [TargCS] [TargCC]. *)
Notation TargCC a b :=
  ((a, b) : (teleC_arg (TeleCC _ _))) (only parsing).
(* The casts and annotations are necessary for Coq to typecheck nested [TargCS] [TargCC]
   as well as the final [TargCO] in a chain of [TargCS] [TargCC]. *)
Notation TargCS a b :=
  ((@TeleCArgCons _ (λ x, teleC_arg (_ x)) a b) : (teleC_arg (TeleCS _))) (only parsing).
Coercion teleC_arg : teleC >-> Sortclass.

Lemma teleC_arg_ind (P : ∀ TT, teleC_arg TT → Prop) :
  P TeleCO TargCO →
  (∀ C (t : teleC) x xs, P t xs → P (TeleCC C t) (TargCC x xs)) →
  (∀ T (b : T → teleC) x xs, P (b x) xs → P (TeleCS b) (TargCS x xs)) →
  ∀ TT (xs : teleC_arg TT), P TT xs.
Proof.
  intros H0 HC HS TT. induction TT as [ |C t IH|T b IH]; simpl.
  - by intros [].
  - intros [x xs]. by apply HC.
  - intros [x xs]. by apply HS.
Qed.

Fixpoint teleC_app {TT : teleC} {U} : (TT -tc> U) -> TT → U :=
  match TT as TT return (TT -tc> U) -> TT → U with
  | TeleCO => λ F _, F
  | TeleCC C t => λ (F : TeleCC C t -tc> U) '(pair x t), teleC_app (F x) t 
  | TeleCS r => λ (F : TeleCS r -tc> U) '(TeleCArgCons x b), teleC_app (F x) b
  end.
(* The bidirectionality hint [&] simplifies defining tele_app-based notation
such as the atomic updates and atomic triples in Iris. *)
Global Arguments teleC_app {!_ _} & _ !_ /.

(* This is a local coercion because otherwise, the "λ.." notation stops working. *)
Local Coercion teleC_app : teleC_fun >-> Funclass.

(** Inversion lemma for [teleC_arg] *)
Lemma teleC_arg_inv {TT : teleC} (a : teleC_arg TT) :
  match TT as TT return teleC_arg TT → Prop with
  | TeleCO => λ a, a = TargCO
  | TeleCC C t => λ a, ∃ x a', a = TargCC x a'
  | TeleCS f => λ a, ∃ x a', a = TargCS x a'
  end a.
Proof. destruct TT; destruct a; eauto. Qed.
Lemma teleC_arg_O_inv (a : TeleCO) : a = TargCO.
Proof. exact (teleC_arg_inv a). Qed.
Lemma teleC_arg_C_inv {C} {t : teleC} (a : TeleCC C t) :
  ∃ x a', a = TargCC x a'.
Proof. exact (teleC_arg_inv a). Qed.
Lemma teleC_arg_S_inv {X} {f : X → teleC} (a : TeleCS f) :
  ∃ x a', a = TargCS x a'.
Proof. exact (teleC_arg_inv a). Qed.

(** Map below a tele_fun *)
Fixpoint teleC_map {T U} {TT : teleC} : (T → U) → (TT -tc> T) → TT -tc> U :=
  match TT as TT return (T → U) → (TT -tc> T) → TT -tc> U with
  | TeleCO => λ F : T → U, F
  | @TeleCC C t => λ (F : T → U) (f : TeleCC C t -tc> T) (c : C),
                  teleC_map F (f c)
  | @TeleCS X b => λ (F : T → U) (f : TeleCS b -tc> T) (x : X),
                  teleC_map F (f x)
  end.
Global Arguments teleC_map {_ _ !_} _ _ /.

Lemma teleC_map_app {T U} {TT : teleC} (F : T → U) (t : TT -tc> T) (x : TT) :
  (teleC_map F t) x = F (t x).
Proof.
  induction TT as [|C te IH|X f IH]; simpl in *.
  - rewrite (teleC_arg_O_inv x). done.
  - destruct (teleC_arg_C_inv x) as [x' [a' ->]]. simpl.
    rewrite <-IH. done.
  - destruct (teleC_arg_S_inv x) as [x' [a' ->]]. simpl.
    rewrite <-IH. done.
Qed.

Global Instance teleC_fmap {TT : teleC} : FMap (teleC_fun TT) := λ T U, teleC_map.

Lemma teleC_fmap_app {T U} {TT : teleC} (F : T → U) (t : TT -tc> T) (x : TT) :
  (F <$> t) x = F (t x).
Proof. apply teleC_map_app. Qed.

(** Operate below [teleC_fun]s with argument teleCscope [TT]. *)
Fixpoint teleC_bind {U} {TT : teleC} : (TT → U) → TT -tc> U :=
  match TT as TT return (TT → U) → TT -tc> U with
  | TeleCO => λ F, F tt
  | TeleCC C t => λ (F : TeleCC C t → U) (c : C),
      teleC_bind (λ a, F (TargCC c a))
  | @TeleCS X b => λ (F : TeleCS b → U) (x : X), (* b x -tc> U *)
      teleC_bind (λ a, F (TargCS x a))
  end.
Global Arguments teleC_bind {_ !_} _ /.

(* Show that teleC_app ∘ teleC_bind is the identity. *)
Lemma teleC_app_bind {U} {TT : teleC} (f : TT → U) x :
  (teleC_bind f) x = f x.
Proof.
  induction TT as [|C t IH|X b IH]; simpl in *.
  - rewrite (teleC_arg_O_inv x). done.
  - destruct (teleC_arg_C_inv x) as [x' [a' ->]]. simpl.
    rewrite IH. done.
  - destruct (teleC_arg_S_inv x) as [x' [a' ->]]. simpl.
    rewrite IH. done.
Qed.

(** We can define the identity function and composition of the [-tc>] function
space. *)
Definition teleC_fun_id {TT : teleC} : TT -tc> TT := teleC_bind id.

Lemma teleC_fun_id_eq {TT : teleC} (x : TT) :
  teleC_fun_id x = x.
Proof. unfold teleC_fun_id. rewrite teleC_app_bind. done. Qed.

Definition teleC_fun_compose {TT1 TT2 TT3 : teleC} :
  (TT2 -tc> TT3) → (TT1 -tc> TT2) → (TT1 -tc> TT3) :=
  λ t1 t2, teleC_bind (compose (teleC_app t1) (teleC_app t2)).

Lemma teleC_fun_compose_eq {TT1 TT2 TT3 : teleC} (f : TT2 -tc> TT3) (g : TT1 -tc> TT2) x :
  teleC_fun_compose f g $ x = (f ∘ g) x.
Proof. unfold teleC_fun_compose. rewrite teleC_app_bind. done. Qed.

(** Notation *)
Notation "'[teleC' x .. z ]" :=
  (TeleCS (fun x => .. (TeleCS (fun z => TeleCO)) ..))
  (x binder, z binder, format "[teleC  '[hv' x  ..  z ']' ]").
Notation "'[teleC' ]" := (TeleCO)
  (format "[teleC ]").

Notation "'[teleC_arg' x ; .. ; z ]" :=
  (TargCS x ( .. (TargCS z TargCO) ..))
  (format "[teleC_arg  '[hv' x ;  .. ;  z ']' ]").
Notation "'[teleC_arg' ]" := (TargCO)
  (format "[teleC_arg ]").

(** Notation-compatible telescope mapping *)
(* This adds (tele_app ∘ tele_bind), which is an identity function, around every
   binder so that, after simplifying, this matches the way we typically write
   notations involving telescopes. *)
Notation "'λ..' x .. y , e" :=
  (teleC_app (teleC_bind (λ x, .. (teleC_app (teleC_bind (λ y, e))) .. )))
  (at level 200, x binder, y binder, right associativity,
   format "'[  ' 'λ..'  x  ..  y ']' ,  e") : stdpp_scope.

(** Telescopic quantifiers *)
Definition tcforall {TT : teleC} (Ψ : TT → Prop) : Prop :=
  teleC_fold (λ (T : Type) (b : T → Prop), ∀ x : T, b x) (λ x, x) (teleC_bind Ψ).
Global Arguments tcforall {!_} _ /.
Definition tcexist {TT : teleC} (Ψ : TT → Prop) : Prop :=
  teleC_fold ex (λ x, x) (teleC_bind Ψ).
Global Arguments tcexist {!_} _ /.

Notation "'∀..' x .. y , P" := (tcforall (λ x, .. (tcforall (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∀..  x  ..  y ,  P") : stdpp_scope.
Notation "'∃..' x .. y , P" := (tcexist (λ x, .. (tcexist (λ y, P)) .. ))
  (at level 200, x binder, y binder, right associativity,
  format "∃..  x  ..  y ,  P") : stdpp_scope.

Lemma tcforall_forall {TT : teleC} (Ψ : TT → Prop) :
  tcforall Ψ ↔ (∀ x, Ψ x).
Proof.
  symmetry. unfold tcforall. induction TT as [|C t IH|X ft IH].
  - simpl. split.
    + done.
    + intros ? p. rewrite (teleC_arg_O_inv p). done.
  - simpl. split; intros Hx a.
    + rewrite <-IH. done.
    + destruct (teleC_arg_C_inv a) as [x [pf ->]].
      revert pf. setoid_rewrite IH. done.
  - simpl. split; intros Hx a.
    + rewrite <-IH. done.
    + destruct (teleC_arg_S_inv a) as [x [pf ->]].
      revert pf. setoid_rewrite IH. done.
Qed.

Lemma tcexist_exist {TT : teleC} (Ψ : TT → Prop) :
  tcexist Ψ ↔ ex Ψ.
Proof.
  symmetry. induction TT as [|C t IH|X ft IH].
  - simpl. split.
    + intros [p Hp]. rewrite (teleC_arg_O_inv p) in Hp. done.
    + intros. by exists TargCO.
  - simpl. split; intros [p Hp]; revert Hp.
    + destruct (teleC_arg_C_inv p) as [x [pf ->]]. intros ?.
      exists x. rewrite <-(IH (λ a, Ψ (TargCC x a))). eauto.
    + rewrite <-(IH (λ a, Ψ (TargCC p a))).
      intros [??]. eauto.
  - simpl. split; intros [p Hp]; revert Hp.
    + destruct (teleC_arg_S_inv p) as [x [pf ->]]. intros ?.
      exists x. rewrite <-(IH x (λ a, Ψ (TargCS x a))). eauto.
    + rewrite <-(IH p (λ a, Ψ (TargCS p a))).
      intros [??]. eauto.
Qed.

(* Teach typeclass resolution how to make progress on these binders *)
Global Typeclasses Opaque tcforall tcexist.
Global Hint Extern 1 (tcforall _) =>
  progress cbn [tcforall teleC_fold teleC_bind teleC_app] : typeclass_instances.
Global Hint Extern 1 (tcexist _) =>
  progress cbn [tcexist teleC_fold teleC_bind teleC_app] : typeclass_instances.
