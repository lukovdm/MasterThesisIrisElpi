From iris.proofmode Require Export base environments classes classes_make modality_instances tactics coq_tactics reduction.
From iris.prelude Require Import options.
From iris.bi Require Export bi telescopes interface derived_laws.
Import bi.
Import env_notations.

From eIris.proofmode Require Import proper.

Section tactics.
Context {PROP : bi}.
Implicit Types Γ : env PROP.
Implicit Types Δ : envs PROP.
Implicit Types P Q : PROP.

Global Lemma tac_exist_destruct_without_name {A} Δ i p j P (Φ : A → PROP) (name: ident_name) Q :
  envs_lookup i Δ = Some (p, P) → IntoExist P Φ name →
  (∀ a, match envs_simple_replace i p (Esnoc Enil j (Φ a)) Δ with
        | Some Δ' => envs_entails Δ' Q
        | None => False
        end) →
  envs_entails Δ Q.
Proof.
  (* rewrite envs_entails_unseal => ?? HΦ. rewrite envs_lookup_sound //.
  rewrite (into_exist P) intuitionistically_if_exist sep_exist_r.
  apply exist_elim=> a; specialize (HΦ a) as Hmatch.
  destruct (envs_simple_replace _ _ _ _) as [Δ'|] eqn:Hrep; last done.
  rewrite envs_simple_replace_singleton_sound' //; simpl. by rewrite wand_elim_r.
Qed. *)
Admitted.

Global Lemma tac_forall_intro_nameless {A} Δ (Φ : A → PROP) Q name :
  FromForall Q Φ name →
  (∀ a, envs_entails Δ (Φ a)) →
  envs_entails Δ Q.
Proof. rewrite envs_entails_unseal /FromForall=> <-. apply iris.bi.interface.bi.forall_intro. Qed.

Local Open Scope lazy_bool_scope.

Lemma tac_specialize_assert_no_am Δ j (q neg : bool) js R P1 P2 P1' Q :
  envs_lookup j Δ = Some (q, R) →
  IntoWand q false R P1 P2 →
  TCEq P1' P1 →
  match
    '(Δ1,Δ2) ← envs_split (if neg is true then Right else Left)
                          js (envs_delete true j q Δ);
    Δ2' ← envs_app (q &&& env_spatial_is_nil Δ1) (Esnoc Enil j P2) Δ2;
    Some (Δ1,Δ2') (* does not preserve position of [j] *)
  with
  | Some (Δ1,Δ2') =>
     (* The constructor [conj] of [∧] still stores the contexts [Δ1] and [Δ2'] *)
     envs_entails Δ1 P1' ∧ envs_entails Δ2' Q
  | None => False
  end → envs_entails Δ Q.
Proof.
  rewrite envs_entails_unseal. intros ?? Hmod HQ.
  destruct (_ ≫= _) as [[Δ1 Δ2']|] eqn:?; last done.
  destruct HQ as [HP1 HQ].
  destruct (envs_split _ _ _) as [[? Δ2]|] eqn:?; simplify_eq/=;
    destruct (envs_app _ _ _) eqn:?; simplify_eq/=.
  rewrite envs_lookup_sound // envs_split_sound //.
  rewrite (envs_app_singleton_sound Δ2) //; simpl.
  rewrite -intuitionistically_if_idemp (into_wand q false) /=.
  destruct (q &&& env_spatial_is_nil Δ1) eqn:Hp; simpl.
  - move: Hp. rewrite !lazy_andb_true. intros [-> ?]; simpl.
    destruct Hmod. rewrite env_spatial_is_nil_intuitionistically // HP1.
    by rewrite assoc intuitionistically_sep_2 wand_elim_l wand_elim_r HQ.
  - rewrite intuitionistically_if_elim HP1. destruct Hmod.
    by rewrite assoc wand_elim_l wand_elim_r HQ.
Qed.

Lemma iproper_top_to_iproper A B R m f :
  @IProperTop PROP A B R m f →
  ⊢@{PROP} (f R) m m.
Proof.
  intros HIPT.
  unfold IProperTop in HIPT.
  done.
Qed.

End tactics.
