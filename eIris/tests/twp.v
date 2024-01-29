From elpi Require Import elpi.

From iris.bi Require Import fixpoint big_op.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris.proofmode Require Import base environments proofmode tactics coq_tactics reduction intro_patterns class_instances spec_patterns.


From eIris.proofmode Require Import base inductive.

Section TWP.

  Context `{!irisGS_gen hlc Λ Σ}.

  (* Elpi Trace Browser. *)
  #[debug]
  EI.ind
  Inductive twp2 (s : stuckness) : coPset -> expr Λ -> (val Λ -> iProp Σ) -> iProp Σ :=
    (* | twp2_some E v e1 Φ : (|={E}=> Φ v) -∗ ⌜to_val e1 = Some v⌝ -∗ twp2 s E e1 Φ *)
    | twp2_none E e1 Φ : (∀ σ1 ns κs nt,
                    state_interp σ1 ns κs nt ={E,∅}=∗
                      ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
                      ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
                        ⌜κ = []⌝ ∗
                        state_interp σ2 (S ns) κs (length efs + nt) ∗
                        twp2 s E e2 Φ ∗
                        [∗ list] ef ∈ efs, twp2 s ⊤ ef fork_post) -∗ ⌜to_val e1 = None⌝ 
                          -∗ twp2 s E e1 Φ.

  Local Ltac iApplyHypExact H :=
    eapply tac_assumption with H _ _; (* (i:=H) *)
      [pm_reflexivity
      |tc_solve
      |pm_reduce; tc_solve ||
        fail 1 "iApply: remaining hypotheses not affine and the goal not absorbing"].
  
  Local Tactic Notation "iSpecializePat" open_constr(H) constr(pat) :=
    let pats := spec_pat.parse pat in iSpecializePat_go H pats.

  Local Ltac iApplyHypLoop H :=
    idtac "hyploop";
    first
      [eapply tac_apply with H _ _ _;
        [pm_reflexivity
        |tc_solve
        |pm_reduce]
      |idtac "start spec"; iSpecializePat H "[]"; last iApplyHypLoop H].
  
  Tactic Notation "iApplyHyp" constr(H) :=
    first
      [iApplyHypExact H
      |iApplyHypLoop H
      |lazymatch iTypeOf H with
        | Some (_,?Q) => fail 1 "iApply: cannot apply" Q
        end].

  (* Elpi Trace Browser. *)
  Local Lemma twp2_pre_proper_mono :
  twp2_proper twp2_pre.
  Proof.
    unfold twp2_proper.
    elpi IProper_solver debug.
    (* pm_reduce.
    iPoseProof (iProper (□> .> .> bi_wand ==> .> bi_wand) (@big_opL (iProp Σ) bi_sep bi_sep_monoid (expr Λ))) as "H".
    iSpecialize ("H" with "[]").
    2: {
      eapply tac_assumption with "H" _ _.
      {pm_reflexivity. }
      {tc_solve. }
      {pm_reduce. tc_solve. }
    }
    Undo 4.
    notypeclasses refine (tac_specialize_assert_no_am _ (INamed "H") _ false [] _ _ _ _ _ _ _ _ _).
    {pm_reflexivity. }
    {tc_solve. }
    {tc_solve. }
    pm_reduce.
    refine (conj _ _).
    2: {
      notypeclasses refine (tac_apply _ (INamed "H") _ _ _ _ _ _ _).
      {pm_reflexivity. }
      {tc_solve. }
    } *)
  Qed.

  Definition twp_pre `{!irisGS_gen hlc Λ Σ} (s : stuckness)
      (wp : coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ) :
    coPset → expr Λ → (val Λ → iProp Σ) → iProp Σ := λ E e1 Φ,
  match to_val e1 with
  | Some v => |={E}=> Φ v
  | None => ∀ σ1 ns κs nt,
     state_interp σ1 ns κs nt ={E,∅}=∗
       ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
       ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
         ⌜κ = []⌝ ∗
         state_interp σ2 (S ns) κs (length efs + nt) ∗
         wp E e2 Φ ∗
         [∗ list] ef ∈ efs, wp ⊤ ef fork_post
  end%I.

End TWP.