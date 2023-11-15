From elpi Require Import elpi.

From iris.bi Require Import fixpoint big_op.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.

From eIris.proofmode Require Import inductive.

Section TWP.

  Context `{!irisGS_gen hlc Λ Σ}.

  #[noproper]
  EI.ind
  Inductive twp2 : stuckness -> coPset -> expr Λ -> (val Λ -> iProp Σ) -> iProp Σ :=
    | twp2_some E v e1 Φ s : (|={E}=> Φ v) -∗ ⌜to_val e1 = Some v⌝ -∗ twp2 s E e1 Φ
    | twp2_none E e1 Φ s : (∀ σ1 ns κs nt,
                    state_interp σ1 ns κs nt ={E,∅}=∗
                      ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
                      ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
                        ⌜κ = []⌝ ∗
                        state_interp σ2 (S ns) κs (length efs + nt) ∗
                        twp2 s E e2 Φ ∗
                        [∗ list] ef ∈ efs, twp2 s ⊤ ef fork_post) -∗ ⌜to_val e1 = None⌝ 
                          -∗ twp2 s E e1 Φ.

  (* Elpi Trace Browser. *)
  Local Lemma twp2_pre_proper_mono :
  twp2_proper twp2_pre.
  Proof.
    unfold twp2_proper.
    elpi IProper_solver debug.
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