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

  EI.ind
  Inductive twp2 (s : stuckness) : coPset -> expr Λ -> (val Λ -> iProp Σ) -> iProp Σ :=
    | twp2_some E v e1 Φ : (|={E}=> Φ v) -∗ ⌜to_val e1 = Some v⌝ -∗ twp2 s E e1 Φ
    | twp2_none E e1 Φ : (∀ σ1 ns κs nt,
                    state_interp σ1 ns κs nt ={E,∅}=∗
                      ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
                      ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
                        ⌜κ = []⌝ ∗
                        state_interp σ2 (S ns) κs (length efs + nt) ∗
                        twp2 s E e2 Φ ∗
                        [∗ list] ef ∈ efs, twp2 s ⊤ ef fork_post) -∗ ⌜to_val e1 = None⌝ 
                          -∗ twp2 s E e1 Φ.

End TWP.