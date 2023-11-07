From iris.bi Require Import fixpoint big_op.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.prelude Require Import options.

From eIris.proofmode Require Import inductive.

Section TWP.

  Context `{!irisGS_gen hlc Λ Σ}.

  EI.ind 
  Inductive twp2 : coPset -> expr Λ -> (val Λ → iProp Σ) -> iProp Σ :=
    twp2_some : |={E}=> Φ v -∗ twp2 E (Some v) Φ.

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