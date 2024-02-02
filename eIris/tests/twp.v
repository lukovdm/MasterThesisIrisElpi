From elpi Require Import elpi.

From iris.bi Require Import fixpoint big_op.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris.proofmode Require Import base environments proofmode tactics coq_tactics reduction intro_patterns class_instances spec_patterns.


From eIris.proofmode Require Import base inductive intros.

Section TWP.

  Context `{!irisGS_gen hlc Λ Σ}.

  EI.ind
  Inductive twp (s : stuckness) : coPset -> expr Λ -> (val Λ -> iProp Σ) -> iProp Σ :=
    | twp_some E v e1 Φ : (|={E}=> Φ v) -∗ ⌜to_val e1 = Some v⌝ -∗ twp s E e1 Φ
    | twp_none E e1 Φ : (∀ σ1 ns κs nt,
                    state_interp σ1 ns κs nt ={E,∅}=∗
                      ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
                      ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
                        ⌜κ = []⌝ ∗
                        state_interp σ2 (S ns) κs (length efs + nt) ∗
                        twp s E e2 Φ ∗
                        [∗ list] ef ∈ efs, twp s ⊤ ef fork_post) -∗ ⌜to_val e1 = None⌝ 
                          -∗ twp s E e1 Φ.

  Notation "'WPE' e @ s ; E [{ Φ } ]" := (twp s E e%E Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'WPE' e @ E [{ Φ } ]" := (twp NotStuck E e%E Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'WPE' e @ E ? [{ Φ } ]" := (twp MaybeStuck E e%E Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'WPE' e [{ Φ } ]" := (twp NotStuck ⊤ e%E Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'WPE' e ? [{ Φ } ]" := (twp MaybeStuck ⊤ e%E Φ)
    (at level 20, e, Φ at level 200, only parsing) : bi_scope.
  Notation "'WPE' e @ s ; E [{ v , Q } ]" := (twp s E e%E (λ v, Q))
    (at level 20, e, Q at level 200,
     format "'[hv' 'WPE'  e  '/' @  '[' s ;  '/' E  ']' '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
  Notation "'WPE' e @ E [{ v , Q } ]" := (twp NotStuck E e%E (λ v, Q))
    (at level 20, e, Q at level 200,
     format "'[hv' 'WPE'  e  '/' @  E  '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
  Notation "'WPE' e @ E ? [{ v , Q } ]" := (twp MaybeStuck E e%E (λ v, Q))
    (at level 20, e, Q at level 200,
     format "'[hv' 'WPE'  e  '/' @  E  '/' ? [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
  Notation "'WPE' e [{ v , Q } ]" := (twp NotStuck ⊤ e%E (λ v, Q))
    (at level 20, e, Q at level 200,
     format "'[hv' 'WPE'  e  '/' [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
  Notation "'WPE' e ? [{ v , Q } ]" := (twp MaybeStuck ⊤ e%E (λ v, Q))
    (at level 20, e, Q at level 200,
     format "'[hv' 'WPE'  e  '/' ? [{  '[' v ,  '/' Q  ']' } ] ']'") : bi_scope.
  
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Lemma twp_strong_mono s1 s2 E1 E2 e Φ Ψ :
    s1 ⊑ s2 → E1 ⊆ E2 →
    WPE e @ s1; E1 [{ Φ }] -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WPE e @ s2; E2 [{ Ψ }].
  Proof.
    iIntros (? HE) "H HΦ". iRevert (E2 Ψ HE) "HΦ".
    eiInduction "H" as "[* IH %Htv [%Ha %Hb] %HaPhi | * IH %Htv [%Ha %Hb] %HaPhi]"; iIntros (E2 Ψ HE) "HΦ"; 
    simplify_eq.
    - iApply twp_some.
      iExists _, _, _, _.
      iSplitL; [|repeat iSplit; done].
      iApply ("HΦ" with "[> -]").
      by iApply (fupd_mask_mono E _).
    - iApply twp_none.
      iExists _, _, _.
      iSplitL; [|repeat iSplit; done].
      iIntros (σ1 ns κs nt) "Hσ".
      iMod (fupd_mask_subseteq E) as "Hclose"; first done.
      iMod ("IH" with "[$]") as "[% IH]".
      iModIntro; iSplit; [by destruct s1, s2|]. iIntros (κ e2 σ2 efs Hstep).
      iMod ("IH" with "[//]") as (?) "(Hσ & IH & IHefs)"; auto.
      iMod "Hclose" as "_"; iModIntro.
      iFrame "Hσ". iSplit; first done. iSplitR "IHefs".
      + iDestruct "IH" as "[IH _]". iApply ("IH" with "[//] HΦ").
      + iApply (big_sepL_impl with "IHefs"); iIntros "!>" (k ef _) "[IH _]".
        iApply "IH"; auto.
  Qed. 

  Lemma fupd_twp s E e Φ : (|={E}=> WPE e @ s; E [{ Φ }]) ⊢ WPE e @ s; E [{ Φ }].
  Proof.
  Admitted.
  Lemma twp_fupd s E e Φ : WPE e @ s; E [{ v, |={E}=> Φ v }] ⊢ WPE e @ s; E [{ Φ }].
  Proof.
  Admitted.

  Lemma twp_bind K `{!LanguageCtx K} s E e Φ :
    WPE e @ s; E [{ v, WPE K (of_val v) @ s; E [{ Φ }] }] ⊢ WPE K e @ s; E [{ Φ }].
  Proof.
    revert Φ. cut (∀ Φ', WPE e @ s; E [{ Φ' }] -∗ ∀ Φ,
      (∀ v, Φ' v -∗ WPE K (of_val v) @ s; E [{ Φ }]) -∗ WPE K e @ s; E [{ Φ }]).
    { iIntros (help Φ) "H". iApply (help with "H"); auto. }
    iIntros (Φ') "H". 
    eiInduction "H" as "[* IH %Htv [%Ha %Hb] %HaPhi | * IH %Htv [%Ha %Hb] %HaPhi]"; iIntros (Φ'') "HΦ".
    - simplify_eq. apply of_to_val in Htv as <-. iApply fupd_twp. by iApply "HΦ".
    - iApply twp_none.
      iExists _, (K e1), _.
      simplify_eq.
      iSplitL; [|repeat iSplit; try done].
      2: { iPureIntro. by apply fill_not_val. }
      iIntros (σ1 ns κs nt) "Hσ". iMod ("IH" with "[$]") as "[% IH]".
      iModIntro; iSplit.
      { iPureIntro. unfold reducible_no_obs in *.
        destruct s; naive_solver eauto using fill_step. }
      iIntros (κ e2 σ2 efs Hstep).
      destruct (fill_step_inv e1 σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
      iMod ("IH" $! κ e2' σ2 efs with "[//]") as (?) "(Hσ & IH & IHefs)".
      iModIntro. iFrame "Hσ". iSplit; first done. iSplitR "IHefs".
      + iDestruct "IH" as "[IH _]". by iApply "IH".
      + by setoid_rewrite and_elim_r.
  Qed.

End TWP.