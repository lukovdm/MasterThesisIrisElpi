From elpi Require Import elpi.

From iris.bi Require Import fixpoint big_op.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre.
From iris.prelude Require Import options.
Import uPred.

From iris.proofmode Require Import base environments proofmode tactics coq_tactics reduction intro_patterns class_instances spec_patterns.


From eIris.proofmode Require Import base inductive intros.

EI.ind
Inductive twp `{!irisGS_gen hlc Λ Σ} (s : stuckness) : coPset -> expr Λ -> (val Λ -d> iProp Σ) -n> iProp Σ :=
  | twp_some E v e1 Φ : (|={E}=> Φ v) -∗ ⌜to_val e1 = Some v⌝ -∗ twp s E e1 Φ
  | twp_none E e1 Φ : (∀ σ1 ns κs nt,
                        state_interp σ1 ns κs nt ={E,∅}=∗
                          ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
                          ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
                            ⌜κ = []⌝ ∗
                            state_interp σ2 (S ns) κs (length efs + nt) ∗
                            twp s E e2 Φ ∗
                            [∗ list] ef ∈ efs, twp s ⊤ ef fork_post) 
                        -∗ ⌜to_val e1 = None⌝ 
                        -∗ twp s E e1 Φ.

Arguments twp {hlc Λ Σ _} _ _ _ _.

  (* EI.ind
  Inductive twp' (s : stuckness) : coPset -> expr Λ -> (val Λ -d> iProp Σ) -n> (val Λ -d> iProp Σ) -n> iProp Σ :=
    | twp'_some E v e1 Φ Φ1 : (|={E}=> Φ v) -∗ ⌜to_val e1 = Some v⌝ -∗ twp' s E e1 Φ Φ1
    | twp'_none E e1 Φ Φ1 : (∀ σ1 ns κs nt,
                          state_interp σ1 ns κs nt ={E,∅}=∗
                            ⌜if s is NotStuck then reducible_no_obs e1 σ1 else True⌝ ∗
                            ∀ κ e2 σ2 efs, ⌜prim_step e1 σ1 κ e2 σ2 efs⌝ ={∅,E}=∗
                              ⌜κ = []⌝ ∗
                              state_interp σ2 (S ns) κs (length efs + nt) ∗
                              twp' s E e2 Φ Φ1 ∗
                              [∗ list] ef ∈ efs, twp' s ⊤ ef Φ1 Φ1) 
                          -∗ ⌜to_val e1 = None⌝ 
                          -∗ twp' s E e1 Φ Φ1. *)

Global Instance twp_ne' `{!irisGS_gen hlc Λ Σ} s E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (twp s E e).
Proof.
  solve_proper.
Qed.

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


(* Texan triples *)
Notation "'[[{' P } ] ] e @ s ; E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPE e @ s; E [{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ E [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPE e @ E [{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  E  '/' [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ E ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPE e @ E ?[{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  E  '/' ? [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPE e [{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' [[{  '[hv' x  ..  y ,  RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e ? [[{ x .. y , 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ,
      P -∗ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WPE e ?[{ Φ }])%I
    (at level 20, x closed binder, y closed binder,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' ? [[{  '[hv' x  ..  y ,   RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.

Notation "'[[{' P } ] ] e @ s ; E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WPE e @ s; E [{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  '[' s ;  '/' E  ']' '/' [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ E [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WPE e @ E [{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  E  '/' [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e @ E ? [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WPE e @ E ?[{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' @  E  '/' ? [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WPE e [{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.
Notation "'[[{' P } ] ] e ? [[{ 'RET' pat ; Q } ] ]" :=
  (□ ∀ Φ, P -∗ (Q -∗ Φ pat%V) -∗ WPE e ?[{ Φ }])%I
    (at level 20,
     format "'[hv' [[{  '[' P  ']' } ] ]  '/  ' e  '/' ? [[{  '[hv' RET  pat ;  '/' Q  ']' } ] ] ']'") : bi_scope.

  
Section TWP_Proofs.
  Context `{!irisGS_gen hlc Λ Σ}.
  Implicit Types s : stuckness.
  Implicit Types P : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance twp_proper s E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (twp s E e).
  Proof.
    by intros Φ Φ' ?; apply equiv_dist=>n; apply twp_ne=>v; apply equiv_dist.
  Qed.


  Lemma twp_value_fupd' s E Φ v : WPE of_val v @ s; E [{ Φ }] ⊣⊢ |={E}=> Φ v.
  Proof.
    iSplit; iIntros "H".
    - eiDestruct "H" as "[% H %H | _ %H]"; rewrite to_of_val in H; by simplify_eq.
    - iApply twp_some. rewrite to_of_val. iExists _. by iFrame.
  Qed.

  Lemma twp_strong_mono s1 s2 E1 E2 e Φ Ψ :
    s1 ⊑ s2 → E1 ⊆ E2 →
    WPE e @ s1; E1 [{ Φ }] -∗ (∀ v, Φ v ={E2}=∗ Ψ v) -∗ WPE e @ s2; E2 [{ Ψ }].
  Proof.
    iIntros (? HE) "H HΦ".
    iRevert (E2 Ψ HE) "HΦ".
    eiInduction "H" as "[* IH %Htv | * IH %Htv]"; try iIntros (E2 Ψ HE) "HΦ"; 
    simplify_eq.
    - solve_proper.
    - iApply twp_some.
      iExists _.
      iSplitL; [|repeat iSplit; done].
      iApply ("HΦ" with "[> -]").
      by iApply (fupd_mask_mono _ _).
    - iApply twp_none.
      iSplitL; [|repeat iSplit; done].
      iIntros (σ1 ns κs nt) "Hσ".
      iMod (fupd_mask_subseteq _) as "Hclose"; first done.
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
    iIntros "H". destruct (to_val e) as [v|] eqn:?.
    - iApply twp_some.
      iExists v.
      repeat iSplit; try done.
      iMod "H".
      eiDestruct "H" as "[% H % | H %]"; by simplify_eq.
    - iApply twp_none.
      iSplit; [|done].
      iIntros (σ1 ns κs nt) "Hσ1". iMod "H".
      eiDestruct "H" as "[% H % | H %]"; simplify_eq.
      by iApply "H".
  Qed.

  Lemma twp_fupd s E e Φ : WPE e @ s; E [{ v, |={E}=> Φ v }] ⊢ WPE e @ s; E [{ Φ }].
  Proof. iIntros "H". iApply (twp_strong_mono with "H"); auto. Qed.

  Lemma twp_atomic s E1 E2 e Φ `{!Atomic (stuckness_to_atomicity s) e} :
    (|={E1,E2}=> WPE e @ s; E2 [{ v, |={E2,E1}=> Φ v }]) ⊢ WPE e @ s; E1 [{ Φ }].
  Proof.
    iIntros "H".
    rewrite 1!twp_unfold /twp_pre /=. destruct (to_val e) as [v|] eqn:He.
    { iApply twp_some. iExists _. iSplit; try done.
       iMod "H".
       iDestruct "H" as "[(% & H & %Hv) | (_ & %H)]"; simplify_eq; try done.
       by iDestruct "H" as ">> $". }
    iApply twp_none. iSplit; [|done].
    iIntros (σ1 ns κs nt) "Hσ". iMod "H". 
    iDestruct "H" as "[(% & _ & %Hv) | (H & %H)]"; simplify_eq; try done.
    iMod ("H" $! σ1 with "Hσ") as "[$ H]".
    iModIntro. iIntros (κ e2 σ2 efs Hstep).
    iMod ("H" with "[//]") as (?) "(Hσ & H & Hefs)". destruct s.
    - eiDestruct "H" as "[% H %Hv | H %Hv]". 
      + iDestruct "H" as ">> H". iFrame. iSplitR; try done.
        iApply twp_some. by iFrame.
      + iMod ("H" with "[$]") as "[H _]". iDestruct "H" as %(? & ? & ? & ?).
        by edestruct (atomic _ _ _ _ _ Hstep).
    - destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
      rewrite twp_value_fupd'. iMod "H" as ">H".
      iModIntro. iSplit; first done. iFrame "Hσ Hefs". by iApply twp_value_fupd'.
  Qed.

  Lemma twp_bind K `{!LanguageCtx K} s E e Φ :
    WPE e @ s; E [{ v, WPE K (of_val v) @ s; E [{ Φ }] }] ⊢ WPE K e @ s; E [{ Φ }].
  Proof.
    revert Φ. cut (∀ Φ', WPE e @ s; E [{ Φ' }] -∗ ∀ Φ,
      (∀ v, Φ' v -∗ WPE K (of_val v) @ s; E [{ Φ }]) -∗ WPE K e @ s; E [{ Φ }]).
    { iIntros (help Φ) "H". iApply (help with "H"); auto. }
    iIntros (Φ') "H". 
    eiInduction "H" as "[* IH %Htv | * IH %Htv]"; first solve_proper; iIntros (Φ'') "HΦ".
    - simplify_eq. apply of_to_val in Htv as <-. iApply fupd_twp. by iApply "HΦ".
    - iApply twp_none.
      simplify_eq.
      iSplitL.
      2: { iPureIntro. by apply fill_not_val. }
      iIntros (σ1 ns κs nt) "Hσ". iMod ("IH" with "[$]") as "[% IH]".
      iModIntro; iSplit.
      { iPureIntro. unfold reducible_no_obs in *.
        destruct s; naive_solver eauto using fill_step. }
      iIntros (κ e2 σ2 efs Hstep).
      destruct (fill_step_inv e0 σ1 κ e2 σ2 efs) as (e2'&->&?); auto.
      iMod ("IH" $! κ e2' σ2 efs with "[//]") as (?) "(Hσ & IH & IHefs)".
      iModIntro. iFrame "Hσ". iSplit; first done. iSplitR "IHefs".
      + iDestruct "IH" as "[IH _]". by iApply "IH".
      + by setoid_rewrite and_elim_r.
  Qed.

  Lemma twp_bind_inv K `{!LanguageCtx K} s E e Φ :
    WPE K e @ s; E [{ Φ }] -∗ WPE e @ s; E [{ v, WPE K (of_val v) @ s; E [{ Φ }] }].
  Proof.
    iIntros "H". remember (K e) as e' eqn:He'.
    iRevert (e He'). iRevert (E e' Φ) "H". iApply twp_ind.
    { solve_proper_prepare. do 3 (f_equiv || done). apply twp_ne'. repeat (f_equiv || done). }
    iIntros "!>" (e' E1 Φ) "IH". iIntros (e ->). destruct (to_val e) as [v|] eqn:He.
    {
      iApply twp_some. iExists _. iSplit; try done.
      iModIntro. apply of_to_val in He as <-. rewrite !twp_unfold.
      iApply (iProper _ _ (twp_pre_mono _ _ _ _ s)).
      2: done.
      by iIntros "!>" (E e Φ') "[_ ?]".
    }
    iApply twp_none. iSplit; try done.
    eiDestruct "IH" as "[%v _ %H | IH %H]"; rewrite fill_not_val // in H.
    iIntros (σ1 ns κs nt) "Hσ". iMod ("IH" with "[$]") as "[% IH]".
    iModIntro; iSplit.
    { destruct s; eauto using reducible_no_obs_fill_inv. }
    iIntros (κ e2 σ2 efs Hstep).
    iMod ("IH" $! κ (K e2) σ2 efs with "[]")
      as (?) "(Hσ & IH & IHefs)"; eauto using fill_step.
    iModIntro. iFrame "Hσ". iSplit; first done. iSplitR "IHefs".
    - iDestruct "IH" as "[IH _]". by iApply "IH".
    - by setoid_rewrite and_elim_r.
  Qed.

  Lemma twp_wp s E e Φ : WPE e @ s; E [{ Φ }] -∗ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros "H". iLöb as "IH" forall (E e Φ).
    rewrite wp_unfold /wp_pre.
    eiDestruct "H" as "[% H %He | H %He]"; rewrite He //.
    iIntros (σ1 ns κ κs nt) "Hσ". iMod ("H" with "Hσ") as "[% H]".
    iIntros "!>". iSplitR.
    { destruct s; eauto using reducible_no_obs_reducible. }
    iIntros (e2 σ2 efs) "Hstep _". iMod ("H" with "Hstep") as (->) "(Hσ & H & Hfork)".
    iApply fupd_mask_intro; [set_solver+|]. iIntros "Hclose".
    iIntros "!>!>". iApply step_fupdN_intro=>//. iModIntro. iMod "Hclose" as "_".
    iModIntro. iFrame "Hσ". iSplitL "H".
    { by iApply "IH". }
    iApply (@big_sepL_impl with "Hfork").
    iIntros "!>" (k ef _) "H". by iApply "IH".
  Qed.

  (** This lemma is similar to [wp_step_fupdN_strong], the difference is the TWP
  (instead of a WP) in the premise. Since TWPs do not use up later credits, we get
  [£ n] in the viewshift in the premise. *)
  Lemma twp_wp_fupdN_strong n s E1 E2 e P Φ :
    TCEq (to_val e) None → E2 ⊆ E1 →
    (∀ σ ns κs nt, state_interp σ ns κs nt ={E1,∅}=∗
                  ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
    ((|={E1,E2}=> £ n ={∅}▷=∗^n |={E2,E1}=> P) ∗
      WPE e @ s; E2 [{ v, P ={E1}=∗ Φ v }]) -∗
    WP e @ s; E1 {{ Φ }}.
  Proof.
    destruct n as [|n].
    { iIntros (_ ?) "/= [_ [HP Hwp]]".
      iApply (wp_strong_mono with "[Hwp]"); [done..|by iApply twp_wp|]; simpl.
      iIntros (v) "H". iApply ("H" with "[>HP]"). iMod "HP".
      iMod lc_zero as "Hlc". by iApply "HP". }
    rewrite wp_unfold twp_unfold /wp_pre /twp_pre. iIntros (-> ?) "H".
    iIntros (σ1 ns κ κs nt) "Hσ".
    destruct (decide (n ≤ num_laters_per_step ns)) as [Hn|Hn]; first last.
    { iDestruct "H" as "[Hn _]". iMod ("Hn" with "Hσ") as %?. lia. }
    iDestruct "H" as "[_ [>HP [(% & H & %H')|(Hwp & _ )]]]"; try done. iMod ("Hwp" with "[$]") as "[% H]".
    iIntros "!>". iSplitR.
    { destruct s; eauto using reducible_no_obs_reducible. }
    iIntros (e2 σ2 efs Hstep) "Hcred /=".
    iDestruct ("H" $! κ e2 σ2 efs with "[% //]") as "H".
    iMod ("HP" with "[Hcred]") as "HP".
    { iApply (lc_weaken with "Hcred"); lia. }
    iIntros "!> !>". iMod "HP". iModIntro.
    iApply step_fupdN_le; [apply Hn|done|..].
    iApply (step_fupdN_wand with "HP"); iIntros "HP".
    iMod "H" as (->) "($ & Hwp & Hfork)". iMod "HP". iModIntro. iSplitR "Hfork".
    - iApply twp_wp. iApply (twp_strong_mono with "Hwp"); [done|set_solver|].
      iIntros (v) "HΦ". iApply ("HΦ" with "HP").
    - iApply (big_sepL_impl with "Hfork").
      iIntros "!>" (k ef _) "H". by iApply twp_wp.
  Qed.

  (** * Derived rules *)
  Lemma twp_mono s E e Φ Ψ :
    (∀ v, Φ v ⊢ Ψ v) → WPE e @ s; E [{ Φ }] ⊢ WPE e @ s; E [{ Ψ }].
  Proof.
    iIntros (HΦ) "H"; iApply (twp_strong_mono with "H"); auto.
    iIntros (v) "?". by iApply HΦ.
  Qed.
  Lemma twp_stuck_mono s1 s2 E e Φ :
    s1 ⊑ s2 → WPE e @ s1; E [{ Φ }] ⊢ WPE e @ s2; E [{ Φ }].
  Proof. iIntros (?) "H". iApply (twp_strong_mono with "H"); auto. Qed.
  Lemma twp_stuck_weaken s E e Φ :
    WPE e @ s; E [{ Φ }] ⊢ WPE e @ E ?[{ Φ }].
  Proof. apply twp_stuck_mono. by destruct s. Qed.
  Lemma twp_mask_mono s E1 E2 e Φ :
    E1 ⊆ E2 → WPE e @ s; E1 [{ Φ }] -∗ WPE e @ s; E2 [{ Φ }].
  Proof. iIntros (?) "H"; iApply (twp_strong_mono with "H"); auto. Qed.
  Global Instance twp_mono' s E e :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (twp s E e).
  Proof. by intros Φ Φ' ?; apply twp_mono. Qed.

  Lemma twp_value_fupd s E Φ e v : IntoVal e v → WPE e @ s; E [{ Φ }] ⊣⊢ |={E}=> Φ v.
  Proof. intros <-. by apply twp_value_fupd'. Qed.
  Lemma twp_value' s E Φ v : Φ v ⊢ WPE (of_val v) @ s; E [{ Φ }].
  Proof. rewrite twp_value_fupd'. auto. Qed.
  Lemma twp_value s E Φ e v : IntoVal e v → Φ v ⊢ WPE e @ s; E [{ Φ }].
  Proof. intros <-. apply twp_value'. Qed.

  Lemma twp_frame_l s E e Φ R : R ∗ WPE e @ s; E [{ Φ }] ⊢ WPE e @ s; E [{ v, R ∗ Φ v }].
  Proof. iIntros "[? H]". iApply (twp_strong_mono with "H"); auto with iFrame. Qed.
  Lemma twp_frame_r s E e Φ R : WPE e @ s; E [{ Φ }] ∗ R ⊢ WPE e @ s; E [{ v, Φ v ∗ R }].
  Proof. iIntros "[H ?]". iApply (twp_strong_mono with "H"); auto with iFrame. Qed.

  Lemma twp_wand s E e Φ Ψ :
    WPE e @ s; E [{ Φ }] -∗ (∀ v, Φ v -∗ Ψ v) -∗ WPE e @ s; E [{ Ψ }].
  Proof.
    iIntros "H HΦ". iApply (twp_strong_mono with "H"); auto.
    iIntros (?) "?". by iApply "HΦ".
  Qed.
  Lemma twp_wand_l s E e Φ Ψ :
    (∀ v, Φ v -∗ Ψ v) ∗ WPE e @ s; E [{ Φ }] -∗ WPE e @ s; E [{ Ψ }].
  Proof. iIntros "[H Hwp]". iApply (twp_wand with "Hwp H"). Qed.
  Lemma twp_wand_r s E e Φ Ψ :
    WPE e @ s; E [{ Φ }] ∗ (∀ v, Φ v -∗ Ψ v) -∗ WPE e @ s; E [{ Ψ }].
  Proof. iIntros "[Hwp H]". iApply (twp_wand with "Hwp H"). Qed.
  Lemma twp_frame_wand s E e Φ R :
    R -∗ WPE e @ s; E [{ v, R -∗ Φ v }] -∗ WPE e @ s; E [{ Φ }].
  Proof.
    iIntros "HR HWP". iApply (twp_wand with "HWP").
    iIntros (v) "HΦ". by iApply "HΦ".
  Qed.

  Lemma twp_wp_step s E e P Φ :
    TCEq (to_val e) None →
    ▷ P -∗
    WPE e @ s; E [{ v, P ={E}=∗ Φ v }] -∗ WP e @ s; E {{ Φ }}.
  Proof.
    iIntros (?) "HP Hwp".
    iApply (wp_step_fupd _ _ E _ P with "[HP]"); [auto..|]. by iApply twp_wp.
  Qed.
End TWP_Proofs.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{!irisGS_gen hlc Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.
  Implicit Types v : val Λ.
  Implicit Types e : expr Λ.

  Global Instance frame_twp p s E e R Φ Ψ :
    (FrameInstantiateExistDisabled → ∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (WPE e @ s; E [{ Φ }]) (WPE e @ s; E [{ Ψ }]) | 2.
  Proof.
    rewrite /Frame=> HR. rewrite twp_frame_l. apply twp_mono, HR. constructor.
  Qed.

  Global Instance is_except_0_wp s E e Φ : IsExcept0 (WPE e @ s; E [{ Φ }]).
  Proof. by rewrite /IsExcept0 -{2}fupd_twp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_twp p s E e P Φ :
    ElimModal True p false (|==> P) P (WPE e @ s; E [{ Φ }]) (WPE e @ s; E [{ Φ }]).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_twp.
  Qed.

  Global Instance elim_modal_fupd_twp p s E e P Φ :
    ElimModal True p false (|={E}=> P) P (WPE e @ s; E [{ Φ }]) (WPE e @ s; E [{ Φ }]).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_twp.
  Qed.
  (** Error message instance for non-mask-changing view shifts.
  Also uses a slightly different error: we cannot apply [fupd_mask_subseteq]
  if [e] is not atomic, so we tell the user to first add a leading [fupd]
  and then change the mask of that. *)
  Global Instance elim_modal_fupd_twp_wrong_mask p s E1 E2 e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
Use [iApply fupd_twp; iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2}=> P) False (WPE e @ s; E1 [{ Φ }]) False | 100.
  Proof. intros []. Qed.

  Global Instance elim_modal_fupd_twp_atomic p s E1 E2 e P Φ :
    ElimModal (Atomic (stuckness_to_atomicity s) e) p false
            (|={E1,E2}=> P) P
            (WPE e @ s; E1 [{ Φ }]) (WPE e @ s; E2 [{ v, |={E2,E1}=> Φ v }])%I | 100.
  Proof.
    intros ?. by rewrite intuitionistically_if_elim
      fupd_frame_r wand_elim_r twp_atomic.
  Qed.
  (** Error message instance for mask-changing view shifts. *)
  Global Instance elim_modal_fupd_twp_atomic_wrong_mask p s E1 E2 E2' e P Φ :
    ElimModal
      (pm_error "Goal and eliminated modality must have the same mask.
  Use [iMod (fupd_mask_subseteq E2)] to adjust the mask of your goal to [E2]")
      p false
      (|={E2,E2'}=> P) False
      (WPE e @ s; E1 [{ Φ }]) False | 200.
  Proof. intros []. Qed.

  Global Instance add_modal_fupd_twp s E e P Φ :
    AddModal (|={E}=> P) P (WPE e @ s; E [{ Φ }]).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_twp. Qed.

  Global Instance elim_acc_twp_atomic {X} E1 E2 α β γ e s Φ :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity s) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (WPE e @ s; E1 [{ Φ }])
            (λ x, WPE e @ s; E2 [{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) }])%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (twp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed.
End proofmode_classes.
