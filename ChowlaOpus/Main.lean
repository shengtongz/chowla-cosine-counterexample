module

public import ChowlaOpus.Parts.Fejer
public import ChowlaOpus.Parts.Bump
public import ChowlaOpus.Parts.J0
public import ChowlaOpus.Parts.Mellin
public import ChowlaOpus.Parts.Annulus
public import ChowlaOpus.Parts.Coeff
public import ChowlaOpus.Parts.W
public import ChowlaOpus.Parts.Q
public import ChowlaOpus.Parts.Var
public import ChowlaOpus.Parts.AsmA
public import ChowlaOpus.Parts.Saw
public import ChowlaOpus.Parts.Aux3
public import ChowlaOpus.Parts.Poisson
public import ChowlaOpus.Parts.Gauss
public import ChowlaOpus.Parts.KChar
public import ChowlaOpus.Parts.Phase
public import ChowlaOpus.Parts.CRT
public import ChowlaOpus.Parts.W9
public import ChowlaOpus.Parts.W10
public import ChowlaOpus.Parts.AsmB
public import ChowlaOpus.Parts.Partial
public import ChowlaOpus.Parts.Spencer
public import ChowlaOpus.Parts.Mesh
public import ChowlaOpus.Parts.Rounding
public import ChowlaOpus.Parts.MainOf

@[expose] public section

/-!
# Theorem 1: a counterexample to Chowla's cosine conjecture
-/

namespace ChowlaOpus

theorem lemma3_final : Lemma3Statement :=
  lemma3Statement_holds bumpStatement_holds
    (coeffStatement_holds annulusStatement_holds)
    (coeffMassStatement_holds annulusStatement_holds)
    (wboundStatement_holds annulusStatement_holds fejerStatement_holds)
    (qposStatement_holds j0Statement_holds besselPlaneStatement_holds multStatement_holds
      (mellinStatement_holds j0Statement_holds besselPlaneStatement_holds)
      annulusStatement_holds fejerStatement_holds)
    (varStatement_holds annulusStatement_holds fejerStatement_holds
      (wrepStatement_holds annulusStatement_holds fejerStatement_holds)
      (wboundStatement_holds annulusStatement_holds fejerStatement_holds))

theorem profile_final : ProfileStatement :=
  profileStatement_holds lemma3_final sawStatement_holds fejerStatement_holds
    fourierDecayStatement_holds

theorem weights_final : WeightsStatement :=
  weightsStatement_holds profile_final crtStatement_holds
    (phaseStatement_holds kernelCharStatement_holds) rowSumStatement_holds multStatement_holds
    (w9Statement_holds rowSumStatement_holds poissonStatement_holds
      plainPoissonStatement_holds multStatement_holds)
    (w10Statement_holds rowSumStatement_holds poissonStatement_holds
      fourierDecayStatement_holds)

theorem rounding_final : RoundingStatement :=
  roundingStatement_holds (spencerStatement_holds partialColoringStatement_holds)
    meshStatement_holds

/-- **Theorem 1.** For every `ε > 0` there are arbitrarily large finite sets `A` of positive
integers with `f_A(t) > -ε √|A|` for every real `t`. -/
theorem main_theorem (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ A : Finset ℕ+, N ≤ A.card ∧ ∀ t : ℝ, -ε * Real.sqrt (A.card : ℝ) < cosineSum A t :=
  cosine_counterexample_of weights_final rounding_final ε hε N

end ChowlaOpus
