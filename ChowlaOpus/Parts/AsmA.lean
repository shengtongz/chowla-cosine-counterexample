module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

theorem lemma3Statement_holds (hBump : BumpStatement) (hC : CoeffStatement)
    (hCM : CoeffMassStatement) (hWb : WboundStatement) (hQ : QposStatement)
    (hV : VarStatement) : Lemma3Statement := by
  obtain ⟨ρ, hρ⟩ := hBump
  obtain ⟨C₁, c, T₁, hC₁, hc, hmass⟩ := hCM ρ hρ
  obtain ⟨C₂, T₂, hC₂, hvar⟩ := hV ρ hρ
  refine ⟨max C₁ C₂, c, lt_max_of_lt_left hC₁, hc, max (max T₁ T₂) 1, ?_⟩
  intro T hT
  have hT₁ : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT₂ : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hT
  have hTpos : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T / T := div_nonneg (Real.log_nonneg hT1) hTpos.le
  have hlogT3 : 0 ≤ Real.log T / T ^ 3 := div_nonneg (Real.log_nonneg hT1) (by positivity)
  set J : ℕ := ⌈T ^ 8⌉₊ with hJ
  have hJ8 : T ^ 8 ≤ (J : ℝ) := Nat.le_ceil _
  refine ⟨J, bL ρ T J, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    exact (hC ρ hρ T hT1 J l).2.2.2.2.2 hl
  · intro l
    exact (hC ρ hρ T hT1 J l).1
  · intro l x hx
    exact (hC ρ hρ T hT1 J l).2.1 x hx
  · intro l x
    exact (hC ρ hρ T hT1 J l).2.2.1 x
  · intro l x
    exact (hC ρ hρ T hT1 J l).2.2.2.1 x
  · intro x
    exact (hC ρ hρ T hT1 J 0).2.2.2.2.1 x
  · intro y
    exact (hQ ρ hρ T hT1 J).2 y
  · exact (hmass T hT₁ J).1
  · calc ∑' j : ℤ, (bL ρ T J 0 j).re ≤ C₁ * Real.log T / T := (hmass T hT₁ J).2.1
      _ = C₁ * (Real.log T / T) := by ring
      _ ≤ max C₁ C₂ * (Real.log T / T) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hlogT
      _ = max C₁ C₂ * Real.log T / T := by ring
  · exact (hmass T hT₁ J).2.2
  · intro s x
    have h := hWb ρ hρ T hT1 J s x
    simpa only [Wsum] using h
  · intro s y
    exact (hQ ρ hρ T hT1 J).1 s y
  · calc ∫ x, ((bL ρ T J 0 x).re - ∑ l ∈ Finset.Icc (-(J : ℤ)) J, ‖bL ρ T J l x‖ ^ 2)
        ≤ C₂ * Real.log T / T ^ 3 := hvar T hT₂ J hJ8
      _ = C₂ * (Real.log T / T ^ 3) := by ring
      _ ≤ max C₁ C₂ * (Real.log T / T ^ 3) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hlogT3
      _ = max C₁ C₂ * Real.log T / T ^ 3 := by ring

end ChowlaOpus
