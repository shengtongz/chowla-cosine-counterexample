module

public import Mathlib
import ChowlaOpus.Main

/-!
# Proofs of the statements in `Challenge.lean`

`cosine_counterexample` is `ChowlaOpus.main_theorem`, assembled in `ChowlaOpus/Main.lean`
from the components in `ChowlaOpus/Parts/`. `ChowlaOpus.cosineSum A t` is by definition
`∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * t)`.

`Erdos510.erdos_510` follows from Theorem 1 with `ε = c`: the resulting set has at least the
threshold size, and the substitution `θ = 2πt` identifies the two cosine sums.
-/

@[expose] public section

namespace Erdos510

open Real Filter
open scoped Finset

set_option linter.unusedVariables false in
theorem erdos_510 :
    ¬ ∃ (c : ℝ) (hc : 0 < c),
      ∀ᶠ N in atTop, ∀ (A : Finset ℕ), 0 ∉ A → #A = N →
      ∃ θ, ∑ n ∈ A, cos (n * θ) < -c * sqrt N := by
  rintro ⟨c, hc, h⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  obtain ⟨A, hcard, hA⟩ := ChowlaOpus.main_theorem c hc N₀
  obtain ⟨θ, hθ⟩ := hN₀ A.card hcard (A.map ⟨PNat.val, PNat.coe_injective⟩)
    (by simp) (by simp)
  have key : -c * Real.sqrt (A.card : ℝ) <
      ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * (θ / (2 * π))) :=
    hA (θ / (2 * π))
  have hsum : ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * (θ / (2 * π))) =
      ∑ n ∈ A.map ⟨PNat.val, PNat.coe_injective⟩, cos (n * θ) := by
    simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hπ : π ≠ 0 := Real.pi_ne_zero
    congr 1
    field_simp
  linarith

end Erdos510

theorem cosine_counterexample (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ A : Finset ℕ+, N ≤ A.card ∧
      ∀ t : ℝ, -ε * Real.sqrt (A.card : ℝ) <
        ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * t) :=
  ChowlaOpus.main_theorem ε hε N
