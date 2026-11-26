module

public import Mathlib
import ChowlaOpus.Main

/-!
# Proofs of the statements in `Challenge.lean`

`cosine_counterexample` is `ChowlaOpus.main_theorem`, assembled in `ChowlaOpus/Main.lean`
from the components in `ChowlaOpus/Parts/`. `ChowlaOpus.cosineSum A t` is by definition
`∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * t)`.
-/

@[expose] public section

theorem cosine_counterexample (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ A : Finset ℕ+, N ≤ A.card ∧
      ∀ t : ℝ, -ε * Real.sqrt (A.card : ℝ) <
        ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * t) :=
  ChowlaOpus.main_theorem ε hε N

theorem chowla_cosine_conjecture_false :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ A : Finset ℕ+, A.Nonempty →
      ∃ t : ℝ, ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * t) <
        -c * Real.sqrt (A.card : ℝ) := by
  rintro ⟨c, hc, h⟩
  obtain ⟨A, hcard, hA⟩ := cosine_counterexample c hc 1
  obtain ⟨t, ht⟩ := h A (Finset.card_pos.mp (by omega))
  exact lt_asymm ht (hA t)
