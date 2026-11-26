module

public import Mathlib

/-!
# A counterexample to Chowla's cosine conjecture

For a finite set `A` of positive integers write `f_A(t) = ∑_{a ∈ A} cos(2π a t)`.
Chowla conjectured in 1965 (S. Chowla, *Some applications of a method of A. Selberg*,
J. Reine Angew. Math. 217 (1965), 128–132, p. 130, eq. (14)) that there is an absolute
constant `c > 0` such that every nonempty `A` satisfies `min_t f_A(t) < -c √|A|`.

This file states two results; both are proved in `Solution.lean`.

* `cosine_counterexample`: for every `ε > 0` there are arbitrarily large finite sets `A` of
  positive integers with `f_A(t) > -ε √|A|` for every real `t`.
* `chowla_cosine_conjecture_false`: the negation of Chowla's conjecture in the form above.
  Since `f_A` is continuous and `1`-periodic, `min_t f_A(t) < -c √|A|` is equivalent to the
  existence of a real `t` with `f_A(t) < -c √|A|`, which is how the conjecture is stated here.

The cosine sum is written out inline, with `a : ℕ+` cast to `ℝ` through `ℕ`.
-/

@[expose] public section

/-- **Theorem 1.** For every `ε > 0` and every `N` there is a finite set `A` of positive
integers with `|A| ≥ N` such that `∑_{a ∈ A} cos(2π a t) > -ε √|A|` for every real `t`. -/
theorem cosine_counterexample (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ A : Finset ℕ+, N ≤ A.card ∧
      ∀ t : ℝ, -ε * Real.sqrt (A.card : ℝ) <
        ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * t) := by
  sorry

/-- **Chowla's cosine conjecture is false.** There is no constant `c > 0` such that every
nonempty finite set `A` of positive integers admits a real `t` with
`∑_{a ∈ A} cos(2π a t) < -c √|A|`. -/
theorem chowla_cosine_conjecture_false :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ A : Finset ℕ+, A.Nonempty →
      ∃ t : ℝ, ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * t) <
        -c * Real.sqrt (A.card : ℝ) := by
  sorry
