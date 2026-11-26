module

public import Mathlib

/-!
# A counterexample to Chowla's cosine conjecture

For a finite set `A` of positive integers write `f_A(t) = ∑_{a ∈ A} cos(2π a t)`.
Chowla conjectured in 1965 (S. Chowla, *Some applications of a method of A. Selberg*,
J. Reine Angew. Math. 217 (1965), 128–132, p. 130, eq. (14)) that there is an absolute
constant `c > 0` such that every nonempty `A` satisfies `min_t f_A(t) < -c √|A|`.
This is Erdős Problem #510.

This file states two results; both are proved in `Solution.lean`.

* `Erdos510.erdos_510`: the negation of the statement `Erdos510.erdos_510` of Erdős Problem
  #510 in Google DeepMind's formal-conjectures repository, copied verbatim from
  `FormalConjectures/ErdosProblems/510.lean` at commit
  `7db2ea3b91bfbd0ab620215163e6c488bbb916d5`. As in that repository's convention for
  disproved problems, the theorem keeps its name and its statement is negated. The angle is
  `θ = 2πt`, and `A : Finset ℕ` with `0 ∉ A` is a set of positive integers.
* `cosine_counterexample`: for every `ε > 0` there are arbitrarily large finite sets `A` of
  positive integers with `f_A(t) > -ε √|A|` for every real `t`. Here the cosine sum is
  written out inline, with `a : ℕ+` cast to `ℝ` through `ℕ`.
-/

@[expose] public section

namespace Erdos510

open Real Filter
open scoped Finset

/-- **Erdős Problem 510 (Chowla's cosine problem) has a negative answer.** There is no
constant `c > 0` such that, for all sufficiently large `N`, every set `A` of `N` positive
integers admits a real `θ` with `∑_{n ∈ A} cos(nθ) < -c √N`. -/
theorem erdos_510 :
    ¬ ∃ (c : ℝ) (hc : 0 < c),
      ∀ᶠ N in atTop, ∀ (A : Finset ℕ), 0 ∉ A → #A = N →
      ∃ θ, ∑ n ∈ A, cos (n * θ) < -c * sqrt N := by
  sorry

end Erdos510

/-- **Theorem 1.** For every `ε > 0` and every `N` there is a finite set `A` of positive
integers with `|A| ≥ N` such that `∑_{a ∈ A} cos(2π a t) > -ε √|A|` for every real `t`. -/
theorem cosine_counterexample (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ A : Finset ℕ+, N ≤ A.card ∧
      ∀ t : ℝ, -ε * Real.sqrt (A.card : ℝ) <
        ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * t) := by
  sorry
