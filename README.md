# A counterexample to Chowla's cosine conjecture, in Lean

This repository is a complete Lean 4 / Mathlib formalization of a counterexample to
Chowla's cosine conjecture, following the manuscript *A prime-square counterexample to
Chowla's cosine conjecture* (unpublished at the time of writing).

The proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`, and contain no
`sorry`.

## The statements

For a finite set `A` of positive integers write

  f_A(t) = ∑_{a ∈ A} cos(2π a t).

Chowla conjectured in 1965 (S. Chowla, *Some applications of a method of A. Selberg*,
J. Reine Angew. Math. 217 (1965), 128–132, p. 130, eq. (14)) that there is an absolute
constant `c > 0` such that every nonempty `A` satisfies `min_t f_A(t) < -c √|A|`.

`Challenge.lean` imports only Mathlib and states two theorems, which `Solution.lean` proves:

```lean
theorem cosine_counterexample (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ A : Finset ℕ+, N ≤ A.card ∧
      ∀ t : ℝ, -ε * Real.sqrt (A.card : ℝ) <
        ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * t)

theorem chowla_cosine_conjecture_false :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ A : Finset ℕ+, A.Nonempty →
      ∃ t : ℝ, ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * t) <
        -c * Real.sqrt (A.card : ℝ)
```

In words:

* `cosine_counterexample` is Theorem 1 of the manuscript. For every `ε > 0` and every `N`
  there is a finite set `A` of positive integers with at least `N` elements such that
  `f_A(t) > -ε √|A|` for every real `t`. So there are arbitrarily large such sets.
* `chowla_cosine_conjecture_false` says that no constant `c > 0` works in Chowla's
  conjecture. Taking `ε = c` in Theorem 1 gives a nonempty set whose cosine sum never drops
  below `-c √|A|`. The conjecture is stated with "there is a real `t` with
  `f_A(t) < -c √|A|`". This is equivalent to `min_t f_A(t) < -c √|A|` because `f_A` is
  continuous and `1`-periodic, so its minimum is attained.

Conventions: `ℕ+` is Mathlib's type of positive integers, and `a : ℕ+` is cast to `ℝ`
through `ℕ`. `A.card` is the number of elements of `A`, and `Real.sqrt` is the real square
root. The angle `t` ranges over all of `ℝ`, which is the same as ranging over `ℝ/ℤ`.

## Relation to the literature

Chowla's cosine problem asks for the largest `K(n)` such that every set of `n` positive
integers has `min_t f_A(t) ≤ -K(n)`. It appears as Problem #510 on the Erdős Problems site
(<https://www.erdosproblems.com/510>), which lists it as open (checked November 2026).

* **Lower bounds:**
  * Bourgain (*Sur le minimum d'une somme de cosinus*, Acta Arith. 45 (1986)) went beyond
    powers of `log n`.
  * Ruzsa (*Negative values of cosine sums*, Acta Arith. 111 (2004)) proved
    `K(n) ≥ exp(c √log n)`.
  * Sanders (*Chowla's cosine problem*, Israel J. Math. 179 (2010)) proved, among other
    results, a polynomial bound when every element of `A` is `O(n)`.
  * The first polynomial bounds were found independently by Jin, Milojević, Tomon and Zhang
    (arXiv:2509.03490, exponent `1/10 - o(1)`) and by Bedert (arXiv:2509.05260, exponent
    `1/5 - o(1)`).
* **Upper bounds:** sets of the form `B - B` with `B` a Sidon set have depth of order `√n`.
  A recent construction (Bu, Khan, Yi, Jha, Chandupatla, Nagpal, arXiv:2610.17160) achieves
  depth `(1/2 + o(1)) √n`.

None of these results contradicts Theorem 1. The sets built here have depth at most
`C (log T) T^{-1/2} √|A|` for a parameter `T`, which is still of order `√|A|` for each fixed
`T`. They are therefore consistent with every polynomial lower bound above, but they show
that no fixed multiple of `√|A|` is forced.

The result and its proof are due to the manuscript cited above, and we make no independent
claim of novelty or priority. A search of arXiv and of the Erdős Problems page found no
earlier published counterexample. We know of no other public formalization of this result.

## How the proof is organized

`ChowlaOpus/Statements.lean` splits the proof into intermediate statements. Each file in
`ChowlaOpus/Parts/` proves one or two of them, possibly assuming others, and
`ChowlaOpus/Main.lean` composes them into `ChowlaOpus.main_theorem`. `Solution.lean`
restates that theorem with the cosine sum written out. The shared definitions are in
`ChowlaOpus/Basic.lean` and `ChowlaOpus/Profile/Defs.lean`.

The proof follows the manuscript section by section.

1. **Lemma 2: the Bessel transform.** This is in `Parts/J0.lean` and `Parts/Mellin.lean`,
   which cover:
   * the function `J₀`, its bounds and decay `|J₀(r)| ≤ 3/√r`, and its Laplace transform;
   * the plane-wave formula (2) for `G_s`;
   * the multiplier `m(τ) = 2^{iτ} Γ(1+iτ/2)/Γ(1−iτ/2)`, with `|m| = 1`;
   * the identity `G̃(τ, x) = m(τ) B̃(τ, x)`.

   The identity is proved by three Fubini interchanges, Gamma integrals and Legendre
   duplication.
2. **The annulus slices.** `Parts/Annulus.lean` proves the facts about `B_s` and
   `ℓ(x) = ½ log(1 + x⁻²)` (with `∫ ℓ = π`), the `L¹` bounds and the periodization estimate.
3. **Lemma 3: finite profiles `W` and `Q`.** The pieces are spread over several files:
   * `Parts/Bump.lean` builds the bump `ρ = φ ⋆ φ` with `ρ̂ ≥ 0`.
   * `Parts/Fejer.lean` proves the Fejér kernel estimates.
   * `Parts/Coeff.lean` bounds the coefficients `b_l` and the mass `H`.
   * `Parts/W.lean` gives the representation of `W` and the bound `0 ≤ W ≤ 1`.
   * `Parts/Q.lean` proves that `Q̂ ≥ 0`.
   * `Parts/Var.lean` proves the variance bound `V ≪ (log T)/T³`.

   `Parts/AsmA.lean` combines them. The parameters are `h = T⁻²`, `X = T²` and Fejér degree
   `J = ⌈T⁸⌉`.
4. **Section 3: separating the label frequencies.** `Parts/Saw.lean` covers the sawtooth
   coefficients, including Parseval and their Fejér averages. `Parts/Aux3.lean` covers the
   auxiliary circle coordinates, the Fejér smoothing in them, and the resulting
   finite-frequency profile.
5. **Section 4: phases modulo a prime square.** This part has four files:
   * `Parts/CRT.lean`: the linear form `L` whose values on the positive modes are positive
     and multiplicatively independent.
   * `Parts/KChar.lean`: an even character `χ₀` with `χ₀(1 + pt) = e(t/p)`.
   * `Parts/Gauss.lean`: the row sums, including identity (7) and the Ramanujan sums.
   * `Parts/Phase.lean`: the phase approximation (8).
6. **Section 5: all real angles.** `Parts/Poisson.lean` proves Poisson summation over
   residue classes and Fourier decay. `Parts/W9.lean` proves the lower bound (9), and
   `Parts/W10.lean` the mass and variance estimates (10). `Parts/AsmB.lean` assembles the
   weights.
7. **Lemma 4: rounding to a set.** `Parts/Partial.lean` proves a partial-colouring lemma,
   and `Parts/Spencer.lean` iterates it to get Spencer's theorem. `Parts/Mesh.lean` extends
   bounds from a mesh to the whole circle. `Parts/Rounding.lean` does the dyadic rounding,
   and `Parts/MainOf.lean` chooses the parameters and finishes the proof.

### Where the Lean proof differs from the manuscript

* Only the qualitative Theorem 1 is a compared theorem. The quantitative form (1) is not
  exported, although the proof uses estimates of that shape internally, with unspecified
  constants.
* **Lemma 2:** the Mellin identity is proved directly instead of citing DLMF 10.22.43 and
  continuing analytically.
* **Kernel character:** it is defined as `u ↦ ψ(1 − u^{p−1})`, where `ψ` is the standard
  additive character of `ℤ/p²ℤ`. This equals the manuscript's `χ₀`, built from the Fermat
  quotient.
* **Phase approximation:** the proof averages an explicit nonnegative trigonometric kernel
  over characters of the form `ξ²`, which are automatically even. It uses orthogonality of
  Dirichlet characters instead of Haar equidistribution and approximation by trigonometric
  polynomials.
* **Lemma 4:** Spencer's theorem is proved rather than cited.
* **Mesh bound:** the extension from a mesh to the circle uses a discrete de la
  Vallée-Poussin interpolation identity with constant 2, for meshes of at least `4N`
  points, instead of Bernstein's inequality.
* **Integrals at `x = 0`:** in Lean the Bochner integral of a non-integrable function is
  `0`, so `ℓ(0)` evaluates to `0`. The proofs treat this point with almost-everywhere
  arguments.

## Authorship, AI involvement and review

**Who wrote the code:** all Lean code in this repository was written by AI agents: Claude
Opus 5.5 running in Cursor. Shengtong Zhang directed the work and is responsible for the
repository. The mathematics comes from the manuscript cited above.

**How it was produced:**
* An orchestrating agent read the manuscript, wrote the shared definitions and split the
  proof into the statements in `ChowlaOpus/Statements.lean`.
* 24 parallel subagents, running the same model, each proved one component.
* The orchestrator recompiled every component, checked for `sorry`, ran `#print axioms`, and
  assembled the result.
* The orchestrator then ported the files to the Lean module system and wrote
  `Challenge.lean`, `Solution.lean` and the metadata.

This took about 2.5 hours of wall-clock time to a complete build.

**Review:** no human has reviewed the formal statements or proofs. The only review was by the
orchestrating agent, which is the same model as the subagents. Correctness of the proof rests
on the Lean kernel. Whether the statements in `Challenge.lean` faithfully express the
mathematics is for the reader to judge from the code above.

Structured metadata is in `formalization.yaml`.

## Building and checking

The project uses Lean `v4.36.0` and Mathlib `v4.36.0`.

```
lake exe cache get
lake build
```

`comparator.json` configures [Comparator](https://github.com/leanprover/comparator) to
check that `Solution.lean` proves the statements of `Challenge.lean` using only `propext`,
`Quot.sound` and `Classical.choice`.

## Licence

Apache-2.0; see `LICENSE`.
