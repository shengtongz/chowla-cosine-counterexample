# A counterexample to Chowla's cosine conjecture, in Lean

This repository is a complete Lean 4 / Mathlib formalization of a counterexample to
Chowla's cosine conjecture [2], following the manuscript [1].

The proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`, and contain no
`sorry`.

## The statements

For a finite set $A$ of positive integers write

$$f_A(t) = \sum_{a \in A} \cos(2\pi a t).$$

Chowla conjectured in 1965 [2, p. 130, eq. (14)] that there is an absolute constant $c > 0$
such that every nonempty $A$ satisfies $\min_t f_A(t) < -c\sqrt{\lvert A \rvert}$.

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

* `cosine_counterexample` is Theorem 1 of [1]. For every $\varepsilon > 0$ and every $N$
  there is a finite set $A$ of positive integers with at least $N$ elements such that
  $f_A(t) > -\varepsilon\sqrt{\lvert A \rvert}$ for every real $t$. So there are arbitrarily large such
  sets.
* `chowla_cosine_conjecture_false` says that no constant $c > 0$ works in Chowla's
  conjecture. Taking $\varepsilon = c$ in Theorem 1 gives a nonempty set whose cosine sum
  never drops below $-c\sqrt{\lvert A \rvert}$. The conjecture is stated with "there is a real $t$ with
  $f_A(t) < -c\sqrt{\lvert A \rvert}$". This is equivalent to $\min_t f_A(t) < -c\sqrt{\lvert A \rvert}$ because
  $f_A$ is continuous and $1$-periodic, so its minimum is attained.

Conventions: `ℕ+` is Mathlib's type of positive integers, and `a : ℕ+` is cast to `ℝ`
through `ℕ`. `A.card` is the number of elements of `A`, and `Real.sqrt` is the real square
root. The angle $t$ ranges over all of $\mathbb{R}$, which is the same as ranging over
$\mathbb{R}/\mathbb{Z}$.

## Relation to the literature

For a finite nonempty set $A$ of positive integers, define the *depth* of $A$ as

$$D(A) = -\min_{t \in \mathbb{R}} f_A(t),$$

the amount by which the cosine sum drops below zero. The depth is always positive, because
$f_A$ is continuous, has mean $0$ over a period, and is not identically zero
($f_A(0) = \lvert A \rvert$). Chowla's cosine problem asks for the smallest depth of an $n$-element set,

$$K(n) = \inf \lbrace D(A) : A \subset \mathbb{Z}_{>0},\ \lvert A \rvert = n \rbrace.$$

In this notation Chowla's conjecture says that $K(n) \ge c\sqrt{n}$ for some $c > 0$ and all
$n$. The problem is also Problem #510 on the Erdős Problems site [3]. Below, $c$ and $C$
denote positive constants, and the asymptotic notation $O$, $\Omega$, $\Theta$ and $o$
refers to $n = \lvert A \rvert \to \infty$.

**Lower bounds.**

* Bourgain [4] proved $K(n) \ge \exp((\log n)^c)$ for some $c > 0$, the first bound beyond
  powers of $\log n$.
* Ruzsa [5] improved this to $K(n) \ge \exp(c\sqrt{\log n})$.
* Sanders [6] proved, among other results, a polynomial bound when every element of $A$ is
  $O(n)$.
* The first polynomial bounds were proved independently by Jin, Milojević, Tomon and
  Zhang [7], with exponent $1/10 - o(1)$, and by Bedert [8]. Bedert's first version gave
  exponent $1/7$, and a later version gives $1/5 - o(1)$.
* These bounds have since been improved:
  * Yip [9] refines the spectral method of [7] and obtains exponent $1/6.43$.
  * Shankar [10] removes the $o(1)$ loss and proves $K(n) \ge c n^{1/5}$.
  * Bu, Khan, Yi, Jha, Chandupatla and Nagpal [11] prove $D(A) \ge c n^{1/4}$ for
    $n$-element sets $A \subset [1, Cn]$.
  * Shankar [12] proves $K(n) = \Omega\bigl((n / \log(2n))^{1/4}\bigr)$, the strongest
    general lower bound we found.

**Upper bounds.** Let $B$ be a Sidon set and let $A$ be the set of positive elements of
$B - B$. Then $\lvert A \rvert = \lvert B \rvert(\lvert B \rvert - 1)/2$ and

$$f_A(t) = \frac{1}{2}\left(\left|\sum_{b \in B} e^{2\pi i b t}\right|^2 - \lvert B \rvert\right) \ge -\frac{\lvert B \rvert}{2},$$

so $D(A) \le (1/\sqrt{2} + o(1))\sqrt{\lvert A \rvert}$. The construction of [11] lowers the constant: it
gives sets with $D(A) \le (1/2 + o(1))\sqrt{\lvert A \rvert}$.

Theorem 1 is consistent with all of these results. For each sufficiently large parameter $T$,
the construction of [1] gives arbitrarily large sets $A$ such that

$$c_1 \frac{P}{T} \le \lvert A \rvert \le c_2 \frac{P}{T} \quad \text{and} \quad D(A) \le C \frac{\log T}{\sqrt{T}} \sqrt{\lvert A \rvert},$$

where $P = p^2$ is a prime square and $c_1$, $c_2$, $C$ are absolute constants. Choosing $T$
with $C (\log T)/\sqrt{T} < \varepsilon$ gives Theorem 1. So for every $c > 0$ there are
infinitely many $n$ with $K(n) < c\sqrt{n}$, and $K(n) = \Theta(\sqrt{n})$ is false. The lower
bounds above that hold for all sets are $O(n^{1/4})$, far below this.

The result and its proof are due to [1], and we make no independent claim of novelty or
priority. A literature search of arXiv and the web in November 2026 found no earlier
published counterexample. We know of no other public formalization of this result.

## How the proof is organized

`ChowlaOpus/Statements.lean` splits the proof into intermediate statements. Each file in
`ChowlaOpus/Parts/` proves one or two of them, possibly assuming others, and
`ChowlaOpus/Main.lean` composes them into `ChowlaOpus.main_theorem`. `Solution.lean`
restates that theorem with the cosine sum written out. The shared definitions are in
`ChowlaOpus/Basic.lean` and `ChowlaOpus/Profile/Defs.lean`.

The proof follows [1] section by section. Throughout, $e(u) = e^{2\pi i u}$.

1. **Lemma 2: the Bessel transform.** This is in `Parts/J0.lean` and `Parts/Mellin.lean`,
   which cover:
   * the function $J_0$, its bounds and decay $\lvert J_0(r) \rvert \le 3/\sqrt{r}$, and its Laplace
     transform;
   * the plane-wave formula (2) for $G_s$;
   * the multiplier $m(\tau) = 2^{i\tau} \Gamma(1 + i\tau/2)/\Gamma(1 - i\tau/2)$, with
     $\lvert m \rvert = 1$;
   * the identity $\widetilde{G}(\tau, x) = m(\tau) \widetilde{B}(\tau, x)$.

   The identity is proved by three Fubini interchanges, Gamma integrals and Legendre
   duplication.
2. **The annulus slices.** `Parts/Annulus.lean` proves the facts about $B_s$ and
   $\ell(x) = \frac{1}{2}\log(1 + x^{-2})$ (with $\int \ell = \pi$), the $L^1$ bounds and the
   periodization estimate.
3. **Lemma 3: finite profiles $W$ and $Q$.** The pieces are spread over several files:
   * `Parts/Bump.lean` builds the bump $\rho = \varphi \ast \varphi$ with $\widehat{\rho} \ge 0$.
   * `Parts/Fejer.lean` proves the Fejér kernel estimates.
   * `Parts/Coeff.lean` bounds the coefficients $b_l$ and the mass $H$.
   * `Parts/W.lean` gives the representation of $W$ and the bound $0 \le W \le 1$.
   * `Parts/Q.lean` proves that $\widehat{Q} \ge 0$.
   * `Parts/Var.lean` proves the variance bound $V \le C (\log T)/T^3$.

   `Parts/AsmA.lean` combines them. The parameters are $h = T^{-2}$, $X = T^2$ and Fejér
   degree $J = \lceil T^8 \rceil$.
4. **Section 3: separating the label frequencies.** `Parts/Saw.lean` covers the sawtooth
   coefficients, including Parseval and their Fejér averages. `Parts/Aux3.lean` covers the
   auxiliary circle coordinates, the Fejér smoothing in them, and the resulting
   finite-frequency profile.
5. **Section 4: phases modulo a prime square.** This part has four files:
   * `Parts/CRT.lean`: the linear form $L$ whose values on the positive modes are positive
     and multiplicatively independent.
   * `Parts/KChar.lean`: an even character $\chi_0$ with $\chi_0(1 + pt) = e(t/p)$.
   * `Parts/Gauss.lean`: the row sums, including identity (7) and the Ramanujan sums.
   * `Parts/Phase.lean`: the phase approximation (8).
6. **Section 5: all real angles.** `Parts/Poisson.lean` proves Poisson summation over
   residue classes and Fourier decay. `Parts/W9.lean` proves the lower bound (9), and
   `Parts/W10.lean` the mass and variance estimates (10). `Parts/AsmB.lean` assembles the
   weights.
7. **Lemma 4: rounding to a set.** `Parts/Partial.lean` proves a partial-colouring lemma,
   and `Parts/Spencer.lean` iterates it to get Spencer's theorem [14]. `Parts/Mesh.lean`
   extends bounds from a mesh to the whole circle. `Parts/Rounding.lean` does the dyadic
   rounding, and `Parts/MainOf.lean` chooses the parameters and finishes the proof.

### Where the Lean proof differs from [1]

* Only the qualitative Theorem 1 is a compared theorem. The quantitative form (1) of [1] is
  not exported, although the proof uses estimates of that shape internally, with unspecified
  constants.
* **Lemma 2:** the Mellin identity is proved directly instead of citing [13, eq. 10.22.43]
  and continuing analytically.
* **Kernel character:** it is defined as $u \mapsto \psi(1 - u^{p-1})$, where $\psi$ is the
  standard additive character of $\mathbb{Z}/p^2\mathbb{Z}$. This equals the character
  $\chi_0$ of [1], built from the Fermat quotient.
* **Phase approximation:** the proof averages an explicit nonnegative trigonometric kernel
  over characters of the form $\xi^2$, which are automatically even. It uses orthogonality of
  Dirichlet characters instead of Haar equidistribution and approximation by trigonometric
  polynomials.
* **Lemma 4:** Spencer's theorem [14] is proved rather than cited.
* **Mesh bound:** the extension from a mesh to the circle uses a discrete de la
  Vallée-Poussin interpolation identity with constant $2$, for meshes of at least $4N$
  points, instead of Bernstein's inequality.
* **Integrals at $x = 0$:** in Lean the Bochner integral of a non-integrable function is
  $0$, so $\ell(0)$ evaluates to $0$. The proofs treat this point with almost-everywhere
  arguments.

## Authorship, AI involvement and review

**Who wrote the code:** all Lean code in this repository was written by AI agents: Claude
Opus 5.5 running in Cursor. Shengtong Zhang directed the work and is responsible for the
repository. The mathematics comes from [1].

**How it was produced:**
* An orchestrating agent read [1], wrote the shared definitions and split the
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

## References

1. *A prime-square counterexample to Chowla's cosine conjecture*. Unpublished manuscript,
   6 pages; not publicly available at the time of writing.
2. S. Chowla, Some applications of a method of A. Selberg, *J. Reine Angew. Math.* **217**
   (1965), 128–132.
3. Erdős Problem #510, <https://www.erdosproblems.com/510>.
4. J. Bourgain, Sur le minimum d'une somme de cosinus, *Acta Arith.* **45** (1986), 381–389.
5. I. Z. Ruzsa, Negative values of cosine sums, *Acta Arith.* **111** (2004), 179–186.
6. T. Sanders, Chowla's cosine problem, *Israel J. Math.* **179** (2010), 1–28;
   arXiv:0807.5104.
7. Z. Jin, A. Milojević, I. Tomon and S. Zhang, From small eigenvalues to large cuts, and
   Chowla's cosine problem, arXiv:2509.03490 (2025).
8. B. Bedert, Polynomial bounds for the Chowla cosine problem, arXiv:2509.05260 (2025).
9. F. Yip, Lower bounds for the magnitude of the minimum eigenvalue of graphs with
   applications to MaxCut and Chowla's cosine problem, arXiv:2610.01657 (2026).
10. A. Shankar, A log-free $n^{1/5}$ bound for Chowla's cosine problem, arXiv:2609.05338
    (2026).
11. B. Bu, F. Khan, H. Yi, A. Jha, I. Chandupatla and M. Nagpal, A half-constant upper bound
    for Chowla's cosine problem, arXiv:2610.17160 (2026).
12. A. Shankar, A quarter-power bound for Chowla's cosine problem, arXiv:2611.11144 (2026).
13. NIST Digital Library of Mathematical Functions, Sections 10.9 and 10.22,
    <https://dlmf.nist.gov/10>.
14. J. Spencer, Six standard deviations suffice, *Trans. Amer. Math. Soc.* **289** (1985),
    679–706.
