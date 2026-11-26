# A counterexample to Chowla's cosine conjecture, in Lean

This repository is a complete Lean 4 / Mathlib formalization of the manuscript [1]
([`manuscript/chowla_prime_square.pdf`](manuscript/chowla_prime_square.pdf)), which gives a
counterexample to Chowla's cosine conjecture [2].

**The manuscript [1], including the counterexample and its proof, was produced by the AI
model Astra 6.2, prompted by Shengtong Zhang. The Lean formalization was then written by
Claude Opus 5.5 agents in Cursor.**

The proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`, and contain no
`sorry`.

## The statements

For a finite set $A$ of positive integers write

$$f_A(t) = \sum_{a \in A} \cos(2\pi a t).$$

Chowla conjectured in 1965 [2, p. 130, eq. (14)] that there is an absolute constant $c > 0$
such that every nonempty $A$ satisfies $\min_t f_A(t) < -c\sqrt{\lvert A \rvert}$. This is
Problem #510 on the Erdős Problems site [3].

`Challenge.lean` imports only Mathlib and states two theorems, which `Solution.lean` proves.

**Main theorem.** Google DeepMind's formal-conjectures repository [4] states Erdős Problem
#510 as the Lean theorem `Erdos510.erdos_510`, tagged `research open`. We prove its
negation. The statement below is copied verbatim from
`FormalConjectures/ErdosProblems/510.lean` at commit `7db2ea3`, with `¬` added. Following
that repository's convention for disproved problems, the theorem keeps its name.

```lean
namespace Erdos510

open Real Filter
open scoped Finset

theorem erdos_510 :
    ¬ ∃ (c : ℝ) (hc : 0 < c),
      ∀ᶠ N in atTop, ∀ (A : Finset ℕ), 0 ∉ A → #A = N →
      ∃ θ, ∑ n ∈ A, cos (n * θ) < -c * sqrt N
```

In words: there is no constant $c > 0$ such that, for all sufficiently large $N$, every set
$A$ of $N$ positive integers has an angle $\theta$ with
$\sum_{n \in A} \cos(n\theta) < -c\sqrt{N}$.

* $A$ is a `Finset ℕ` with $0 \notin A$, that is, a set of positive integers. The
  substitution $\theta = 2\pi t$ turns $\cos(n\theta)$ into the summands of $f_A(t)$.
* Asking for some $\theta$ below $-c\sqrt{N}$ is the same as asking for
  $\min_t f_A(t) < -c\sqrt{N}$, because $f_A$ is continuous and periodic, so its minimum is
  attained.
* The statement only asks for the bound when $N$ is large. Its negation is therefore
  stronger than the negation of Chowla's conjecture as stated for all $A$.

**Theorem 1 of [1].**

```lean
theorem cosine_counterexample (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ A : Finset ℕ+, N ≤ A.card ∧
      ∀ t : ℝ, -ε * Real.sqrt (A.card : ℝ) <
        ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * t)
```

For every $\varepsilon > 0$ and every $N$ there is a finite set $A$ of positive integers with
at least $N$ elements such that $f_A(t) > -\varepsilon\sqrt{\lvert A \rvert}$ for every real
$t$. Theorem 1 implies the main theorem: given $c > 0$ and any threshold $N_0$, Theorem 1 with
$\varepsilon = c$ gives a set with at least $N_0$ elements that violates the bound. This is
how `Solution.lean` proves `Erdos510.erdos_510`.

Conventions: `ℕ+` is Mathlib's type of positive integers, and `a : ℕ+` is cast to `ℝ`
through `ℕ`. Both `#A` and `A.card` are the number of elements of `A`. `sqrt` and `Real.sqrt`
are the real square root, applied to a natural number cast to `ℝ`. `∀ᶠ N in atTop` means "for
all sufficiently large `N`". The angles $\theta$ and $t$ range over all of $\mathbb{R}$.

## Relation to the literature

For a finite nonempty set $A$ of positive integers, define the *depth* of $A$ as

$$D(A) = -\min_{t \in \mathbb{R}} f_A(t),$$

the amount by which the cosine sum drops below zero. The depth is always positive, because
$f_A$ is continuous, has mean $0$ over a period, and is not identically zero
($f_A(0) = \lvert A \rvert$). Chowla's cosine problem asks for the smallest depth of an
$n$-element set,

$$K(n) = \inf \lbrace D(A) : A \subset \mathbb{Z}_{>0},\ \lvert A \rvert = n \rbrace.$$

In this notation Chowla's conjecture says that $K(n) \ge c\sqrt{n}$ for some $c > 0$ and all
$n$. Below, $c$ and $C$ denote positive constants, and the asymptotic notation $O$, $\Omega$,
$\Theta$ and $o$ refers to $n = \lvert A \rvert \to \infty$.

**Lower bounds.**

* Bourgain [5] proved $K(n) \ge \exp((\log n)^c)$ for some $c > 0$, the first bound beyond
  powers of $\log n$.
* Ruzsa [6] improved this to $K(n) \ge \exp(c\sqrt{\log n})$.
* Sanders [7] proved, among other results, a polynomial bound when every element of $A$ is
  $O(n)$.
* The first polynomial bounds were proved independently by Jin, Milojević, Tomon and
  Zhang [8], with exponent $1/10 - o(1)$, and by Bedert [9]. Bedert's first version gave
  exponent $1/12$, the second $1/7 - o(1)$, and a later version gives $1/5 - o(1)$.
* These bounds have since been improved:
  * Yip [10] refines the spectral method of [8] and obtains exponent $1/6.43$.
  * Shankar [11] removes the $o(1)$ loss and proves $K(n) \ge c n^{1/5}$.
  * Bu, Khan, Yi, Jha, Chandupatla and Nagpal [12] prove $D(A) \ge c n^{1/4}$ for
    $n$-element sets $A \subset [1, Cn]$.
  * Shankar [13] proves $K(n) = \Omega\bigl((n / \log(2n))^{1/4}\bigr)$, the strongest
    general lower bound we found.

**Coefficients near one.** Knowledge Sense [14] proved a polynomial bound when each cosine
carries its own coefficient close to $1$. For distinct positive integers
$a_1, \dots, a_N$ and real numbers $s_1, \dots, s_N \in [0.99, 1.01]$,

$$\min_{x \in \mathbb{R}} \sum_{j=1}^{N} s_j \cos(2\pi a_j x) \le -\frac{N^{1/9}}{20}.$$

The preprint describes this as the first polynomial bound for a question of Ruzsa recalled by
Bedert [9], for which only a bound of order $\log N$ had been recorded. Taking every
$s_j = 1$ gives $K(n) \ge n^{1/9}/20$ for every $n \ge 1$, with an explicit constant. The
preprint comes with a Lean formalization of its main theorems.

**Upper bounds.** Let $B$ be a Sidon set and let $A$ be the set of positive elements of
$B - B$. Then $\lvert A \rvert = \lvert B \rvert(\lvert B \rvert - 1)/2$ and

$$f_A(t) = \frac{1}{2}\left(\left|\sum_{b \in B} e^{2\pi i b t}\right|^2 - \lvert B \rvert\right) \ge -\frac{\lvert B \rvert}{2},$$

so $D(A) \le (1/\sqrt{2} + o(1))\sqrt{\lvert A \rvert}$. The construction of [12] lowers the
constant: it gives sets with $D(A) \le (1/2 + o(1))\sqrt{\lvert A \rvert}$.

Theorem 1 is consistent with all of these results. For each sufficiently large parameter $T$,
the construction of [1] gives arbitrarily large sets $A$ such that

$$c_1 \frac{P}{T} \le \lvert A \rvert \le c_2 \frac{P}{T} \quad \text{and} \quad D(A) \le C \frac{\log T}{\sqrt{T}} \sqrt{\lvert A \rvert},$$

where $P = p^2$ is a prime square and $c_1$, $c_2$, $C$ are absolute constants. Choosing $T$
with $C (\log T)/\sqrt{T} < \varepsilon$ gives Theorem 1. So for every $c > 0$ there are
infinitely many $n$ with $K(n) < c\sqrt{n}$, and $K(n) = \Theta(\sqrt{n})$ is false. The lower
bounds above that hold for all sets are $O(n^{1/4})$, far below this.

The result and its proof are due to [1], and we make no independent claim of novelty or
priority. A literature search of arXiv and the web in November 2026 found no earlier
published counterexample.

**Related formalizations.**

* formal-conjectures [4] states Erdős Problem #510 as `Erdos510.erdos_510`, tagged
  `research open`. Our main theorem is its negation, verbatim. Several benchmark and
  catalogue repositories copy that statement as an open problem or as a target to refute.
* Knowledge Sense [14] formalized their bound for coefficients near one in Lean.
* lean-genius [15] has a work-in-progress file of elementary Lean lemmas about these cosine
  sums. It does not address the conjecture itself.

A search of GitHub in November 2026 found no other formalization of a counterexample.

## How the proof is organized

`ChowlaOpus/Statements.lean` splits the proof into intermediate statements. Each file in
`ChowlaOpus/Parts/` proves one or two of them, possibly assuming others, and
`ChowlaOpus/Main.lean` composes them into `ChowlaOpus.main_theorem`. `Solution.lean`
restates that theorem with the cosine sum written out as `cosine_counterexample`, and
derives `Erdos510.erdos_510` from it. The shared definitions are in `ChowlaOpus/Basic.lean`
and `ChowlaOpus/Profile/Defs.lean`.

The proof follows [1] section by section. Throughout, $e(u) = e^{2\pi i u}$.

1. **Lemma 2: the Bessel transform.** This is in `Parts/J0.lean` and `Parts/Mellin.lean`,
   which cover:
   * the function $J_0$, its bounds and decay $\lvert J_0(r) \rvert \le 3/\sqrt{r}$, and its
     Laplace transform;
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
   and `Parts/Spencer.lean` iterates it to get Spencer's theorem [16]. `Parts/Mesh.lean`
   extends bounds from a mesh to the whole circle. `Parts/Rounding.lean` does the dyadic
   rounding, and `Parts/MainOf.lean` chooses the parameters and finishes the proof.

### Where the Lean proof differs from [1]

* The compared theorems are the negation of the formal-conjectures statement and the
  qualitative Theorem 1. The quantitative form (1) of [1] is not exported, although the
  proof uses estimates of that shape internally, with unspecified constants.
* **Lemma 2:** the Mellin identity is proved directly instead of citing [17, eq. 10.22.43]
  and continuing analytically.
* **Kernel character:** it is defined as $u \mapsto \psi(1 - u^{p-1})$, where $\psi$ is the
  standard additive character of $\mathbb{Z}/p^2\mathbb{Z}$. This equals the character
  $\chi_0$ of [1], built from the Fermat quotient.
* **Phase approximation:** the proof averages an explicit nonnegative trigonometric kernel
  over characters of the form $\xi^2$, which are automatically even. It uses orthogonality of
  Dirichlet characters instead of Haar equidistribution and approximation by trigonometric
  polynomials.
* **Lemma 4:** Spencer's theorem [16] is proved rather than cited.
* **Mesh bound:** the extension from a mesh to the circle uses a discrete de la
  Vallée-Poussin interpolation identity with constant $2$, for meshes of at least $4N$
  points, instead of Bernstein's inequality.
* **Integrals at $x = 0$:** in Lean the Bochner integral of a non-integrable function is
  $0$, so $\ell(0)$ evaluates to $0$. The proofs treat this point with almost-everywhere
  arguments.

## Authorship, AI involvement and review

**Who produced the mathematics:** Astra 6.2, prompted by Shengtong Zhang. The manuscript [1],
including the counterexample and its proof, is its output.

**Who wrote the code:** all Lean code in this repository was written by AI agents: Claude
Opus 5.5 running in Cursor. Shengtong Zhang directed the work and is responsible for the
repository.

**How it was produced:**
* An orchestrating agent read [1], wrote the shared definitions and split the
  proof into the statements in `ChowlaOpus/Statements.lean`.
* 24 parallel subagents, running the same model, each proved one or two of the component
  files in `ChowlaOpus/Parts/`.
* The orchestrator recompiled every component, checked for `sorry`, ran `#print axioms`, and
  assembled the result.
* The orchestrator then ported the files to the Lean module system and wrote
  `Challenge.lean`, `Solution.lean` and the metadata.

This took about 2.5 hours of wall-clock time to a complete build.

**Review:** no human has reviewed the formal statements or proofs. The only review was by the
orchestrating agent, which is the same model as the subagents. Correctness of the proof rests
on the Lean kernel. The main statement is taken verbatim from formal-conjectures [4]. Whether
the statements in `Challenge.lean` faithfully express the mathematics is for the reader to
judge from the code above.

Structured metadata is in `formalization.yaml`.

## Building and checking

The project uses Lean `v4.36.0` and Mathlib `v4.36.0`.

```
lake exe cache get
lake build
```

`comparator.json` configures [Comparator](https://github.com/leanprover/comparator) to
check that `Solution.lean` proves the statements `Erdos510.erdos_510` and
`cosine_counterexample` of `Challenge.lean` using only `propext`, `Quot.sound` and
`Classical.choice`.

## Licence

Apache-2.0; see `LICENSE`. This covers the Lean code, the documentation and the manuscript
in `manuscript/`.

## References

1. Astra 6.2 (AI model), prompted by Shengtong Zhang, *A prime-square counterexample to
   Chowla's cosine conjecture*. Manuscript, 6 pages, included in this repository as
   [`manuscript/chowla_prime_square.pdf`](manuscript/chowla_prime_square.pdf); not published
   elsewhere.
2. S. Chowla, Some applications of a method of A. Selberg, *J. Reine Angew. Math.* **217**
   (1965), 128–132.
3. Erdős Problem #510, <https://www.erdosproblems.com/510>.
4. Google DeepMind, Formal Conjectures, Erdős Problem 510,
   `FormalConjectures/ErdosProblems/510.lean` at commit `7db2ea3`,
   <https://github.com/google-deepmind/formal-conjectures/blob/7db2ea3b91bfbd0ab620215163e6c488bbb916d5/FormalConjectures/ErdosProblems/510.lean>.
5. J. Bourgain, Sur le minimum d'une somme de cosinus, *Acta Arith.* **45** (1986), 381–389.
6. I. Z. Ruzsa, Negative values of cosine sums, *Acta Arith.* **111** (2004), 179–186.
7. T. Sanders, Chowla's cosine problem, *Israel J. Math.* **179** (2010), 1–28;
   arXiv:0807.5104.
8. Z. Jin, A. Milojević, I. Tomon and S. Zhang, From small eigenvalues to large cuts, and
   Chowla's cosine problem, arXiv:2509.03490 (2025).
9. B. Bedert, Polynomial bounds for the Chowla cosine problem, arXiv:2509.05260 (2025).
10. F. Yip, Lower bounds for the magnitude of the minimum eigenvalue of graphs with
    applications to MaxCut and Chowla's cosine problem, arXiv:2610.01657 (2026).
11. A. Shankar, A log-free $n^{1/5}$ bound for Chowla's cosine problem, arXiv:2609.05338
    (2026).
12. B. Bu, F. Khan, H. Yi, A. Jha, I. Chandupatla and M. Nagpal, A half-constant upper bound
    for Chowla's cosine problem, arXiv:2610.17160 (2026).
13. A. Shankar, A quarter-power bound for Chowla's cosine problem, arXiv:2611.11144 (2026).
14. Knowledge Sense, Chowla's cosine problem with near-unit coefficients, preprint with Lean
    formalization (12 October 2026),
    <https://github.com/KnowledgeSense/math/tree/91f1bdd2a10abeb28acc742ce3ee884874caf124/preprints/Chowlas-Cosine-Problem-with-Near-Unit-Coefficients-October-12-2026>.
15. lean-genius, `Proofs/Erdos510WIP01.lean`,
    <https://github.com/rjwalters/lean-genius/blob/15110ef2440acd23105e78d2dc522311736f1b75/proofs/Proofs/Erdos510WIP01.lean>.
16. J. Spencer, Six standard deviations suffice, *Trans. Amer. Math. Soc.* **289** (1985),
    679–706.
17. NIST Digital Library of Mathematical Functions, Sections 10.9 and 10.22,
    <https://dlmf.nist.gov/10>.
