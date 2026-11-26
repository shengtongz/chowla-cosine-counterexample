module

public import ChowlaOpus.Profile.Defs

@[expose] public section

/-!
# Statements of the components of the proof

Each `...Statement` is a `Prop` proved by exactly one file in `ChowlaOpus/Parts/`, possibly
assuming other statements as hypotheses. `ChowlaOpus/Main.lean` composes them.

Dependency graph (component : proves  ⟸  assumes). A few hypotheses are taken but unused:
`BesselPlaneStatement` in `mellinStatement_holds` and `AnnulusStatement` in `qposStatement_holds`.
* Fejer     : FejerStatement
* Bump      : BumpStatement
* J0        : J0Statement, BesselPlaneStatement
* Mellin    : MultStatement; MellinStatement             ⟸ J0Statement
* Annulus   : AnnulusStatement
* Coeff     : CoeffStatement, CoeffMassStatement         ⟸ AnnulusStatement
* W         : WrepStatement, WboundStatement             ⟸ AnnulusStatement, FejerStatement
* Q         : QposStatement                              ⟸ J0, BesselPlane, Mult, Mellin, Fejer
* Var       : VarStatement                               ⟸ AnnulusStatement, FejerStatement,
                                                            WrepStatement, WboundStatement
* AsmA      : Lemma3Statement                            ⟸ Bump, Coeff, CoeffMass, Wbound, Qpos, Var
* Saw       : SawStatement
* Aux3      : ProfileStatement                           ⟸ Lemma3, Saw, Fejer, FourierDecay
* Poisson   : PoissonStatement, PlainPoissonStatement, FourierDecayStatement
* Gauss     : RowSumStatement
* KChar     : KernelCharStatement
* Phase     : PhaseStatement                             ⟸ KernelCharStatement
* CRT       : CRTStatement
* W9        : W9Statement                                ⟸ RowSum, Poisson, PlainPoisson, Mult
* W10       : W10Statement                               ⟸ RowSum, Poisson, FourierDecay
* AsmB      : WeightsStatement                           ⟸ Profile, CRT, Phase, RowSum, Mult, W9, W10
* Partial   : PartialColoringStatement
* Spencer   : SpencerStatement                           ⟸ PartialColoringStatement
* Mesh      : MeshStatement
* Rounding  : RoundingStatement                          ⟸ SpencerStatement, MeshStatement
* MainOf    : cosine_counterexample_of                   ⟸ WeightsStatement, RoundingStatement
* Main      : main_theorem (restated as `cosine_counterexample` in `Solution.lean`)
-/

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

/-! ## Rounding (§6, Lemma 4) -/

/-- Partial colouring (entropy/pigeonhole step of Spencer's theorem), rectangular form. -/
def PartialColoringStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M v : ℕ), 1 ≤ v → v ≤ M → ∀ A : Fin M → Fin v → ℝ,
    (∀ i j, |A i j| ≤ 1) →
    ∃ x : Fin v → ℤ, (∀ j, |x j| ≤ 1) ∧
      v ≤ 10 * (Finset.univ.filter (fun j => x j ≠ 0)).card ∧
      ∀ i, |∑ j, A i j * (x j : ℝ)| ≤ C * Real.sqrt (v * Real.log (2 * M / v))

/-- Spencer's theorem, rectangular form: a full signing of an `M × v` matrix (`v ≤ M`) with
entries in `[-1,1]` has all row sums `O(√(v log(2M/v)))`. -/
def SpencerStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M v : ℕ), 1 ≤ v → v ≤ M → ∀ A : Fin M → Fin v → ℝ,
    (∀ i j, |A i j| ≤ 1) →
    ∃ ε : Fin v → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ i, |∑ j, A i j * ε j| ≤ C * Real.sqrt (v * Real.log (2 * M / v))

/-- Mesh bound (consequence of Bernstein's inequality): a cosine polynomial of degree `≤ N`
bounded by `E` on a mesh of `M ≥ K N` equally spaced points is bounded by `2E` everywhere. -/
def MeshStatement : Prop :=
  ∃ K : ℕ, 1 ≤ K ∧ ∀ (N M : ℕ) (c : ℕ → ℝ) (E : ℝ), K * N ≤ M → 0 < M →
    (∀ i < M, |∑ d ∈ Finset.Icc 1 N, c d * Real.cos (2 * Real.pi * d * ((i : ℝ) / M))| ≤ E) →
    ∀ t : ℝ, |∑ d ∈ Finset.Icc 1 N, c d * Real.cos (2 * Real.pi * d * t)| ≤ 2 * E

/-- Lemma 4 (rounding), with an upper bound `S` for the rounding variance. -/
def RoundingStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (w : ℕ → ℝ) (S : ℝ), 1 ≤ N → (∀ d, 0 ≤ w d ∧ w d ≤ 1) →
    0 < S → S ≤ N → ∑ d ∈ Finset.Icc 1 N, w d * (1 - w d) ≤ S →
    ∃ a : ℕ → ℝ, (∀ d, a d = 0 ∨ a d = 1) ∧
      ∀ t : ℝ, |∑ d ∈ Finset.Icc 1 N, (a d - w d) * Real.cos (2 * Real.pi * d * t)| ≤
        C * Real.sqrt (S * Real.log (2 * N / S))

/-! ## Weights (§5, displays (9) and (10)) -/

/-- Fractional weights with a small negative cosine sum, large mass and small rounding
variance, for arbitrarily large `T` and then arbitrarily large `p`. -/
def WeightsStatement : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧ ∀ p₀ : ℕ,
    ∃ (p N : ℕ) (w : ℕ → ℝ), p₀ ≤ p ∧ 1 ≤ N ∧ (N : ℝ) ≤ 2 * (p : ℝ) ^ 2 * T ^ 2 ∧
      (∀ d, 0 ≤ w d ∧ w d ≤ 1) ∧
      (∀ t : ℝ, -(C * p * Real.log T / T) ≤
        ∑ d ∈ Finset.Icc 1 N, w d * Real.cos (2 * Real.pi * d * t)) ∧
      c * (p : ℝ) ^ 2 / T ≤ ∑ d ∈ Finset.Icc 1 N, w d ∧
      ∑ d ∈ Finset.Icc 1 N, w d * (1 - w d) ≤ C * (p : ℝ) ^ 2 * Real.log T / T ^ 3

/-! ## Profiles (Lemma 3 and §3) -/

/-- Output of Lemma 3 (label rescaled to period one). `W_s = ∑ b_l e(ls) ∈ [0,1]`,
`Q_s = ∑ m(2πl/T) b_l e(ls)` has nonnegative physical Fourier transform, (4) and (5). -/
def Lemma3Statement : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ∃ (J : ℕ) (b : ℤ → ℝ → ℂ),
      (∀ l, (J : ℤ) < |l| → b l = 0) ∧
      (∀ l, ContDiff ℝ 2 (b l)) ∧
      (∀ l x, T ^ 2 < |x| → b l x = 0) ∧
      (∀ l x, b l (-x) = b l x) ∧
      (∀ l x, b (-l) x = starRingEnd ℂ (b l x)) ∧
      (∀ x, (b 0 x).im = 0 ∧ 0 ≤ (b 0 x).re) ∧
      (∀ y, (𝓕 (b 0) y).im = 0 ∧ 0 ≤ (𝓕 (b 0) y).re) ∧
      Summable (fun j : ℤ => (b 0 j).re) ∧
      ∑' j : ℤ, (b 0 j).re ≤ C * Real.log T / T ∧
      c / T ≤ ∫ x, (b 0 x).re ∧
      (∀ s x, (∑ l ∈ Finset.Icc (-(J : ℤ)) J, b l x * ee (l * s)).im = 0 ∧
        0 ≤ (∑ l ∈ Finset.Icc (-(J : ℤ)) J, b l x * ee (l * s)).re ∧
        (∑ l ∈ Finset.Icc (-(J : ℤ)) J, b l x * ee (l * s)).re ≤ 1) ∧
      (∀ s y, (∑ l ∈ Finset.Icc (-(J : ℤ)) J,
          mult (2 * Real.pi * l / T) * 𝓕 (b l) y * ee (l * s)).im = 0 ∧
        0 ≤ (∑ l ∈ Finset.Icc (-(J : ℤ)) J,
          mult (2 * Real.pi * l / T) * 𝓕 (b l) y * ee (l * s)).re) ∧
      ∫ x, ((b 0 x).re - ∑ l ∈ Finset.Icc (-(J : ℤ)) J, ‖b l x‖ ^ 2) ≤
        C * Real.log T / T ^ 3

/-- The structural properties of a separated profile at scale `T` (output of §3):
frequency set `S ⊆ ℤ^{k+1}` (coordinate `0` is the label frequency), coefficients `cf`
supported in `[-R, R]` with Fourier decay constant `K`. -/
structure IsProfile {k : ℕ} (T : ℝ) (S : Finset (Fin (k + 1) → ℤ))
    (cf : (Fin (k + 1) → ℤ) → ℝ → ℂ) (K R : ℝ) : Prop where
  zero_mem : 0 ∈ S
  neg_mem : ∀ v ∈ S, -v ∈ S
  label_ne : ∀ v ∈ S, v ≠ 0 → v 0 ≠ 0
  nonprop : ∀ v ∈ S, ∀ w ∈ S, 0 < v 0 → 0 < w 0 → (∀ i j, v i * w j = v j * w i) → v = w
  zero_off : ∀ v, v ∉ S → cf v = 0
  smooth : ∀ v, ContDiff ℝ 2 (cf v)
  supp : ∀ v x, R < |x| → cf v x = 0
  even : ∀ v x, cf v (-x) = cf v x
  conj : ∀ v x, cf (-v) x = starRingEnd ℂ (cf v x)
  decay : ∀ v y, ‖𝓕 (cf v) y‖ ≤ K / (1 + y ^ 2)
  b0 : ∀ x, (cf 0 x).im = 0 ∧ 0 ≤ (cf 0 x).re
  fourier_b0 : ∀ y, (𝓕 (cf 0) y).im = 0 ∧ 0 ≤ (𝓕 (cf 0) y).re
  range : ∀ (θ : Fin (k + 1) → ℝ) (x : ℝ), (trigEval S (fun v => cf v x) θ).im = 0 ∧
    0 ≤ (trigEval S (fun v => cf v x) θ).re ∧ (trigEval S (fun v => cf v x) θ).re ≤ 1
  pos : ∀ (θ : Fin (k + 1) → ℝ) (y : ℝ),
    (trigEval S (fun v => mult (2 * Real.pi * v 0 / T) * 𝓕 (cf v) y) θ).im = 0 ∧
    0 ≤ (trigEval S (fun v => mult (2 * Real.pi * v 0 / T) * 𝓕 (cf v) y) θ).re

/-- Output of §3: separated profiles for all large `T`, with the bounds (4), (5). -/
def ProfileStatement : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    ∃ (k : ℕ) (S : Finset (Fin (k + 1) → ℤ)) (cf : (Fin (k + 1) → ℤ) → ℝ → ℂ) (K : ℝ),
      IsProfile T S cf K (T ^ 2) ∧
      Summable (fun j : ℤ => (cf 0 j).re) ∧
      ∑' j : ℤ, (cf 0 j).re ≤ C * Real.log T / T ∧
      c / T ≤ ∫ x, (cf 0 x).re ∧
      ∫ x, ((cf 0 x).re - ∑ v ∈ S, ‖cf v x‖ ^ 2) ≤ C * Real.log T / T ^ 3

/-! ## Arithmetic (§4) -/

/-- Chinese remainder construction: pairwise non-proportional integer vectors with positive
first coordinate are sent by a linear form to positive, multiplicatively independent integers. -/
def CRTStatement : Prop :=
  ∀ (k : ℕ) (S : Finset (Fin (k + 1) → ℤ)), (∀ v ∈ S, 0 < v 0) →
    (∀ v ∈ S, ∀ w ∈ S, (∀ i j, v i * w j = v j * w i) → v = w) →
    ∃ L : Fin (k + 1) → ℤ, (∀ v ∈ S, 0 < ∑ i, L i * v i) ∧
      MultIndep (fun v : S => (∑ i, L i * (v : Fin (k + 1) → ℤ) i).toNat)

/-- Existence of an even character mod `p²` restricting to `1 + pt ↦ e(t/p)`. -/
def KernelCharStatement : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ χ : MulChar (ZMod (p ^ 2)) ℂ, KernelChar p χ

/-- Display (8): prescribed unimodular phases are approximated by Gauss phases of even kernel
characters at every sufficiently large prime. -/
def PhaseStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ι → ℕ), (∀ i, 0 < n i) → MultIndep n →
    ∀ η : ℝ, 0 < η → ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p → ∀ μ : ι → ℂ, (∀ i, ‖μ i‖ = 1) →
      ∃ χ : MulChar (ZMod (p ^ 2)) ℂ, KernelChar p χ ∧
        ∀ i, ‖gaussPhase p χ (n i) - μ i‖ < η

/-- Display (7) and the row sums of §5. -/
def RowSumStatement : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ χ : MulChar (ZMod (p ^ 2)) ℂ, KernelChar p χ →
    (∀ n k : ℤ, ¬ (p : ℤ) ∣ n → ¬ (p : ℤ) ∣ k →
      rowSum p χ n k = p * ((χ (k : ZMod (p ^ 2)))⁻¹) ^ n * gaussPhase p χ n) ∧
    (∀ n k : ℤ, ¬ (p : ℤ) ∣ n → (p : ℤ) ∣ k → rowSum p χ n k = 0) ∧
    (∀ k : ℤ, rowSum p χ 0 k =
      (if (p : ℤ) ^ 2 ∣ k then ((p : ℂ) ^ 2) else 0) - (if (p : ℤ) ∣ k then (p : ℂ) else 0)) ∧
    (∀ n : ℤ, ¬ (p : ℤ) ∣ n → ‖gaussPhase p χ n‖ = 1) ∧
    (∀ n : ℤ, gaussPhase p χ (-n) = starRingEnd ℂ (gaussPhase p χ n))

/-! ## Fourier analysis utilities -/

/-- Fourier decay of `C²` compactly supported functions. -/
def FourierDecayStatement : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, ‖𝓕 f y‖ ≤ K / (1 + y ^ 2)

/-- Poisson summation for a profile sampled at `d / p²`, twisted by `χ(d)^n`, restricted to
`p ∤ d`. -/
def PoissonStatement : Prop :=
  ∀ p : ℕ, p.Prime → ∀ (χ : MulChar (ZMod (p ^ 2)) ℂ) (n : ℤ) (f : ℝ → ℂ) (K : ℝ),
    Continuous f → HasCompactSupport f → (∀ y, ‖𝓕 f y‖ ≤ K / (1 + y ^ 2)) → ∀ t : ℝ,
      Summable (fun k : ℤ => 𝓕 f (k - (p : ℝ) ^ 2 * t) * rowSum p χ n k) ∧
      HasSum (fun d : ℤ => (if (p : ℤ) ∣ d then 0 else
          f ((d : ℝ) / (p : ℝ) ^ 2) * (χ (d : ZMod (p ^ 2))) ^ n) * ee (d * t))
        (∑' k : ℤ, 𝓕 f (k - (p : ℝ) ^ 2 * t) * rowSum p χ n k)

/-- Plain Poisson summation `∑_k 𝓕f(k + y) = ∑_j f(j) e(-jy)`. -/
def PlainPoissonStatement : Prop :=
  ∀ (f : ℝ → ℂ) (K : ℝ), Continuous f → HasCompactSupport f →
    (∀ y, ‖𝓕 f y‖ ≤ K / (1 + y ^ 2)) → ∀ y : ℝ,
      Summable (fun j : ℤ => f j * ee (-((j : ℝ) * y))) ∧
      HasSum (fun k : ℤ => 𝓕 f (k + y)) (∑' j : ℤ, f j * ee (-((j : ℝ) * y)))

/-! ## The weights of §5 -/

/-- `w_d = Re ∑_{v ∈ S} c_v(d/p²) χ(d)^{L·v}` for `p ∤ d`, and `0` otherwise. -/
noncomputable def wgt {k : ℕ} (S : Finset (Fin (k + 1) → ℤ)) (cf : (Fin (k + 1) → ℤ) → ℝ → ℂ)
    (L : Fin (k + 1) → ℤ) (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) (d : ℤ) : ℝ :=
  if (p : ℤ) ∣ d then 0 else
    (∑ v ∈ S, cf v ((d : ℝ) / (p : ℝ) ^ 2) * (χ (d : ZMod (p ^ 2))) ^ (∑ i, L i * v i)).re

/-- Display (9): lower bound for the cosine sum of the weights. -/
def W9Statement : Prop :=
  ∀ (k : ℕ) (T K : ℝ) (S : Finset (Fin (k + 1) → ℤ)) (cf : (Fin (k + 1) → ℤ) → ℝ → ℂ),
    IsProfile T S cf K (T ^ 2) → 0 < T →
    ∀ (L : Fin (k + 1) → ℤ) (p : ℕ), p.Prime → p ≠ 2 →
    (∀ v ∈ S, 2 * |∑ i, L i * v i| < p) →
    (∀ v ∈ S, ∀ w ∈ S, ∑ i, L i * v i = ∑ i, L i * w i → v = w) →
    ∀ χ : MulChar (ZMod (p ^ 2)) ℂ, KernelChar p χ →
    ∀ η : ℝ, 0 ≤ η → η * (5 * K * S.card) ≤ 1 / T →
    (∀ v ∈ S, v ≠ 0 → ‖gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T)‖ ≤ η) →
    ∀ N : ℕ, (p : ℝ) ^ 2 * T ^ 2 ≤ N → ∀ t : ℝ,
      -((p : ℝ) / 2 * (∑' j : ℤ, (cf 0 j).re + 1 / T)) ≤
        ∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d * Real.cos (2 * Real.pi * d * t)

/-- Display (10): mass and rounding variance of the weights, up to `O_T(p)`. -/
def W10Statement : Prop :=
  ∀ (k : ℕ) (T K : ℝ) (S : Finset (Fin (k + 1) → ℤ)) (cf : (Fin (k + 1) → ℤ) → ℝ → ℂ),
    IsProfile T S cf K (T ^ 2) → 0 < T →
    ∀ L : Fin (k + 1) → ℤ, (∀ v ∈ S, ∀ w ∈ S, ∑ i, L i * v i = ∑ i, L i * w i → v = w) →
    ∃ E : ℝ, ∀ p : ℕ, p.Prime → p ≠ 2 → (∀ v ∈ S, 2 * |∑ i, L i * v i| < p) →
      ∀ χ : MulChar (ZMod (p ^ 2)) ℂ, KernelChar p χ → ∀ N : ℕ, (p : ℝ) ^ 2 * T ^ 2 ≤ N →
        |∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d - ((p : ℝ) ^ 2 - p) / 2 * ∫ x, (cf 0 x).re|
          ≤ E * p ∧
        |∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d * (1 - wgt S cf L p χ d) -
          ((p : ℝ) ^ 2 - p) / 2 * ∫ x, ((cf 0 x).re - ∑ v ∈ S, ‖cf v x‖ ^ 2)| ≤ E * p

/-! ## Internal statements for Lemma 2 and Lemma 3 -/

/-- Fejér kernel facts. -/
def FejerStatement : Prop :=
  (∀ R : ℕ, Continuous (fejer R)) ∧
  (∀ (R : ℕ) (t : ℝ), 0 ≤ fejer R t) ∧
  (∀ (R : ℕ) (t : ℝ), fejer R (t + 1) = fejer R t) ∧
  (∀ (R : ℕ) (t : ℝ), fejer R (-t) = fejer R t) ∧
  (∀ R : ℕ, ∫ t in (0 : ℝ)..1, fejer R t = 1) ∧
  (∀ (R : ℕ) (t : ℝ),
    ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * ee (k * t) = fejer R t) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 1 ≤ R →
    ∫ t in (-(1 / 2) : ℝ)..(1 / 2), fejer R t * Real.sqrt |t| ≤ C / Real.sqrt R)

/-- Existence of the bump `ρ` of §2. -/
def BumpStatement : Prop := ∃ ρ : ℝ → ℝ, IsBump ρ

/-- Facts about `J₀`: bounds, decay and the Laplace transform. -/
def J0Statement : Prop :=
  Continuous J0 ∧ (∀ r, |J0 r| ≤ 1) ∧ (∀ r, J0 (-r) = J0 r) ∧ J0 0 = 1 ∧
  (∀ r, |J0 r - 1| ≤ r ^ 2 / 4) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → |J0 r| ≤ C / Real.sqrt r) ∧
  (∀ lam c : ℝ, 0 < lam → 0 ≤ c →
    IntegrableOn (fun a => Real.exp (-(lam * a)) * J0 (a * c)) (Set.Ioi 0) ∧
    ∫ a in Set.Ioi (0 : ℝ), Real.exp (-(lam * a)) * J0 (a * c) = 1 / Real.sqrt (lam ^ 2 + c ^ 2))

/-- Display (2): averaging a plane wave over the circle. -/
def BesselPlaneStatement : Prop :=
  ∀ σ x : ℝ, besselG σ x = (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (1 - Real.cos (Real.exp (-σ) * Real.sin θ)) * Real.cos (Real.exp (-σ) * x * Real.cos θ)

/-- Elementary properties of the multiplier `m`. -/
def MultStatement : Prop :=
  (∀ τ : ℝ, ‖mult τ‖ = 1) ∧ mult 0 = 1 ∧ (∀ τ : ℝ, mult (-τ) = starRingEnd ℂ (mult τ))

/-- Lemma 2: the label transform of `G` is `m` times the label transform of `B`. -/
def MellinStatement : Prop :=
  ∀ ξ x : ℝ, x ≠ 0 → Integrable (fun σ => besselG σ x) ∧
    ∫ σ, (besselG σ x : ℂ) * ee (-(ξ * σ)) = mult (2 * Real.pi * ξ) * betaF ξ x

/-- Facts about the annulus slice `B_σ(x)`, its label mean `ℓ`, the periodization and `β_ξ`. -/
def AnnulusStatement : Prop :=
  Measurable (Function.uncurry annB) ∧
  (∀ σ x, 0 ≤ annB σ x ∧ annB σ x ≤ 1) ∧
  (∀ σ x, annB σ (-x) = annB σ x) ∧
  (∀ x, x ≠ 0 → Integrable (fun σ => annB σ x)) ∧
  (∀ x, x ≠ 0 → ellF x = Real.log (1 + (x ^ 2)⁻¹) / 2) ∧
  (∀ x, 0 ≤ ellF x) ∧
  (∀ x, x ≠ 0 → ellF x ≤ 1 / (2 * x ^ 2)) ∧
  Integrable ellF ∧ ∫ x, ellF x = Real.pi ∧
  (∀ σ, Integrable (annB σ) ∧ ∫ x, annB σ x ≤ 2 * Real.exp (-|σ|)) ∧
  (∀ x δ, x ≠ 0 → ∫ σ, |annB (σ - δ) x - annB σ x| ≤ 2 * min |δ| (ellF x)) ∧
  (∀ σ u, ∫ x, |annB σ (x - u) - annB σ x| ≤ min (4 * |u|) (4 * Real.exp (-|σ|))) ∧
  (∀ T σ x, 1 ≤ T → x ≠ 0 → Summable (fun j : ℤ => annB (σ + j * T) x)) ∧
  (∀ T σ, 1 ≤ T → Integrable (fun x => max (perB T σ x - 1) 0) ∧
    ∫ x, max (perB T σ x - 1) 0 ≤ 5 * Real.exp (-T)) ∧
  (∀ ξ, Measurable (betaF ξ)) ∧
  (∀ ξ x, ‖betaF ξ x‖ ≤ ellF x) ∧ (∀ x, betaF 0 x = ellF x) ∧
  (∀ ξ x, betaF (-ξ) x = starRingEnd ℂ (betaF ξ x)) ∧ (∀ ξ x, betaF ξ (-x) = betaF ξ x)

/-- Structural properties of the coefficients `b_l`. -/
def CoeffStatement : Prop :=
  ∀ ρ : ℝ → ℝ, IsBump ρ → ∀ T : ℝ, 1 ≤ T → ∀ (J : ℕ) (l : ℤ),
    ContDiff ℝ 2 (bL ρ T J l) ∧
    (∀ x, T ^ 2 < |x| → bL ρ T J l x = 0) ∧
    (∀ x, bL ρ T J l (-x) = bL ρ T J l x) ∧
    (∀ x, bL ρ T J (-l) x = starRingEnd ℂ (bL ρ T J l x)) ∧
    (∀ x, (bL ρ T J 0 x).im = 0 ∧ 0 ≤ (bL ρ T J 0 x).re) ∧
    ((J : ℤ) < |l| → bL ρ T J l = 0)

/-- Display (5) and the lower bound for the mass in (4). -/
def CoeffMassStatement : Prop :=
  ∀ ρ : ℝ → ℝ, IsBump ρ → ∃ C c T₀ : ℝ, 0 < C ∧ 0 < c ∧ ∀ T : ℝ, T₀ ≤ T → ∀ J : ℕ,
    Summable (fun j : ℤ => (bL ρ T J 0 j).re) ∧
    ∑' j : ℤ, (bL ρ T J 0 j).re ≤ C * Real.log T / T ∧
    c / T ≤ ∫ x, (bL ρ T J 0 x).re

/-- The label representation of `W` as a Fejér average of smoothed slices. -/
def WrepStatement : Prop :=
  ∀ ρ : ℝ → ℝ, IsBump ρ → ∀ T : ℝ, 1 ≤ T → ∀ (J : ℕ) (s x : ℝ),
    Integrable (fun σ => fejer J (s - σ / T) * smB ρ T σ x) ∧
    Wsum ρ T J s x = ((psiF ρ (x / T ^ 2) / (T * (1 + aT ρ T)) *
      ∫ σ, fejer J (s - σ / T) * smB ρ T σ x : ℝ) : ℂ)

/-- `0 ≤ W ≤ 1`. -/
def WboundStatement : Prop :=
  ∀ ρ : ℝ → ℝ, IsBump ρ → ∀ T : ℝ, 1 ≤ T → ∀ (J : ℕ) (s x : ℝ),
    (Wsum ρ T J s x).im = 0 ∧ 0 ≤ (Wsum ρ T J s x).re ∧ (Wsum ρ T J s x).re ≤ 1

/-- Spectral positivity of the output profile `Q` (display (6)), and of `b̂₀`. -/
def QposStatement : Prop :=
  ∀ ρ : ℝ → ℝ, IsBump ρ → ∀ T : ℝ, 1 ≤ T → ∀ J : ℕ,
    (∀ s y : ℝ,
      (∑ l ∈ Finset.Icc (-(J : ℤ)) J, mult (2 * Real.pi * l / T) * 𝓕 (bL ρ T J l) y *
        ee (l * s)).im = 0 ∧
      0 ≤ (∑ l ∈ Finset.Icc (-(J : ℤ)) J, mult (2 * Real.pi * l / T) * 𝓕 (bL ρ T J l) y *
        ee (l * s)).re) ∧
    (∀ y : ℝ, (𝓕 (bL ρ T J 0) y).im = 0 ∧ 0 ≤ (𝓕 (bL ρ T J 0) y).re)

/-- The integrated rounding variance in (4). -/
def VarStatement : Prop :=
  ∀ ρ : ℝ → ℝ, IsBump ρ → ∃ C T₀ : ℝ, 0 < C ∧ ∀ T : ℝ, T₀ ≤ T → ∀ J : ℕ, T ^ 8 ≤ J →
    ∫ x, ((bL ρ T J 0 x).re - ∑ l ∈ Finset.Icc (-(J : ℤ)) J, ‖bL ρ T J l x‖ ^ 2) ≤
      C * Real.log T / T ^ 3

/-- Fourier coefficients of the sawtooth phases `e(α{t})` (used in §3). -/
def SawStatement : Prop :=
  (∀ α : ℝ, HasSum (fun k : ℤ => ‖sawCoeff α k‖ ^ 2) 1) ∧
  (∀ (α : ℝ) (k : ℤ), sawCoeff (-α) (-k) = starRingEnd ℂ (sawCoeff α k)) ∧
  (∀ m k : ℤ, sawCoeff m k = if k = m then 1 else 0) ∧
  (∀ (α : ℝ) (R : ℕ) (u : ℝ),
    ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * sawCoeff α k * ee (k * u) =
      ∫ t in (0 : ℝ)..1, (fejer R (u - t) : ℂ) * saw α t)

end ChowlaOpus
