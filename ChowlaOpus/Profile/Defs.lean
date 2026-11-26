module

public import ChowlaOpus.Basic

@[expose] public section

/-!
# Definitions for §1–§2 of the paper (Lemma 2 and Lemma 3)

Conventions.
* The label variable `σ ∈ ℝ` is the logarithm of the radius; the annulus slice is
  `B_σ(x) = 1{|x| ≤ e^σ ≤ √(1+x²)}` (`annB σ x`).
* The label transform at (cyclic) frequency `ξ` is `∫ v(σ) e(-ξσ) dσ`
  (angular frequency `τ = 2πξ`).
* In Lemma 3 the label has period `T`; after rescaling `σ = T s` the label `s` has period one,
  and the `l`-th mode corresponds to `ξ = l / T`.
* `h = (T²)⁻¹`, `X = T²`.
-/

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

/-! ## The annulus slice and its label transforms -/

/-- Horizontal slice of the annulus: `B_σ(x) = 1{|x| ≤ e^σ ∧ e^{2σ} ≤ 1 + x²}`. -/
noncomputable def annB (σ x : ℝ) : ℝ :=
  if |x| ≤ Real.exp σ ∧ Real.exp σ ^ 2 ≤ 1 + x ^ 2 then 1 else 0

/-- Label mean `ℓ(x) = ∫ B_σ(x) dσ` (equal to `½ log(1 + x⁻²)` for `x ≠ 0`). -/
noncomputable def ellF (x : ℝ) : ℝ := ∫ σ, annB σ x

/-- Label transform of the slice at cyclic frequency `ξ`: `β_ξ(x) = ∫ B_σ(x) e(-ξσ) dσ`. -/
noncomputable def betaF (ξ x : ℝ) : ℂ := ∫ σ, (annB σ x : ℂ) * ee (-(ξ * σ))

/-- Periodization in the label with period `T`: `P_σ(x) = ∑_j B_{σ + jT}(x)`. -/
noncomputable def perB (T σ x : ℝ) : ℝ := ∑' j : ℤ, annB (σ + j * T) x

/-! ## Bessel profile and the multiplier (Lemma 2) -/

/-- `J₀(r) = (1/2π) ∫_0^{2π} cos(r cos θ) dθ`. -/
noncomputable def J0 (r : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos (r * Real.cos θ)

/-- `G_σ(x) = J₀(e^{-σ}|x|) - J₀(e^{-σ}√(1+x²))`. -/
noncomputable def besselG (σ x : ℝ) : ℝ :=
  J0 (Real.exp (-σ) * |x|) - J0 (Real.exp (-σ) * Real.sqrt (1 + x ^ 2))

/-- The unimodular multiplier `m(τ) = 2^{iτ} Γ(1 + iτ/2) / Γ(1 - iτ/2)`. -/
noncomputable def mult (τ : ℝ) : ℂ :=
  (2 : ℂ) ^ (Complex.I * τ) * Complex.Gamma (1 + Complex.I * τ / 2) /
    Complex.Gamma (1 - Complex.I * τ / 2)

/-! ## The bump and the profile coefficients (Lemma 3) -/

/-- An even nonnegative smooth probability density supported in `[-1,1]` with real,
nonnegative Fourier transform, maximal at `0`. -/
structure IsBump (ρ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ ρ
  nonneg : ∀ x, 0 ≤ ρ x
  even : ∀ x, ρ (-x) = ρ x
  supp : ∀ x, 1 ≤ |x| → ρ x = 0
  integral_eq : ∫ x, ρ x = 1
  fourier_im : ∀ y, (𝓕 (fun x => (ρ x : ℂ)) y).im = 0
  fourier_nonneg : ∀ y, 0 ≤ (𝓕 (fun x => (ρ x : ℂ)) y).re
  le_at_zero : ∀ x, ρ x ≤ ρ 0

/-- `ψ(x) = ρ(x)/ρ(0)`. -/
noncomputable def psiF (ρ : ℝ → ℝ) (x : ℝ) : ℝ := ρ x / ρ 0

/-- `ρ_h(x) = h⁻¹ ρ(x/h)`. -/
noncomputable def rhoH (ρ : ℝ → ℝ) (h x : ℝ) : ℝ := ρ (x / h) / h

/-- The scale `h = T⁻²`. -/
noncomputable def hT (T : ℝ) : ℝ := (T ^ 2)⁻¹

/-- Normalization constant `a = 8 ρ(0) T² e^{-T}` (dominates `‖ρ_h‖_∞ · ∫ (P_σ - 1)₊`). -/
noncomputable def aT (ρ : ℝ → ℝ) (T : ℝ) : ℝ := 8 * ρ 0 * T ^ 2 * Real.exp (-T)

/-- Physically smoothed slice `(ρ_h ∗ B_σ)(x) = ∫ ρ_h(y) B_σ(x - y) dy`. -/
noncomputable def smB (ρ : ℝ → ℝ) (T σ x : ℝ) : ℝ :=
  ∫ y, rhoH ρ (hT T) y * annB σ (x - y)

/-- Physically smoothed Bessel profile `(ρ_h ∗ G_σ)(x) = ∫ ρ_h(y) G_σ(x - y) dy`. -/
noncomputable def smG (ρ : ℝ → ℝ) (T σ x : ℝ) : ℝ :=
  ∫ y, rhoH ρ (hT T) y * besselG σ (x - y)

/-- The label coefficients of Lemma 3 (label rescaled to period one):
`b_l(x) = (φ_J(l) / (T(1+a))) ψ(x/T²) (ρ_h ∗ β_{l/T})(x)`, where `φ_J` is the Fejér coefficient. -/
noncomputable def bL (ρ : ℝ → ℝ) (T : ℝ) (J : ℕ) (l : ℤ) (x : ℝ) : ℂ :=
  ((fejerCoeff J l / (T * (1 + aT ρ T)) * psiF ρ (x / T ^ 2) : ℝ) : ℂ) *
    ∫ y, (rhoH ρ (hT T) y : ℂ) * betaF ((l : ℝ) / T) (x - y)

/-- The profile `W_s(x) = ∑_{|l| ≤ J} b_l(x) e(l s)` (period one in `s`). -/
noncomputable def Wsum (ρ : ℝ → ℝ) (T : ℝ) (J : ℕ) (s x : ℝ) : ℂ :=
  ∑ l ∈ Finset.Icc (-(J : ℤ)) J, bL ρ T J l x * ee (l * s)

/-- The output profile `Q_s(x) = ∑_{|l| ≤ J} m(2πl/T) b_l(x) e(l s)` of display (6). -/
noncomputable def Qsum (ρ : ℝ → ℝ) (T : ℝ) (J : ℕ) (s x : ℝ) : ℂ :=
  ∑ l ∈ Finset.Icc (-(J : ℤ)) J, mult (2 * Real.pi * l / T) * bL ρ T J l x * ee (l * s)

/-! ## Auxiliary circle coordinates (§3) -/

/-- The sawtooth phase `t ↦ e(α {t})`, one-periodic in `t`. -/
noncomputable def saw (α t : ℝ) : ℂ := ee (α * Int.fract t)

/-- Fourier coefficients of `saw α` on `[0, 1]`. -/
noncomputable def sawCoeff (α : ℝ) (k : ℤ) : ℂ :=
  ∫ t in (0 : ℝ)..1, saw α t * ee (-((k : ℝ) * t))

end ChowlaOpus
