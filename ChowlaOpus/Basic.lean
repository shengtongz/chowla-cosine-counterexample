module

public import Mathlib

@[expose] public section

/-!
# Basic notation for the prime-square counterexample to Chowla's cosine conjecture

Notation shared by all components: `ee x = exp(2πix)`, the cosine sum `cosineSum`,
multiplicative independence, trigonometric polynomials in several variables, Fejér
coefficients and kernels, and the characters and Gauss-type sums modulo `p²` used in §4–§5.
-/

open scoped FourierTransform
open Real MeasureTheory

namespace ChowlaOpus

/-- `ee x = exp(2πix)`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

lemma ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma norm_ee (x : ℝ) : ‖ee x‖ = 1 := by
  unfold ee
  rw [Complex.norm_exp]
  simp

lemma ee_ne_zero (x : ℝ) : ee x ≠ 0 := Complex.exp_ne_zero _

lemma ee_intCast (n : ℤ) : ee n = 1 := by
  unfold ee
  have : 2 * (Real.pi : ℂ) * Complex.I * (n : ℝ) = n * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

lemma ee_add_intCast (x : ℝ) (n : ℤ) : ee (x + n) = ee x := by
  rw [ee_add, ee_intCast, mul_one]

lemma ee_neg (x : ℝ) : ee (-x) = starRingEnd ℂ (ee x) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast; ring

lemma ee_re (x : ℝ) : (ee x).re = Real.cos (2 * Real.pi * x) := by
  unfold ee
  have : 2 * (Real.pi : ℂ) * Complex.I * (x : ℝ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

lemma ee_im (x : ℝ) : (ee x).im = Real.sin (2 * Real.pi * x) := by
  unfold ee
  have : 2 * (Real.pi : ℂ) * Complex.I * (x : ℝ) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_im]

lemma ee_mul_intCast (x : ℝ) (n : ℤ) : ee (x * n) = ee x ^ n := by
  unfold ee
  rw [← Complex.exp_int_mul]
  congr 1; push_cast; ring

lemma fourier_eq_ee (f : ℝ → ℂ) (w : ℝ) : 𝓕 f w = ∫ v, ee (-(v * w)) * f v := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr 1; ext v
  simp only [smul_eq_mul, ee]
  congr 2
  push_cast; ring

/-- The cosine sum `f_A(t) = ∑_{a ∈ A} cos(2π a t)`. -/
noncomputable def cosineSum (A : Finset ℕ+) (t : ℝ) : ℝ :=
  ∑ a ∈ A, Real.cos (2 * Real.pi * ((a : ℕ) : ℝ) * t)

/-- Multiplicative independence of a finite family of naturals: the only integer exponent
vector giving a trivial rational product is zero. -/
def MultIndep {ι : Type*} [Fintype ι] (n : ι → ℕ) : Prop :=
  ∀ e : ι → ℤ, ∏ i, ((n i : ℚ) ^ e i) = 1 → e = 0

/-- Evaluation of a trigonometric polynomial on the torus `ℝ^k / ℤ^k` with frequency set `S`
and coefficients `f`. -/
noncomputable def trigEval {k : ℕ} (S : Finset (Fin k → ℤ)) (f : (Fin k → ℤ) → ℂ)
    (θ : Fin k → ℝ) : ℂ :=
  ∑ v ∈ S, f v * ee (∑ i, (v i : ℝ) * θ i)

/-! ## Fejér kernel (definitions only) -/

/-- Fejér coefficient `(1 - |k|/(R+1))₊`. -/
noncomputable def fejerCoeff (R : ℕ) (k : ℤ) : ℝ := max 0 (1 - |(k : ℝ)| / ((R : ℝ) + 1))

/-- Fejér kernel of degree `R` on `ℝ/ℤ`, as a cosine polynomial. -/
noncomputable def fejer (R : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(R : ℤ)) R, fejerCoeff R k * Real.cos (2 * Real.pi * k * t)

lemma fejerCoeff_nonneg (R : ℕ) (k : ℤ) : 0 ≤ fejerCoeff R k := le_max_left _ _

lemma fejerCoeff_le_one (R : ℕ) (k : ℤ) : fejerCoeff R k ≤ 1 := by
  unfold fejerCoeff
  apply max_le zero_le_one
  have : 0 ≤ |(k : ℝ)| / ((R : ℝ) + 1) := by positivity
  linarith

lemma fejerCoeff_zero (R : ℕ) : fejerCoeff R 0 = 1 := by simp [fejerCoeff]

lemma fejerCoeff_neg (R : ℕ) (k : ℤ) : fejerCoeff R (-k) = fejerCoeff R k := by
  simp [fejerCoeff, abs_neg]

lemma fejerCoeff_eq_zero (R : ℕ) (k : ℤ) (h : (R : ℤ) < |k|) : fejerCoeff R k = 0 := by
  unfold fejerCoeff
  apply max_eq_left
  have h' : (R : ℝ) + 1 ≤ |(k : ℝ)| := by
    have : (R : ℤ) + 1 ≤ |k| := h
    exact_mod_cast this
  have hpos : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  rw [sub_nonpos, le_div_iff₀ hpos]; linarith

/-! ## Characters modulo `p²` -/

/-- An even character mod `p²` which restricts to `1 + p t ↦ e(t/p)` on the kernel of reduction. -/
def KernelChar (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) : Prop :=
  χ (-1) = 1 ∧ ∀ t : ℤ, χ (((1 + (p : ℤ) * t : ℤ)) : ZMod (p ^ 2)) = ee ((t : ℝ) / p)

/-- The normalized Gauss phase `t_n = e(-n/p²) χ(n)^n` of display (7). -/
noncomputable def gaussPhase (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) (n : ℤ) : ℂ :=
  ee (-(n : ℝ) / (p : ℝ) ^ 2) * (χ (n : ZMod (p ^ 2))) ^ n

/-- Row sum `∑*_{r mod p²} χ(r)^n e(k r / p²)` over residues coprime to `p`. -/
noncomputable def rowSum (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) (n k : ℤ) : ℂ :=
  ∑ r ∈ (Finset.range (p ^ 2)).filter (fun r => Nat.Coprime r p),
    (χ (r : ZMod (p ^ 2))) ^ n * ee ((k : ℝ) * (r : ℝ) / (p : ℝ) ^ 2)

end ChowlaOpus
