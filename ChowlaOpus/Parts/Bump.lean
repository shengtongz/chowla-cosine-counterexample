module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff Convolution
open Real MeasureTheory

/-!
# The bump `ρ`

We take `φ` a normalized smooth bump supported in `(-1/2, 1/2)` and set `ρ = φ ⋆ φ`.
Then `𝓕 ρ = (𝓕 φ)²` with `𝓕 φ` real since `φ` is real and even.
-/

namespace ChowlaOpus.BumpAux

/-- The underlying bump function data. -/
noncomputable def bump0 : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

/-- The normalized bump `φ`. -/
noncomputable def phi : ℝ → ℝ := bump0.normed volume

lemma phi_contDiff : ContDiff ℝ ∞ phi := bump0.contDiff_normed

lemma phi_continuous : Continuous phi := bump0.continuous_normed

lemma phi_nonneg (x : ℝ) : 0 ≤ phi x := bump0.nonneg_normed x

lemma phi_neg (x : ℝ) : phi (-x) = phi x := bump0.normed_neg x

lemma phi_integral : ∫ x, phi x = 1 := bump0.integral_normed

lemma phi_hasCompactSupport : HasCompactSupport phi := bump0.hasCompactSupport_normed

lemma phi_integrable : Integrable phi := bump0.integrable_normed

lemma phi_eq_zero {x : ℝ} (hx : 1 / 2 ≤ |x|) : phi x = 0 := by
  have h := bump0.support_normed_eq (μ := volume)
  by_contra hne
  have hx' : x ∈ Function.support phi := hne
  rw [phi, h] at hx'
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx'
  have : bump0.rOut = 1 / 2 := rfl
  linarith

/-- Complex-valued version of `φ`. -/
noncomputable def phiC (x : ℝ) : ℂ := (phi x : ℂ)

lemma phiC_integrable : Integrable phiC := phi_integrable.ofReal

/-- `ρ = φ ⋆ φ`. -/
noncomputable def rho : ℝ → ℝ := phi ⋆[ContinuousLinearMap.mul ℝ ℝ] phi

lemma rho_apply (x : ℝ) : rho x = ∫ y, phi y * phi (x - y) := by
  simp [rho, convolution_def]

lemma rho_contDiff : ContDiff ℝ ∞ rho :=
  phi_hasCompactSupport.contDiff_convolution_left _ phi_contDiff
    phi_integrable.locallyIntegrable

lemma rho_nonneg (x : ℝ) : 0 ≤ rho x := by
  rw [rho_apply]
  exact integral_nonneg fun y => mul_nonneg (phi_nonneg _) (phi_nonneg _)

lemma rho_even (x : ℝ) : rho (-x) = rho x := by
  rw [rho_apply, rho_apply, ← integral_neg_eq_self]
  congr 1; ext y
  rw [phi_neg, show -x - -y = -(x - y) by ring, phi_neg]

lemma rho_supp (x : ℝ) (hx : 1 ≤ |x|) : rho x = 0 := by
  rw [rho_apply]
  have : ∀ y, phi y * phi (x - y) = 0 := by
    intro y
    by_cases hy : 1 / 2 ≤ |y|
    · rw [phi_eq_zero hy, zero_mul]
    · have : 1 / 2 ≤ |x - y| := by
        have := abs_sub_abs_le_abs_sub x y
        rw [not_le] at hy
        linarith
      rw [phi_eq_zero this, mul_zero]
  simp [this]

lemma rho_integral : ∫ x, rho x = 1 := by
  rw [rho]
  refine (integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) (μ := volume) (ν := volume)
    phi_integrable phi_integrable).trans ?_
  rw [phi_integral]
  simp

lemma phi_sq_integrable : Integrable (fun y => phi y ^ 2) := by
  have hc : Continuous (fun y => phi y ^ 2) := phi_continuous.pow 2
  exact hc.integrable_of_hasCompactSupport
    (phi_hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num))

lemma phi_mul_integrable (x : ℝ) : Integrable (fun y => phi y * phi (x - y)) :=
  (phi_continuous.mul (phi_continuous.comp (continuous_const.sub continuous_id)))
    |>.integrable_of_hasCompactSupport
      (phi_hasCompactSupport.mul_right (f' := fun y => phi (x - y)))

lemma rho_zero : rho 0 = ∫ y, phi y ^ 2 := by
  rw [rho_apply]
  congr 1; ext y
  rw [zero_sub, phi_neg, sq]

lemma rho_le_zero (x : ℝ) : rho x ≤ rho 0 := by
  rw [rho_zero, rho_apply]
  have hint : Integrable (fun y => (phi y ^ 2 + phi (x - y) ^ 2) / 2) :=
    (phi_sq_integrable.add (phi_sq_integrable.comp_sub_left x)).div_const 2
  calc ∫ y, phi y * phi (x - y) ≤ ∫ y, (phi y ^ 2 + phi (x - y) ^ 2) / 2 :=
        integral_mono (phi_mul_integrable x) hint
          (fun y => by nlinarith [sq_nonneg (phi y - phi (x - y))])
    _ = ∫ y, phi y ^ 2 := by
        rw [integral_div, integral_add phi_sq_integrable (phi_sq_integrable.comp_sub_left x),
          integral_sub_left_eq_self (fun y => phi y ^ 2)]
        ring

lemma rhoC_eq : (fun x => (rho x : ℂ)) = phiC ⋆[ContinuousLinearMap.mul ℂ ℂ] phiC := by
  ext x
  rw [rho_apply, convolution_def]
  simp only [ContinuousLinearMap.mul_apply', phiC]
  rw [← integral_complex_ofReal]
  push_cast
  rfl

lemma fourier_phiC_conj (w : ℝ) : starRingEnd ℂ (𝓕 phiC w) = 𝓕 phiC w := by
  rw [fourier_eq_ee, ← integral_conj, ← integral_neg_eq_self]
  congr 1; ext v
  rw [map_mul, show -(-v * w) = v * w by ring, ee_neg (v * w)]
  simp [phiC, phi_neg]

lemma fourier_phiC_im (w : ℝ) : (𝓕 phiC w).im = 0 :=
  Complex.conj_eq_iff_im.mp (fourier_phiC_conj w)

lemma fourier_rho (w : ℝ) : 𝓕 (fun x => (rho x : ℂ)) w = 𝓕 phiC w * 𝓕 phiC w := by
  rw [rhoC_eq, Real.fourier_mul_convolution_eq phiC_integrable phiC_integrable]

lemma isBump_rho : IsBump rho where
  smooth := rho_contDiff
  nonneg := rho_nonneg
  even := rho_even
  supp := rho_supp
  integral_eq := rho_integral
  fourier_im := fun y => by
    rw [fourier_rho, Complex.mul_im, fourier_phiC_im]; ring
  fourier_nonneg := fun y => by
    rw [fourier_rho, Complex.mul_re, fourier_phiC_im]
    nlinarith [sq_nonneg (𝓕 phiC y).re]
  le_at_zero := rho_le_zero

end ChowlaOpus.BumpAux

namespace ChowlaOpus

theorem bumpStatement_holds : BumpStatement := ⟨BumpAux.rho, BumpAux.isBump_rho⟩

end ChowlaOpus
