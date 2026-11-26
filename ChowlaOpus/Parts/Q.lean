module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff ComplexOrder
open Real MeasureTheory

namespace ChowlaOpus.QAux

open ChowlaOpus

/-! ### Generalities -/

lemma cnonneg_iff {z : ℂ} : 0 ≤ z ↔ z.im = 0 ∧ 0 ≤ z.re :=
  ⟨fun h => ⟨(Complex.nonneg_iff.1 h).2.symm, (Complex.nonneg_iff.1 h).1⟩,
    fun h => Complex.nonneg_iff.2 ⟨h.2, h.1.symm⟩⟩

lemma integral_cnonneg {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : ∀ a, 0 ≤ f a) : 0 ≤ ∫ a, f a ∂μ := by
  have hfe : ∫ a, f a ∂μ = ∫ a, ((f a).re : ℂ) ∂μ := by
    refine integral_congr_ae (ae_of_all _ fun a => ?_)
    apply Complex.ext
    · simp
    · simp [(cnonneg_iff.1 (hf a)).1]
  rw [hfe, integral_complex_ofReal]
  exact Complex.zero_le_real.2 (integral_nonneg fun a => (cnonneg_iff.1 (hf a)).2)

lemma continuous_ee : Continuous ee := by unfold ee; fun_prop

lemma ae_ne' (x : ℝ) : ∀ᵐ y : ℝ, y ≠ x := by
  rw [ae_iff]; simp

lemma le_abs_of_nmem {c x : ℝ} (hx : x ∉ Set.Icc (-c) c) : c ≤ |x| := by
  by_contra h
  push Not at h
  exact hx ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

lemma abs_one_sub_cos_le (u : ℝ) : |1 - cos u| ≤ 2 := by
  rw [abs_le]; constructor <;> linarith [cos_le_one u, neg_one_le_cos u]

lemma ofReal_cos_eq_ee (t : ℝ) : ((cos (2 * π * t) : ℝ) : ℂ) = (ee t + ee (-t)) / 2 := by
  rw [Complex.ofReal_cos, Complex.cos]
  unfold ee
  congr 2
  · congr 1; push_cast; ring
  · congr 1; push_cast; ring

/-! ### The bump -/

section bump

variable {ρ : ℝ → ℝ} {T : ℝ}

lemma hT_pos (hT1 : 1 ≤ T) : 0 < hT T := by
  unfold ChowlaOpus.hT; have : 0 < T := by linarith
  positivity

lemma hT_le_one (hT1 : 1 ≤ T) : hT T ≤ 1 := by
  unfold ChowlaOpus.hT; apply inv_le_one_of_one_le₀; nlinarith

lemma rho_dil_zero (hρ : IsBump ρ) {c x : ℝ} (hc : 0 < c) (hx : c ≤ |x|) : ρ (x / c) = 0 := by
  apply hρ.supp
  rw [abs_div, abs_of_pos hc, le_div_iff₀ hc, one_mul]; exact hx

lemma rhoH_nonneg (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (y : ℝ) : 0 ≤ rhoH ρ h y :=
  div_nonneg (hρ.nonneg _) hh.le

lemma rhoH_le (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (y : ℝ) : rhoH ρ h y ≤ ρ 0 / h :=
  div_le_div_of_nonneg_right (hρ.le_at_zero _) hh.le

lemma rhoH_eq_zero (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) {y : ℝ} (hy : h ≤ |y|) :
    rhoH ρ h y = 0 := by
  unfold rhoH; rw [rho_dil_zero hρ hh hy, zero_div]

lemma rhoH_cont (hρ : IsBump ρ) {h : ℝ} : Continuous (rhoH ρ h) := by
  have := hρ.smooth.continuous
  unfold rhoH; fun_prop

lemma rhoH_hcs (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : HasCompactSupport (rhoH ρ h) :=
  HasCompactSupport.intro (isCompact_Icc (a := -h) (b := h))
    (fun _ hy => rhoH_eq_zero hρ hh (le_abs_of_nmem hy))

lemma rhoH_integrable (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : Integrable (rhoH ρ h) :=
  (rhoH_cont hρ).integrable_of_hasCompactSupport (rhoH_hcs hρ hh)

lemma rhoH_even (hρ : IsBump ρ) (h y : ℝ) : rhoH ρ h (-y) = rhoH ρ h y := by
  unfold rhoH; rw [neg_div, hρ.even]

lemma rhoH_integral (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : ∫ y, rhoH ρ h y = 1 := by
  unfold rhoH
  rw [integral_div, Measure.integral_comp_div ρ h, hρ.integral_eq, abs_of_pos hh, smul_eq_mul,
    mul_one, div_self hh.ne']

lemma rhoH_mul_integrable (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun y => rhoH ρ h y * f y) :=
  ((rhoH_cont hρ).mul hf).integrable_of_hasCompactSupport (rhoH_hcs hρ hh).mul_right

lemma psi_zero (hρ : IsBump ρ) (hT1 : 1 ≤ T) {x : ℝ} (hx : T ^ 2 ≤ |x|) :
    psiF ρ (x / T ^ 2) = 0 := by
  have : 0 < T ^ 2 := by have : 0 < T := by linarith
                         positivity
  unfold psiF; rw [rho_dil_zero hρ this hx, zero_div]

lemma psiF_meas (hρ : IsBump ρ) : Measurable (psiF ρ) := by
  have := hρ.smooth.continuous
  exact (by unfold psiF; fun_prop : Continuous (psiF ρ)).measurable

lemma psi_cont (hρ : IsBump ρ) : Continuous (fun x => psiF ρ (x / T ^ 2)) := by
  have := hρ.smooth.continuous
  unfold psiF; fun_prop

lemma psi_hcs (hρ : IsBump ρ) (hT1 : 1 ≤ T) : HasCompactSupport (fun x => psiF ρ (x / T ^ 2)) :=
  HasCompactSupport.intro (isCompact_Icc (a := -(T ^ 2)) (b := T ^ 2))
    (fun _ hx => psi_zero hρ hT1 (le_abs_of_nmem hx))

lemma psi_integrable (hρ : IsBump ρ) (hT1 : 1 ≤ T) : Integrable (fun x => psiF ρ (x / T ^ 2)) :=
  (psi_cont hρ).integrable_of_hasCompactSupport (psi_hcs hρ hT1)

lemma rho_dil_hcs (hρ : IsBump ρ) {c : ℝ} (hc : 0 < c) :
    HasCompactSupport (fun x => (ρ (x / c) : ℂ)) :=
  HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c))
    (fun _ hx => by rw [rho_dil_zero hρ hc (le_abs_of_nmem hx), Complex.ofReal_zero])

lemma ee_rho_dil_integrable (hρ : IsBump ρ) {c : ℝ} (hc : 0 < c) (η : ℝ) :
    Integrable (fun x => ee (-(x * η)) * (ρ (x / c) : ℂ)) := by
  have := hρ.smooth.continuous
  have hee := continuous_ee
  exact (by fun_prop : Continuous (fun x => ee (-(x * η)) * (ρ (x / c) : ℂ))).integrable_of_hasCompactSupport
    (rho_dil_hcs hρ hc).mul_left

lemma FT_rho_nonneg (hρ : IsBump ρ) (η : ℝ) : 0 ≤ 𝓕 (fun u => (ρ u : ℂ)) η :=
  cnonneg_iff.2 ⟨hρ.fourier_im η, hρ.fourier_nonneg η⟩

/-- Fourier transform of a dilate. -/
lemma FT_dil {c : ℝ} (hc : 0 < c) (η : ℝ) :
    ∫ x, ee (-(x * η)) * (ρ (x / c) : ℂ) = (c : ℂ) * 𝓕 (fun u => (ρ u : ℂ)) (c * η) := by
  rw [fourier_eq_ee]
  have := Measure.integral_comp_div (fun u => ee (-(u * (c * η))) * (ρ u : ℂ)) c
  rw [abs_of_pos hc, Complex.real_smul] at this
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  rw [show x / c * (c * η) = x * η by field_simp]

/-! ### The cosine transform `Rr` of `ρ_h` -/

/-- `R(om) = ∫ ρ_h(y) cos(omy) dy`. -/
noncomputable def Rr (ρ : ℝ → ℝ) (T om : ℝ) : ℝ := ∫ y, rhoH ρ (hT T) y * cos (om * y)

lemma Rr_eq (hρ : IsBump ρ) (hT1 : 1 ≤ T) (om : ℝ) :
    Rr ρ T om = (𝓕 (fun u => (ρ u : ℂ)) (hT T * (om / (2 * π)))).re := by
  have hh := hT_pos hT1
  have hπ : (2 * π) ≠ 0 := by positivity
  have hint := ee_rho_dil_integrable hρ hh (om / (2 * π))
  have key := FT_dil (ρ := ρ) hh (om / (2 * π))
  have hre := integral_re hint
  rw [key] at hre
  have e : ∀ x, RCLike.re (ee (-(x * (om / (2 * π)))) * (ρ (x / hT T) : ℂ)) =
      ρ (x / hT T) * cos (om * x) := by
    intro x
    simp only [RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, ee_re]
    rw [show 2 * π * -(x * (om / (2 * π))) = -(x * (2 * π * (om / (2 * π)))) by ring,
      mul_div_cancel₀ om hπ, cos_neg, mul_comm x om, mul_comm]
  simp_rw [e] at hre
  unfold Rr rhoH
  have e2 : ∫ y, ρ (y / hT T) / hT T * cos (om * y) = (∫ y, ρ (y / hT T) * cos (om * y)) / hT T := by
    rw [← integral_div]; congr 1; ext y; ring
  rw [e2, hre]
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
  exact mul_div_cancel_left₀ _ hh.ne'

lemma Rr_nonneg (hρ : IsBump ρ) (hT1 : 1 ≤ T) (om : ℝ) : 0 ≤ Rr ρ T om := by
  rw [Rr_eq hρ hT1]; exact hρ.fourier_nonneg _

lemma Rr_abs_le (hρ : IsBump ρ) (hT1 : 1 ≤ T) (om : ℝ) : |Rr ρ T om| ≤ 1 := by
  have hh := hT_pos hT1
  unfold Rr
  calc |∫ y, rhoH ρ (hT T) y * cos (om * y)| ≤ ∫ y, |rhoH ρ (hT T) y * cos (om * y)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ y, rhoH ρ (hT T) y := by
        refine integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _)
          (rhoH_integrable hρ hh) (ae_of_all _ fun y => ?_)
        show |rhoH ρ (hT T) y * cos (om * y)| ≤ rhoH ρ (hT T) y
        rw [abs_mul, abs_of_nonneg (rhoH_nonneg hρ hh y)]
        exact mul_le_of_le_one_right (rhoH_nonneg hρ hh y) (abs_cos_le_one _)
    _ = 1 := rhoH_integral hρ hh

lemma Rr_meas (hρ : IsBump ρ) : Measurable (Rr ρ T) := by
  have hc := rhoH_cont hρ (h := hT T)
  have hcont : Continuous (fun p : ℝ × ℝ => rhoH ρ (hT T) p.2 * cos (p.1 * p.2)) := by fun_prop
  exact (hcont.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

lemma Sr_zero (hρ : IsBump ρ) (h om : ℝ) : ∫ y, rhoH ρ h y * sin (om * y) = 0 := by
  have h1 := integral_neg_eq_self (fun y => rhoH ρ h y * sin (om * y)) volume
  have e : ∀ y, rhoH ρ h (-y) * sin (om * -y) = -(rhoH ρ h y * sin (om * y)) := by
    intro y; rw [rhoH_even hρ, mul_neg, sin_neg]; ring
  simp only [e, integral_neg] at h1
  linarith

/-! ### Plane-wave formula for `smG` -/

lemma inner_eq (hρ : IsBump ρ) (hT1 : 1 ≤ T) (a θ x : ℝ) :
    ∫ y, rhoH ρ (hT T) y * ((1 - cos (a * sin θ)) * cos (a * (x - y) * cos θ)) =
      (1 - cos (a * sin θ)) * Rr ρ T (a * cos θ) * cos (a * cos θ * x) := by
  have hh := hT_pos hT1
  have e : ∀ y, rhoH ρ (hT T) y * ((1 - cos (a * sin θ)) * cos (a * (x - y) * cos θ)) =
      ((1 - cos (a * sin θ)) * cos (a * cos θ * x)) * (rhoH ρ (hT T) y * cos (a * cos θ * y)) +
      ((1 - cos (a * sin θ)) * sin (a * cos θ * x)) * (rhoH ρ (hT T) y * sin (a * cos θ * y)) := by
    intro y
    rw [show a * (x - y) * cos θ = a * cos θ * x - a * cos θ * y by ring, cos_sub]; ring
  simp_rw [e]
  rw [integral_add ((rhoH_mul_integrable hρ hh (by fun_prop)).const_mul _)
      ((rhoH_mul_integrable hρ hh (by fun_prop)).const_mul _), integral_const_mul,
    integral_const_mul, Sr_zero hρ]
  unfold Rr; ring

lemma plane_wave (hB : BesselPlaneStatement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) (σ x : ℝ) :
    smG ρ T σ x = (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π),
      (1 - cos (exp (-σ) * sin θ)) * Rr ρ T (exp (-σ) * cos θ) * cos (exp (-σ) * cos θ * x) := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  have hh := hT_pos hT1
  let G2 : ℝ → ℝ → ℝ := fun y θ =>
    rhoH ρ (hT T) y * ((1 - cos (exp (-σ) * sin θ)) * cos (exp (-σ) * (x - y) * cos θ))
  have hG2 : Integrable (Function.uncurry G2)
      (volume.prod (volume.restrict (Set.Ioc 0 (2 * π)))) := by
    refine Integrable.mono' ((rhoH_integrable hρ hh).mul_prod (integrable_const (2 : ℝ))) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have := rhoH_cont hρ (h := hT T)
      show Continuous (fun p : ℝ × ℝ => rhoH ρ (hT T) p.1 *
        ((1 - cos (exp (-σ) * sin p.2)) * cos (exp (-σ) * (x - p.1) * cos p.2)))
      fun_prop
    · filter_upwards with p
      simp only [Function.uncurry, G2, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (rhoH_nonneg hρ hh _)]
      apply mul_le_mul_of_nonneg_left _ (rhoH_nonneg hρ hh _)
      have h1 := abs_one_sub_cos_le (exp (-σ) * sin p.2)
      have h2 := abs_cos_le_one (exp (-σ) * (x - p.1) * cos p.2)
      calc |1 - cos (exp (-σ) * sin p.2)| * |cos (exp (-σ) * (x - p.1) * cos p.2)| ≤ 2 * 1 := by
            gcongr
        _ = 2 := by ring
  unfold smG
  simp_rw [hB σ, intervalIntegral.integral_of_le h2π]
  calc ∫ y, rhoH ρ (hT T) y * (1 / (2 * π) * ∫ θ in Set.Ioc 0 (2 * π),
          (1 - cos (exp (-σ) * sin θ)) * cos (exp (-σ) * (x - y) * cos θ))
      = ∫ y, 1 / (2 * π) * ∫ θ in Set.Ioc 0 (2 * π), G2 y θ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only [G2]
        rw [integral_const_mul]; ring
    _ = 1 / (2 * π) * ∫ θ in Set.Ioc 0 (2 * π), ∫ y, G2 y θ := by
        rw [integral_const_mul, integral_integral_swap hG2]
    _ = _ := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun θ => ?_)
        simp only [G2]
        exact inner_eq hρ hT1 _ θ x

/-! ### Fourier transform of a modulated dilate of `ψ` -/

/-- `P(om, y) = ∫ ψ(x/X) cos(omx) e(-xy) dx`. -/
noncomputable def Pm (ρ : ℝ → ℝ) (T om y : ℝ) : ℂ :=
  ∫ x, ee (-(x * y)) * ((psiF ρ (x / T ^ 2) * cos (om * x) : ℝ) : ℂ)

lemma Pm_eq (hρ : IsBump ρ) (hT1 : 1 ≤ T) (om y : ℝ) :
    Pm ρ T om y = (((ρ 0)⁻¹ / 2 * T ^ 2 : ℝ) : ℂ) *
      (𝓕 (fun u => (ρ u : ℂ)) (T ^ 2 * (y - om / (2 * π))) +
        𝓕 (fun u => (ρ u : ℂ)) (T ^ 2 * (y + om / (2 * π)))) := by
  have hX : 0 < T ^ 2 := by have : 0 < T := by linarith
                            positivity
  have hπ : (2 * π) ≠ 0 := by positivity
  have e : ∀ x, ee (-(x * y)) * ((psiF ρ (x / T ^ 2) * cos (om * x) : ℝ) : ℂ) =
      (((ρ 0)⁻¹ / 2 : ℝ) : ℂ) * (ee (-(x * (y - om / (2 * π)))) * (ρ (x / T ^ 2) : ℂ) +
        ee (-(x * (y + om / (2 * π)))) * (ρ (x / T ^ 2) : ℂ)) := by
    intro x
    have hc : cos (om * x) = cos (2 * π * (x * (om / (2 * π)))) := by
      congr 1
      rw [show 2 * π * (x * (om / (2 * π))) = x * (2 * π * (om / (2 * π))) by ring,
        mul_div_cancel₀ om hπ, mul_comm]
    have e1 : ee (-(x * (y - om / (2 * π)))) = ee (-(x * y)) * ee (x * (om / (2 * π))) := by
      rw [← ee_add]; congr 1; ring
    have e2 : ee (-(x * (y + om / (2 * π)))) = ee (-(x * y)) * ee (-(x * (om / (2 * π)))) := by
      rw [← ee_add]; congr 1; ring
    rw [hc, Complex.ofReal_mul, ofReal_cos_eq_ee, e1, e2]
    unfold psiF; push_cast; ring
  unfold Pm
  simp_rw [e]
  rw [integral_const_mul, integral_add (ee_rho_dil_integrable hρ hX _)
    (ee_rho_dil_integrable hρ hX _), FT_dil hX, FT_dil hX]
  push_cast; ring

lemma Pm_nonneg (hρ : IsBump ρ) (hT1 : 1 ≤ T) (om y : ℝ) : 0 ≤ Pm ρ T om y := by
  rw [Pm_eq hρ hT1]
  refine mul_nonneg (Complex.zero_le_real.2 ?_) (add_nonneg (FT_rho_nonneg hρ _) (FT_rho_nonneg hρ _))
  exact mul_nonneg (div_nonneg (inv_nonneg.2 (hρ.nonneg 0)) two_pos.le) (sq_nonneg T)

/-! ### Positivity of the Fourier transform of a single label -/

/-- `Φ(σ, y) = 𝓕[x ↦ ψ(x/X) (ρ_h ∗ G_σ)(x)](y)`. -/
noncomputable def Phi (ρ : ℝ → ℝ) (T σ y : ℝ) : ℂ :=
  ∫ x, ee (-(x * y)) * ((psiF ρ (x / T ^ 2) * smG ρ T σ x : ℝ) : ℂ)

lemma Phi_eq (hB : BesselPlaneStatement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) (σ y : ℝ) :
    Phi ρ T σ y = ((1 / (2 * π) : ℝ) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π),
      (((1 - cos (exp (-σ) * sin θ)) * Rr ρ T (exp (-σ) * cos θ) : ℝ) : ℂ) *
        Pm ρ T (exp (-σ) * cos θ) y := by
  have h2π : (0 : ℝ) ≤ 2 * π := by positivity
  let H : ℝ → ℝ → ℂ := fun x θ => ee (-(x * y)) * ((psiF ρ (x / T ^ 2) *
    ((1 - cos (exp (-σ) * sin θ)) * Rr ρ T (exp (-σ) * cos θ) * cos (exp (-σ) * cos θ * x)) : ℝ) : ℂ)
  have hH : Integrable (Function.uncurry H) (volume.prod (volume.restrict (Set.Ioc 0 (2 * π)))) := by
    refine Integrable.mono' ((psi_integrable hρ hT1).abs.mul_prod (integrable_const (2 : ℝ))) ?_ ?_
    · apply Measurable.aestronglyMeasurable
      have hR := Rr_meas hρ (T := T)
      have hee : Measurable ee := continuous_ee.measurable
      have hψ : Measurable (psiF ρ) := psiF_meas hρ
      show Measurable (fun p : ℝ × ℝ => ee (-(p.1 * y)) * ((psiF ρ (p.1 / T ^ 2) *
        ((1 - cos (exp (-σ) * sin p.2)) * Rr ρ T (exp (-σ) * cos p.2) *
          cos (exp (-σ) * cos p.2 * p.1)) : ℝ) : ℂ))
      fun_prop
    · filter_upwards with p
      simp only [Function.uncurry, H, norm_mul, norm_ee, one_mul, Complex.norm_real,
        Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have h1 := abs_one_sub_cos_le (exp (-σ) * sin p.2)
      have h2 := Rr_abs_le hρ hT1 (exp (-σ) * cos p.2)
      have h3 := abs_cos_le_one (exp (-σ) * cos p.2 * p.1)
      calc |1 - cos (exp (-σ) * sin p.2)| * |Rr ρ T (exp (-σ) * cos p.2)| *
            |cos (exp (-σ) * cos p.2 * p.1)| ≤ 2 * 1 * 1 := by gcongr
        _ = 2 := by ring
  have step1 : ∀ x, ee (-(x * y)) * ((psiF ρ (x / T ^ 2) * smG ρ T σ x : ℝ) : ℂ) =
      ((1 / (2 * π) : ℝ) : ℂ) * ∫ θ in Set.Ioc 0 (2 * π), H x θ := by
    intro x
    rw [plane_wave hB hρ hT1 σ x, intervalIntegral.integral_of_le h2π]
    simp only [H]
    rw [integral_const_mul, integral_complex_ofReal, integral_const_mul]
    push_cast; ring
  unfold Phi
  rw [intervalIntegral.integral_of_le h2π]
  simp_rw [step1]
  rw [integral_const_mul, integral_integral_swap hH]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [H]
  unfold Pm
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  push_cast; ring

lemma Phi_nonneg (hB : BesselPlaneStatement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) (σ y : ℝ) :
    0 ≤ Phi ρ T σ y := by
  rw [Phi_eq hB hρ hT1 σ y]
  refine mul_nonneg (Complex.zero_le_real.2 (by positivity)) ?_
  rw [intervalIntegral.integral_of_le (by positivity)]
  refine integral_cnonneg fun θ => mul_nonneg (Complex.zero_le_real.2 ?_) (Pm_nonneg hρ hT1 _ y)
  exact mul_nonneg (by linarith [cos_le_one (exp (-σ) * sin θ)]) (Rr_nonneg hρ hT1 _)

end bump

/-! ### Bounds for the Bessel profile -/

/-- The locally integrable majorant `k(z) = 1 + |z|^{-1/2}`. -/
noncomputable def kq (z : ℝ) : ℝ := 1 + 1 / Real.sqrt |z|

lemma kq_ge_one (z : ℝ) : 1 ≤ kq z := by
  unfold kq; have : 0 ≤ 1 / √|z| := by positivity
  linarith

lemma kq_meas : Measurable kq := by
  unfold kq; fun_prop

lemma inv_sqrt_abs_intervalIntegrable {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun z : ℝ => 1 / √|z|) volume (-R) R := by
  have hpos : IntervalIntegrable (fun z : ℝ => 1 / √|z|) volume 0 R := by
    have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := R) (r := -(1 / 2))
      (by norm_num)
    refine IntervalIntegrable.congr ?_ this
    intro z hz
    rw [Set.uIoc_of_le hR] at hz
    simp only
    rw [abs_of_pos hz.1, Real.rpow_neg hz.1.le, ← Real.sqrt_eq_rpow, one_div]
  have hneg : IntervalIntegrable (fun z : ℝ => 1 / √|z|) volume (-R) 0 := by
    rw [IntervalIntegrable.iff_comp_neg]
    simpa [abs_neg] using hpos.symm
  exact hneg.trans hpos

lemma kq_integrableOn {R : ℝ} (hR : 0 ≤ R) : IntegrableOn kq (Set.Icc (-R) R) := by
  have h1 : IntegrableOn (fun z : ℝ => 1 / √|z|) (Set.Icc (-R) R) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1
      (inv_sqrt_abs_intervalIntegrable hR)
  have h0 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (-R) R) :=
    continuous_const.integrableOn_Icc
  exact h0.add h1

lemma G_unif (hB : BesselPlaneStatement) (σ z : ℝ) : |besselG σ z| ≤ exp (-σ) ^ 2 / 2 := by
  rw [hB σ z, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
  have hb : ‖∫ θ in (0 : ℝ)..(2 * π), (1 - cos (exp (-σ) * sin θ)) *
      cos (exp (-σ) * z * cos θ)‖ ≤ exp (-σ) ^ 2 / 2 * |2 * π - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ _
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : 0 ≤ 1 - cos (exp (-σ) * sin θ) := by linarith [cos_le_one (exp (-σ) * sin θ)]
    have h2 : 1 - cos (exp (-σ) * sin θ) ≤ (exp (-σ) * sin θ) ^ 2 / 2 := by
      linarith [one_sub_sq_div_two_le_cos (x := exp (-σ) * sin θ)]
    have h3 : (exp (-σ) * sin θ) ^ 2 ≤ exp (-σ) ^ 2 := by
      rw [mul_pow]; exact mul_le_of_le_one_right (by positivity) (sin_sq_le_one θ)
    rw [abs_of_nonneg h1]
    calc (1 - cos (exp (-σ) * sin θ)) * |cos (exp (-σ) * z * cos θ)|
        ≤ (1 - cos (exp (-σ) * sin θ)) * 1 := mul_le_mul_of_nonneg_left (abs_cos_le_one _) h1
      _ ≤ exp (-σ) ^ 2 / 2 := by linarith
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hb
  calc 1 / (2 * π) * |∫ θ in (0 : ℝ)..(2 * π), (1 - cos (exp (-σ) * sin θ)) *
        cos (exp (-σ) * z * cos θ)| ≤ 1 / (2 * π) * (exp (-σ) ^ 2 / 2 * (2 * π)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = exp (-σ) ^ 2 / 2 := by field_simp

lemma G_decay (hJ : J0Statement) : ∃ C : ℝ, 0 < C ∧ ∀ σ z : ℝ, z ≠ 0 →
    |besselG σ z| ≤ C * exp (σ / 2) * kq z := by
  obtain ⟨C, hC, hdec⟩ := hJ.2.2.2.2.2.1
  refine ⟨C, hC, fun σ z hz => ?_⟩
  have hs : √(exp (-σ)) = exp (-(σ / 2)) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (exp_pos _).le (exp_pos _).le, ← Real.exp_add]; ring_nf
  have hz' : 0 < |z| := abs_pos.2 hz
  have h1 : |J0 (exp (-σ) * |z|)| ≤ C * exp (σ / 2) * (1 / √|z|) := by
    have := hdec (exp (-σ) * |z|) (by positivity)
    rw [Real.sqrt_mul (exp_pos _).le, hs] at this
    calc _ ≤ C / (exp (-(σ / 2)) * √|z|) := this
      _ = C * exp (σ / 2) * (1 / √|z|) := by rw [Real.exp_neg]; field_simp
  have hq : 1 ≤ √(1 + z ^ 2) := Real.one_le_sqrt.2 (by nlinarith)
  have h2 : |J0 (exp (-σ) * √(1 + z ^ 2))| ≤ C * exp (σ / 2) := by
    have := hdec (exp (-σ) * √(1 + z ^ 2)) (by positivity)
    rw [Real.sqrt_mul (exp_pos _).le, hs] at this
    calc _ ≤ C / (exp (-(σ / 2)) * √(√(1 + z ^ 2))) := this
      _ ≤ C / (exp (-(σ / 2)) * 1) := by
          apply div_le_div_of_nonneg_left hC.le (by positivity)
          exact mul_le_mul_of_nonneg_left (Real.one_le_sqrt.2 hq) (exp_pos _).le
      _ = C * exp (σ / 2) := by rw [mul_one, Real.exp_neg]; field_simp
  unfold besselG kq
  calc |J0 (exp (-σ) * |z|) - J0 (exp (-σ) * √(1 + z ^ 2))|
      ≤ |J0 (exp (-σ) * |z|)| + |J0 (exp (-σ) * √(1 + z ^ 2))| := abs_sub _ _
    _ ≤ C * exp (σ / 2) * (1 / √|z|) + C * exp (σ / 2) := add_le_add h1 h2
    _ = C * exp (σ / 2) * (1 + 1 / √|z|) := by ring

lemma exp_half_le {σ : ℝ} (hσ : σ ≤ 0) : exp (σ / 2) ≤ 8 * (1 + σ ^ 2)⁻¹ := by
  have h := Real.quadratic_le_exp_of_nonneg (x := -σ / 2) (by linarith)
  have hprod : exp (σ / 2) * exp (-σ / 2) = 1 := by
    rw [← Real.exp_add, show σ / 2 + -σ / 2 = 0 by ring, Real.exp_zero]
  have hpos : 0 < exp (σ / 2) := exp_pos _
  have key : exp (σ / 2) * (1 + σ ^ 2) ≤ 8 := by nlinarith
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; exact key

lemma exp_two_le {σ : ℝ} (hσ : 0 ≤ σ) : exp (-σ) ^ 2 ≤ (1 + σ ^ 2)⁻¹ := by
  have h := Real.quadratic_le_exp_of_nonneg (x := 2 * σ) (by linarith)
  have hprod : exp (-σ) ^ 2 * exp (2 * σ) = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, show -σ + -σ + 2 * σ = 0 by ring, Real.exp_zero]
  have h1 : 1 + σ ^ 2 ≤ exp (2 * σ) := by nlinarith
  rw [← one_div, le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg (exp (-σ)))]

lemma G_bound (hJ : J0Statement) (hB : BesselPlaneStatement) : ∃ Cg : ℝ, 0 < Cg ∧
    ∀ σ z : ℝ, z ≠ 0 → |besselG σ z| ≤ kq z * (Cg * (1 + σ ^ 2)⁻¹) := by
  obtain ⟨C, hC, hdec⟩ := G_decay hJ
  refine ⟨8 * C + 1, by positivity, fun σ z hz => ?_⟩
  have hk := kq_ge_one z
  have hw : 0 ≤ (1 + σ ^ 2)⁻¹ := by positivity
  have hkw : 0 ≤ kq z * (1 + σ ^ 2)⁻¹ := mul_nonneg (by linarith) hw
  rcases le_total σ 0 with hσ | hσ
  · calc |besselG σ z| ≤ C * exp (σ / 2) * kq z := hdec σ z hz
      _ ≤ C * (8 * (1 + σ ^ 2)⁻¹) * kq z := by
          gcongr; exact exp_half_le hσ
      _ ≤ kq z * ((8 * C + 1) * (1 + σ ^ 2)⁻¹) := by linarith
  · calc |besselG σ z| ≤ exp (-σ) ^ 2 / 2 := G_unif hB σ z
      _ ≤ (1 + σ ^ 2)⁻¹ := by linarith [exp_two_le hσ, sq_nonneg (exp (-σ))]
      _ = 1 * (1 * (1 + σ ^ 2)⁻¹) := by ring
      _ ≤ kq z * ((8 * C + 1) * (1 + σ ^ 2)⁻¹) := by
          gcongr; linarith

/-! ### Step 2: bounds for the smoothed profile -/

section steps

variable {ρ : ℝ → ℝ} {T : ℝ}

lemma conv_bound_pt (hρ : IsBump ρ) (hT1 : 1 ≤ T) {x R : ℝ} (hx : |x| ≤ R) (y : ℝ) :
    rhoH ρ (hT T) y * kq (x - y) ≤
      (ρ 0 / hT T) * Set.indicator (Set.Icc (-(R + 1)) (R + 1)) kq (x - y) := by
  have hh := hT_pos hT1
  have hh1 := hT_le_one hT1
  have hk := kq_ge_one (x - y)
  by_cases hy : |y| < hT T
  · have hmem : x - y ∈ Set.Icc (-(R + 1)) (R + 1) := by
      rw [Set.mem_Icc, ← abs_le]
      calc |x - y| ≤ |x| + |y| := abs_sub _ _
        _ ≤ R + 1 := by linarith
    rw [Set.indicator_of_mem hmem]
    exact mul_le_mul_of_nonneg_right (rhoH_le hρ hh y) (by linarith)
  · push Not at hy
    rw [rhoH_eq_zero hρ hh hy, zero_mul]
    apply mul_nonneg (div_nonneg (hρ.nonneg 0) hh.le)
    exact Set.indicator_nonneg (fun z _ => by linarith [kq_ge_one z]) _

lemma dom_integrable (T ρ0 R x : ℝ) (hR : 0 ≤ R) :
    Integrable (fun y => (ρ0 / hT T) * Set.indicator (Set.Icc (-(R + 1)) (R + 1)) kq (x - y)) :=
  (((kq_integrableOn (by linarith : (0 : ℝ) ≤ R + 1)).integrable_indicator
    measurableSet_Icc).comp_sub_left x).const_mul _

lemma conv_integrable (hρ : IsBump ρ) (hT1 : 1 ≤ T) (x : ℝ) :
    Integrable (fun y => rhoH ρ (hT T) y * kq (x - y)) := by
  have hh := hT_pos hT1
  refine Integrable.mono' (dom_integrable T (ρ 0) |x| x (abs_nonneg x)) ?_ ?_
  · exact ((rhoH_cont hρ).measurable.mul
      (kq_meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (rhoH_nonneg hρ hh y)
      (by linarith [kq_ge_one (x - y)]))]
    exact conv_bound_pt hρ hT1 le_rfl y

/-- The uniform constant bounding `∫ ρ_h(y) k(x - y) dy` for `|x| ≤ T²`. -/
noncomputable def Kx (ρ : ℝ → ℝ) (T : ℝ) : ℝ :=
  (ρ 0 / hT T) * ∫ z in Set.Icc (-(T ^ 2 + 1)) (T ^ 2 + 1), kq z

lemma conv_le (hρ : IsBump ρ) (hT1 : 1 ≤ T) {x : ℝ} (hx : |x| ≤ T ^ 2) :
    ∫ y, rhoH ρ (hT T) y * kq (x - y) ≤ Kx ρ T := by
  calc ∫ y, rhoH ρ (hT T) y * kq (x - y)
      ≤ ∫ y, (ρ 0 / hT T) * Set.indicator (Set.Icc (-(T ^ 2 + 1)) (T ^ 2 + 1)) kq (x - y) :=
        integral_mono (conv_integrable hρ hT1 x) (dom_integrable T (ρ 0) _ x (sq_nonneg T))
          (fun y => conv_bound_pt hρ hT1 hx y)
    _ = Kx ρ T := by
        rw [integral_const_mul, integral_sub_left_eq_self
          (fun z => Set.indicator (Set.Icc (-(T ^ 2 + 1)) (T ^ 2 + 1)) kq z) volume x,
          integral_indicator measurableSet_Icc]
        rfl

lemma smG_bound (hρ : IsBump ρ) (hT1 : 1 ≤ T) {Cg : ℝ} (hCg : 0 < Cg)
    (hG : ∀ σ z : ℝ, z ≠ 0 → |besselG σ z| ≤ kq z * (Cg * (1 + σ ^ 2)⁻¹))
    (σ : ℝ) {x : ℝ} (hx : |x| ≤ T ^ 2) :
    |smG ρ T σ x| ≤ Kx ρ T * (Cg * (1 + σ ^ 2)⁻¹) := by
  have hh := hT_pos hT1
  unfold smG
  calc |∫ y, rhoH ρ (hT T) y * besselG σ (x - y)|
      ≤ ∫ y, |rhoH ρ (hT T) y * besselG σ (x - y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y, rhoH ρ (hT T) y * kq (x - y) * (Cg * (1 + σ ^ 2)⁻¹) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _)
          ((conv_integrable hρ hT1 x).mul_const _) ?_
        filter_upwards [ae_ne' x] with y hy
        rw [abs_mul, abs_of_nonneg (rhoH_nonneg hρ hh y), mul_assoc]
        exact mul_le_mul_of_nonneg_left (hG σ (x - y) (sub_ne_zero.2 (Ne.symm hy)))
          (rhoH_nonneg hρ hh y)
    _ = (∫ y, rhoH ρ (hT T) y * kq (x - y)) * (Cg * (1 + σ ^ 2)⁻¹) := integral_mul_const _ _
    _ ≤ Kx ρ T * (Cg * (1 + σ ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_right (conv_le hρ hT1 hx) (by positivity)

lemma smG_sm (hJ : J0Statement) (hρ : IsBump ρ) :
    StronglyMeasurable (fun p : ℝ × ℝ => smG ρ T p.2 p.1) := by
  have hc : Continuous (fun q : (ℝ × ℝ) × ℝ => rhoH ρ (hT T) q.2 * besselG q.1.2 (q.1.1 - q.2)) := by
    have := hρ.smooth.continuous
    have := hJ.1
    simp only [rhoH, besselG]
    fun_prop
  exact hc.stronglyMeasurable.integral_prod_right'

/-! ### Step 3: label representation -/

lemma step3 (hJ : J0Statement) (hMe : MellinStatement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) {Cg : ℝ}
    (hG : ∀ σ z : ℝ, z ≠ 0 → |besselG σ z| ≤ kq z * (Cg * (1 + σ ^ 2)⁻¹)) (ξ x : ℝ) :
    mult (2 * π * ξ) * ∫ y, (rhoH ρ (hT T) y : ℂ) * betaF ξ (x - y) =
      ∫ σ, ee (-(ξ * σ)) * (smG ρ T σ x : ℂ) := by
  have hh := hT_pos hT1
  have hint : Integrable (Function.uncurry fun (y σ : ℝ) =>
      (rhoH ρ (hT T) y : ℂ) * ((besselG σ (x - y) : ℂ) * ee (-(ξ * σ))))
      (volume.prod volume) := by
    refine Integrable.mono' ((conv_integrable hρ hT1 x).mul_prod
      (integrable_inv_one_add_sq.const_mul Cg)) ?_ ?_
    · apply Continuous.aestronglyMeasurable
      have := hρ.smooth.continuous
      have := hJ.1
      have := continuous_ee
      show Continuous (fun p : ℝ × ℝ =>
        (rhoH ρ (hT T) p.1 : ℂ) * ((besselG p.2 (x - p.1) : ℂ) * ee (-(ξ * p.2))))
      simp only [rhoH, besselG]
      fun_prop
    · have hae : ∀ᵐ p ∂(volume.prod volume : Measure (ℝ × ℝ)), p.1 ≠ x := by
        rw [ae_iff]
        have : {p : ℝ × ℝ | ¬p.1 ≠ x} = {x} ×ˢ Set.univ := by
          ext p; simp
        rw [this, Measure.prod_prod]; simp
      filter_upwards [hae] with p hp
      simp only [Function.uncurry, norm_mul, norm_ee, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (rhoH_nonneg hρ hh _)]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hG p.2 (x - p.1) (sub_ne_zero.2 (Ne.symm hp)))
        (rhoH_nonneg hρ hh _)
  calc mult (2 * π * ξ) * ∫ y, (rhoH ρ (hT T) y : ℂ) * betaF ξ (x - y)
      = ∫ y, (rhoH ρ (hT T) y : ℂ) * (mult (2 * π * ξ) * betaF ξ (x - y)) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only; ring
    _ = ∫ y, ∫ σ, (rhoH ρ (hT T) y : ℂ) * ((besselG σ (x - y) : ℂ) * ee (-(ξ * σ))) := by
        apply integral_congr_ae
        filter_upwards [ae_ne' x] with y hy
        rw [← (hMe ξ (x - y) (sub_ne_zero.2 (Ne.symm hy))).2, integral_const_mul]
    _ = ∫ σ, ∫ y, (rhoH ρ (hT T) y : ℂ) * ((besselG σ (x - y) : ℂ) * ee (-(ξ * σ))) :=
        integral_integral_swap hint
    _ = ∫ σ, ee (-(ξ * σ)) * (smG ρ T σ x : ℂ) := by
        refine integral_congr_ae (ae_of_all _ fun σ => ?_)
        simp only
        unfold smG
        rw [← integral_complex_ofReal, ← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only
        push_cast; ring

/-! ### Step 4: Fubini in `(x, σ)` -/

lemma step4_int (hJ : J0Statement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) {Cg : ℝ} (hCg : 0 < Cg)
    (hG : ∀ σ z : ℝ, z ≠ 0 → |besselG σ z| ≤ kq z * (Cg * (1 + σ ^ 2)⁻¹)) (ξ y : ℝ) :
    Integrable (Function.uncurry fun (x σ : ℝ) => ee (-(x * y)) *
      ((psiF ρ (x / T ^ 2) : ℂ) * (ee (-(ξ * σ)) * (smG ρ T σ x : ℂ)))) (volume.prod volume) := by
  refine Integrable.mono' ((psi_integrable hρ hT1).abs.mul_prod
    ((integrable_inv_one_add_sq.const_mul Cg).const_mul (Kx ρ T))) ?_ ?_
  · apply Measurable.aestronglyMeasurable
    have hm : Measurable (fun p : ℝ × ℝ => smG ρ T p.2 p.1) := (smG_sm hJ hρ).measurable
    have hee : Measurable ee := continuous_ee.measurable
    have hψ : Measurable (psiF ρ) := psiF_meas hρ
    show Measurable (fun p : ℝ × ℝ => ee (-(p.1 * y)) *
      ((psiF ρ (p.1 / T ^ 2) : ℂ) * (ee (-(ξ * p.2)) * (smG ρ T p.2 p.1 : ℂ))))
    fun_prop
  · filter_upwards with p
    simp only [Function.uncurry, norm_mul, norm_ee, one_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hx : |p.1| ≤ T ^ 2
    · exact mul_le_mul_of_nonneg_left (smG_bound hρ hT1 hCg hG p.2 hx) (abs_nonneg _)
    · push Not at hx
      rw [psi_zero hρ hT1 hx.le]
      simp only [abs_zero, zero_mul, le_refl]

lemma Phi_int (hJ : J0Statement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) {Cg : ℝ} (hCg : 0 < Cg)
    (hG : ∀ σ z : ℝ, z ≠ 0 → |besselG σ z| ≤ kq z * (Cg * (1 + σ ^ 2)⁻¹)) (ξ y : ℝ) :
    Integrable (fun σ => ee (-(ξ * σ)) * Phi ρ T σ y) := by
  have := (step4_int hJ hρ hT1 hCg hG ξ y).integral_prod_right
  refine this.congr (ae_of_all _ fun σ => ?_)
  simp only [Function.uncurry]
  unfold Phi
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only
  push_cast; ring

lemma core (hJ : J0Statement) (hMe : MellinStatement) (hρ : IsBump ρ) (hT1 : 1 ≤ T) {Cg : ℝ}
    (hCg : 0 < Cg) (hG : ∀ σ z : ℝ, z ≠ 0 → |besselG σ z| ≤ kq z * (Cg * (1 + σ ^ 2)⁻¹))
    (ξ c y : ℝ) :
    mult (2 * π * ξ) * ∫ x, ee (-(x * y)) * (((c * psiF ρ (x / T ^ 2) : ℝ) : ℂ) *
      ∫ y', (rhoH ρ (hT T) y' : ℂ) * betaF ξ (x - y')) =
    (c : ℂ) * ∫ σ, ee (-(ξ * σ)) * Phi ρ T σ y := by
  calc mult (2 * π * ξ) * ∫ x, ee (-(x * y)) * (((c * psiF ρ (x / T ^ 2) : ℝ) : ℂ) *
        ∫ y', (rhoH ρ (hT T) y' : ℂ) * betaF ξ (x - y'))
      = ∫ x, (c : ℂ) * ∫ σ, ee (-(x * y)) *
          ((psiF ρ (x / T ^ 2) : ℂ) * (ee (-(ξ * σ)) * (smG ρ T σ x : ℂ))) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        have h3 := step3 hJ hMe hρ hT1 hG ξ x
        calc mult (2 * π * ξ) * (ee (-(x * y)) * (((c * psiF ρ (x / T ^ 2) : ℝ) : ℂ) *
              ∫ y', (rhoH ρ (hT T) y' : ℂ) * betaF ξ (x - y')))
            = ee (-(x * y)) * ((c * psiF ρ (x / T ^ 2) : ℝ) : ℂ) *
              (mult (2 * π * ξ) * ∫ y', (rhoH ρ (hT T) y' : ℂ) * betaF ξ (x - y')) := by ring
          _ = ee (-(x * y)) * ((c * psiF ρ (x / T ^ 2) : ℝ) : ℂ) *
              ∫ σ, ee (-(ξ * σ)) * (smG ρ T σ x : ℂ) := by rw [h3]
          _ = (c : ℂ) * ∫ σ, ee (-(x * y)) *
              ((psiF ρ (x / T ^ 2) : ℂ) * (ee (-(ξ * σ)) * (smG ρ T σ x : ℂ))) := by
              rw [← integral_const_mul, ← integral_const_mul]
              refine integral_congr_ae (ae_of_all _ fun σ => ?_)
              simp only
              push_cast; ring
    _ = (c : ℂ) * ∫ x, ∫ σ, ee (-(x * y)) *
          ((psiF ρ (x / T ^ 2) : ℂ) * (ee (-(ξ * σ)) * (smG ρ T σ x : ℂ))) :=
        integral_const_mul _ _
    _ = (c : ℂ) * ∫ σ, ∫ x, ee (-(x * y)) *
          ((psiF ρ (x / T ^ 2) : ℂ) * (ee (-(ξ * σ)) * (smG ρ T σ x : ℂ))) := by
        rw [integral_integral_swap (step4_int hJ hρ hT1 hCg hG ξ y)]
    _ = (c : ℂ) * ∫ σ, ee (-(ξ * σ)) * Phi ρ T σ y := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun σ => ?_)
        simp only
        unfold Phi
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only
        push_cast; ring

end steps

end ChowlaOpus.QAux

namespace ChowlaOpus

theorem qposStatement_holds (hJ : J0Statement) (hB : BesselPlaneStatement)
    (hM : MultStatement) (hMe : MellinStatement) (_hA : AnnulusStatement)
    (hF : FejerStatement) : QposStatement := by
  intro ρ hρ T hT1 J
  obtain ⟨Cg, hCg, hG⟩ := QAux.G_bound hJ hB
  have hT0 : 0 < T := by linarith
  have hD : 0 < T * (1 + aT ρ T) := by
    have : 0 ≤ aT ρ T := by
      unfold aT; have := hρ.nonneg 0
      positivity
    positivity
  have hFT : ∀ l : ℤ, ∀ y, mult (2 * Real.pi * l / T) * 𝓕 (bL ρ T J l) y =
      ((fejerCoeff J l / (T * (1 + aT ρ T)) : ℝ) : ℂ) *
        ∫ σ, ee (-(((l : ℝ) / T) * σ)) * QAux.Phi ρ T σ y := by
    intro l y
    rw [fourier_eq_ee, show 2 * Real.pi * (l : ℝ) / T = 2 * Real.pi * ((l : ℝ) / T) by ring]
    exact QAux.core hJ hMe hρ hT1 hCg hG ((l : ℝ) / T) (fejerCoeff J l / (T * (1 + aT ρ T))) y
  refine ⟨fun s y => ?_, fun y => ?_⟩
  · have hsum : ∑ l ∈ Finset.Icc (-(J : ℤ)) J,
        mult (2 * Real.pi * l / T) * 𝓕 (bL ρ T J l) y * ee (l * s) =
        ∫ σ, (((T * (1 + aT ρ T))⁻¹ : ℝ) : ℂ) * ((fejer J (s - σ / T) : ℝ) : ℂ) *
          QAux.Phi ρ T σ y := by
      calc ∑ l ∈ Finset.Icc (-(J : ℤ)) J,
            mult (2 * Real.pi * l / T) * 𝓕 (bL ρ T J l) y * ee (l * s)
          = ∑ l ∈ Finset.Icc (-(J : ℤ)) J, ∫ σ,
              ((fejerCoeff J l / (T * (1 + aT ρ T)) : ℝ) : ℂ) * ee (l * s) *
                (ee (-(((l : ℝ) / T) * σ)) * QAux.Phi ρ T σ y) := by
            apply Finset.sum_congr rfl
            intro l _
            rw [hFT, integral_const_mul]; ring
        _ = ∫ σ, ∑ l ∈ Finset.Icc (-(J : ℤ)) J,
              ((fejerCoeff J l / (T * (1 + aT ρ T)) : ℝ) : ℂ) * ee (l * s) *
                (ee (-(((l : ℝ) / T) * σ)) * QAux.Phi ρ T σ y) := by
            rw [integral_finsetSum]
            intro l _
            exact (QAux.Phi_int hJ hρ hT1 hCg hG _ y).const_mul _
        _ = _ := by
            refine integral_congr_ae (ae_of_all _ fun σ => ?_)
            simp only
            rw [← hF.2.2.2.2.2.1 J (s - σ / T), Finset.mul_sum, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro l _
            have e : ee (l * s) * ee (-(((l : ℝ) / T) * σ)) = ee (l * (s - σ / T)) := by
              rw [← ee_add]; congr 1; ring
            rw [← e]
            push_cast; ring
    rw [hsum]
    have hnn : 0 ≤ ∫ σ, (((T * (1 + aT ρ T))⁻¹ : ℝ) : ℂ) * ((fejer J (s - σ / T) : ℝ) : ℂ) *
        QAux.Phi ρ T σ y :=
      QAux.integral_cnonneg fun σ => mul_nonneg (mul_nonneg
        (Complex.zero_le_real.2 (inv_nonneg.2 hD.le)) (Complex.zero_le_real.2 (hF.2.1 J _)))
        (QAux.Phi_nonneg hB hρ hT1 σ y)
    exact QAux.cnonneg_iff.1 hnn
  · have h0 := hFT 0 y
    simp only [Int.cast_zero, mul_zero, zero_div, zero_mul, neg_zero, ee_zero, one_mul] at h0
    rw [hM.2.1, one_mul] at h0
    rw [h0]
    have hnn : 0 ≤ ((fejerCoeff J 0 / (T * (1 + aT ρ T)) : ℝ) : ℂ) * ∫ σ, QAux.Phi ρ T σ y :=
      mul_nonneg (Complex.zero_le_real.2 (div_nonneg (fejerCoeff_nonneg _ _) hD.le))
        (QAux.integral_cnonneg fun σ => QAux.Phi_nonneg hB hρ hT1 σ y)
    exact QAux.cnonneg_iff.1 hnn

end ChowlaOpus
