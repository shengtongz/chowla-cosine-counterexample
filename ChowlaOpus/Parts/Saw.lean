module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.SawAux

lemma continuous_ee : Continuous ee := by
  unfold ee; fun_prop

lemma measurable_saw (α : ℝ) : Measurable (saw α) := by
  unfold saw
  exact continuous_ee.measurable.comp (measurable_const.mul measurable_fract)

lemma norm_saw (α t : ℝ) : ‖saw α t‖ = 1 := norm_ee _

lemma intervalIntegrable_saw_mul_ee (α c : ℝ) :
    IntervalIntegrable (fun t => saw α t * ee (c * t)) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne ?_ ?_
  · exact ((measurable_saw α).mul
      (continuous_ee.measurable.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by simp [norm_saw, norm_ee]

lemma sawCoeff_eq_fourierCoeffOn (α : ℝ) (k : ℤ) :
    sawCoeff α k = fourierCoeffOn zero_lt_one (saw α) k := by
  rw [fourierCoeffOn_eq_integral, show (1 : ℝ) / (1 - 0) = 1 by norm_num, one_smul]
  unfold sawCoeff
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [smul_eq_mul]
  rw [fourier_coe_apply, mul_comm]
  unfold ee
  congr 2
  push_cast
  ring

/-- Parseval for the sawtooth phase. -/
lemma hasSum_sq_sawCoeff (α : ℝ) : HasSum (fun k : ℤ => ‖sawCoeff α k‖ ^ 2) 1 := by
  have hL2 : MemLp (saw α) 2 (volume.restrict (Set.Ioc 0 1)) :=
    MemLp.of_bound (measurable_saw α).aestronglyMeasurable 1
      (ae_of_all _ fun t => (norm_saw α t).le)
  have h := hasSum_sq_fourierCoeffOn zero_lt_one hL2
  simp_rw [← sawCoeff_eq_fourierCoeffOn] at h
  convert h using 1
  simp [norm_saw]

lemma sawCoeff_neg_neg (α : ℝ) (k : ℤ) :
    sawCoeff (-α) (-k) = starRingEnd ℂ (sawCoeff α k) := by
  unfold sawCoeff
  rw [← intervalIntegral.intervalIntegral_conj]
  refine intervalIntegral.integral_congr fun t _ => ?_
  unfold saw
  rw [map_mul, ← ee_neg, ← ee_neg]
  congr 2 <;> push_cast <;> ring

lemma integral_ee_int (n : ℤ) : ∫ t in (0 : ℝ)..1, ee (n * t) = if n = 0 then 1 else 0 := by
  split_ifs with hn
  · simp [hn, ee_zero]
  · have hc : (2 * Real.pi * Complex.I * n : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    have h1 : ∀ t : ℝ, ee (n * t) = Complex.exp ((2 * Real.pi * Complex.I * n : ℂ) * t) := by
      intro t; unfold ee; congr 1; push_cast; ring
    simp_rw [h1]
    rw [integral_exp_mul_complex hc]
    have h2 : Complex.exp ((2 * Real.pi * Complex.I * n : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← h1, mul_one, ee_intCast]
    rw [h2]
    simp

lemma sawCoeff_intCast (m k : ℤ) : sawCoeff m k = if k = m then 1 else 0 := by
  unfold sawCoeff
  have h : ∀ t : ℝ, saw m t * ee (-((k : ℝ) * t)) = ee (((m - k : ℤ) : ℝ) * t) := by
    intro t
    unfold saw
    rw [← Int.self_sub_floor, ← ee_add]
    have : (m : ℝ) * (t - ⌊t⌋) + -(k * t) = ((m - k : ℤ) : ℝ) * t + ((-(m * ⌊t⌋) : ℤ) : ℝ) := by
      push_cast; ring
    rw [this, ee_add_intCast]
  simp_rw [h]
  rw [integral_ee_int]
  by_cases hkm : k = m
  · simp [hkm]
  · have : m - k ≠ 0 := by omega
    simp [hkm, this]

/-- The Fejér kernel as an exponential sum. -/
lemma fejer_complex (R : ℕ) (x : ℝ) :
    (fejer R x : ℂ) = ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * ee (k * x) := by
  have hcos : ∀ k : ℤ, ((Real.cos (2 * Real.pi * k * x) : ℝ) : ℂ) =
      (ee (k * x) + ee (-(k * x))) / 2 := by
    intro k
    rw [ee_neg, Complex.add_conj, ee_re]
    push_cast
    ring_nf
  have hS : ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * ee (-(k * x)) =
      ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * ee (k * x) := by
    refine Finset.sum_nbij' (fun k => -k) (fun k => -k) ?_ ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
    · intro k _; simp
    · intro k _; simp
    · intro k _; simp [fejerCoeff_neg]
  unfold fejer
  rw [Complex.ofReal_sum]
  simp_rw [Complex.ofReal_mul, hcos]
  have hsplit : ∀ k : ℤ, (fejerCoeff R k : ℂ) * ((ee (k * x) + ee (-(k * x))) / 2) =
      (fejerCoeff R k : ℂ) * ee (k * x) / 2 + (fejerCoeff R k : ℂ) * ee (-(k * x)) / 2 := by
    intro k; ring
  simp_rw [hsplit, Finset.sum_add_distrib, ← Finset.sum_div, hS]
  ring

lemma fejer_sum_sawCoeff (α : ℝ) (R : ℕ) (u : ℝ) :
    ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * sawCoeff α k * ee (k * u) =
      ∫ t in (0 : ℝ)..1, (fejer R (u - t) : ℂ) * saw α t := by
  have h : ∀ t : ℝ, (fejer R (u - t) : ℂ) * saw α t = ∑ k ∈ Finset.Icc (-(R : ℤ)) R,
      ((fejerCoeff R k : ℂ) * ee (k * u)) * (saw α t * ee (-(k : ℝ) * t)) := by
    intro t
    rw [fejer_complex, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show (k : ℝ) * (u - t) = k * u + -(k : ℝ) * t by ring, ee_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_finsetSum fun k _ =>
    (intervalIntegrable_saw_mul_ee α _).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  unfold sawCoeff
  simp_rw [neg_mul]
  ring

end ChowlaOpus.SawAux

namespace ChowlaOpus

theorem sawStatement_holds : SawStatement :=
  ⟨SawAux.hasSum_sq_sawCoeff, SawAux.sawCoeff_neg_neg, SawAux.sawCoeff_intCast,
    SawAux.fejer_sum_sawCoeff⟩

end ChowlaOpus
