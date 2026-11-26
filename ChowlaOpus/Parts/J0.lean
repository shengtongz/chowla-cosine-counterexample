module

public import ChowlaOpus.Statements

@[expose] public section

/-!
# Component J0: elementary properties of `J₀` and the plane-wave average (display (2))
-/

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.J0Aux

lemma continuous_integrand : Continuous (fun p : ℝ × ℝ => Real.cos (p.1 * Real.cos p.2)) := by
  fun_prop

lemma j0_continuous : Continuous J0 := by
  unfold J0
  have : Continuous fun r : ℝ => ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos (r * Real.cos θ) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ => Real.cos (r * Real.cos θ)) continuous_integrand _ _
  exact continuous_const.mul this

lemma j0_abs_le_one (r : ℝ) : |J0 r| ≤ 1 := by
  unfold J0
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (C := 1) (f := fun θ => Real.cos (r * Real.cos θ)) (fun θ _ => by
      simpa using Real.abs_cos_le_one _)
  rw [Real.norm_eq_abs] at h
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
  have hp : |2 * π - 0| = 2 * π := by rw [sub_zero, abs_of_pos (by positivity)]
  rw [hp, one_mul] at h
  calc 1 / (2 * π) * |∫ θ in (0:ℝ)..2 * π, Real.cos (r * Real.cos θ)|
      ≤ 1 / (2 * π) * (2 * π) := by gcongr
    _ = 1 := by field_simp

lemma j0_neg (r : ℝ) : J0 (-r) = J0 r := by
  unfold J0
  simp [neg_mul, Real.cos_neg]

lemma j0_zero : J0 0 = 1 := by
  unfold J0
  simp
  field_simp

lemma j0_sub_one (r : ℝ) : |J0 r - 1| ≤ r ^ 2 / 4 := by
  have hI : IntervalIntegrable (fun θ => Real.cos (r * Real.cos θ)) volume 0 (2 * π) :=
    (by fun_prop : Continuous fun θ => Real.cos (r * Real.cos θ)).intervalIntegrable _ _
  have hJ : J0 r - 1 = 1 / (2 * π) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.cos (r * Real.cos θ) - 1) := by
    unfold J0
    rw [intervalIntegral.integral_sub hI intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
    field_simp
  have hbound : ‖∫ θ in (0 : ℝ)..(2 * Real.pi), (Real.cos (r * Real.cos θ) - 1)‖ ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi), r ^ 2 / 2 * Real.cos θ ^ 2 := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by positivity)
    · refine Filter.Eventually.of_forall (fun θ _ => ?_)
      rw [Real.norm_eq_abs]
      have h1 := Real.one_sub_sq_div_two_le_cos (x := r * Real.cos θ)
      have h2 := Real.cos_le_one (r * Real.cos θ)
      rw [abs_of_nonpos (by linarith)]
      nlinarith
    · exact (by fun_prop : Continuous fun θ => r ^ 2 / 2 * Real.cos θ ^ 2).intervalIntegrable _ _
  have hcos : ∫ θ in (0 : ℝ)..(2 * Real.pi), r ^ 2 / 2 * Real.cos θ ^ 2 = r ^ 2 / 2 * π := by
    rw [intervalIntegral.integral_const_mul, integral_cos_sq]
    simp
  rw [hcos, Real.norm_eq_abs] at hbound
  rw [hJ, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
  calc 1 / (2 * π) * |∫ θ in (0:ℝ)..2 * π, (Real.cos (r * Real.cos θ) - 1)|
      ≤ 1 / (2 * π) * (r ^ 2 / 2 * π) := by gcongr
    _ = r ^ 2 / 4 := by field_simp; ring

lemma j0_abs_arg (a x : ℝ) :
    J0 (a * |x|) = (1 / (2 * π)) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos (a * x * Real.cos θ) := by
  unfold J0
  refine congrArg (fun I => 1 / (2 * π) * I) ?_
  apply intervalIntegral.integral_congr
  intro θ _
  rcases abs_choice x with h | h
  · simp only [h]
  · simp only [h]
    rw [show a * -x * Real.cos θ = -(a * x * Real.cos θ) by ring, Real.cos_neg]

lemma rot_identity (x θ : ℝ) :
    Real.sqrt (1 + x ^ 2) * Real.cos (θ + (Real.arctan x - π / 2)) =
      x * Real.cos θ + Real.sin θ := by
  have hR : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [show θ + (Real.arctan x - π / 2) = (θ + Real.arctan x) - π / 2 by ring,
    Real.cos_sub_pi_div_two, Real.sin_add, Real.sin_arctan, Real.cos_arctan]
  field_simp
  ring

lemma j0_sqrt_arg (a x : ℝ) :
    J0 (a * Real.sqrt (1 + x ^ 2)) = (1 / (2 * π)) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.cos (a * (x * Real.cos θ + Real.sin θ)) := by
  unfold J0
  refine congrArg (fun I => 1 / (2 * π) * I) ?_
  set f : ℝ → ℝ := fun θ => Real.cos (a * Real.sqrt (1 + x ^ 2) * Real.cos θ) with hf
  have hper : Function.Periodic f (2 * π) := by
    intro θ; simp only [hf, Real.cos_add_two_pi]
  set β := Real.arctan x - π / 2
  have h1 : ∫ θ in (0 : ℝ)..(2 * Real.pi), f (θ + β) = ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ := by
    rw [intervalIntegral.integral_comp_add_right, zero_add]
    have := hper.intervalIntegral_add_eq β 0
    rw [zero_add] at this
    rw [add_comm (2 * π) β, this]
  rw [← h1]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [hf]
  rw [mul_assoc, rot_identity]

lemma integral_sin_sin_eq_zero (a x : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Real.sin (a * x * Real.cos θ) * Real.sin (a * Real.sin θ)
      = 0 := by
  set g : ℝ → ℝ := fun θ => Real.sin (a * x * Real.cos θ) * Real.sin (a * Real.sin θ) with hg
  have h1 : ∫ θ in (0 : ℝ)..(2 * Real.pi), g (2 * π - θ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ := by
    rw [intervalIntegral.integral_comp_sub_left]
    simp
  have h2 : ∫ θ in (0 : ℝ)..(2 * Real.pi), g (2 * π - θ) =
      -∫ θ in (0 : ℝ)..(2 * Real.pi), g θ := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [hg, Real.cos_two_pi_sub, Real.sin_two_pi_sub, mul_neg, Real.sin_neg]
  change ∫ θ in (0 : ℝ)..(2 * Real.pi), g θ = 0
  linarith

lemma besselPlane (σ x : ℝ) : besselG σ x = (1 / (2 * Real.pi)) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi),
      (1 - Real.cos (Real.exp (-σ) * Real.sin θ)) * Real.cos (Real.exp (-σ) * x * Real.cos θ) := by
  unfold besselG
  rw [j0_abs_arg, j0_sqrt_arg, ← mul_sub]
  refine congrArg (fun I => 1 / (2 * π) * I) ?_
  generalize Real.exp (-σ) = a
  have hc : ∀ θ, Real.cos (a * (x * Real.cos θ + Real.sin θ)) =
      Real.cos (a * x * Real.cos θ) * Real.cos (a * Real.sin θ) -
        Real.sin (a * x * Real.cos θ) * Real.sin (a * Real.sin θ) := by
    intro θ
    rw [show a * (x * Real.cos θ + Real.sin θ) = a * x * Real.cos θ + a * Real.sin θ by ring,
      Real.cos_add]
  simp_rw [hc]
  have i1 : IntervalIntegrable (fun θ => Real.cos (a * x * Real.cos θ)) volume 0 (2 * π) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun θ => Real.cos (a * x * Real.cos θ) * Real.cos (a * Real.sin θ))
      volume 0 (2 * π) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun θ => Real.sin (a * x * Real.cos θ) * Real.sin (a * Real.sin θ))
      volume 0 (2 * π) :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub i2 i3, integral_sin_sin_eq_zero, sub_zero,
    ← intervalIntegral.integral_sub i1 i2]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only
  ring

lemma laplace_cos (lam w : ℝ) (hlam : 0 < lam) :
    IntegrableOn (fun a => Real.exp (-(lam * a)) * Real.cos (a * w)) (Set.Ioi 0) ∧
    ∫ a in Set.Ioi (0:ℝ), Real.exp (-(lam * a)) * Real.cos (a * w) = lam / (lam ^ 2 + w ^ 2) := by
  set z : ℂ := -lam + w * Complex.I with hzdef
  have hz : z.re < 0 := by simp [z]; linarith
  have hint := integrableOn_exp_mul_complex_Ioi hz 0
  have hval := integral_exp_mul_complex_Ioi hz 0
  have hpt : ∀ a : ℝ, (Complex.exp (z * a)).re = Real.exp (-(lam * a)) * Real.cos (a * w) := by
    intro a
    rw [Complex.exp_re]
    simp [z]
    ring_nf
  constructor
  · have := hint.re
    simpa [hpt] using this
  · have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    simp_rw [hpt] at h
    rw [h, hval]
    simp [z, Complex.div_re, Complex.normSq_apply]
    field_simp

/-- The globally smooth antiderivative `θ - arctan(...)` of `k / (cos² θ + k² sin² θ)`. -/
noncomputable def Gk (k θ : ℝ) : ℝ :=
  θ - Real.arctan ((1 - k) * Real.sin θ * Real.cos θ / (Real.cos θ ^ 2 + k * Real.sin θ ^ 2))

lemma alg_Gk (k s c : ℝ) (_hk : 0 < k) (hsc : s ^ 2 + c ^ 2 = 1) (hD : 0 < c ^ 2 + k * s ^ 2)
    (hE : 0 < c ^ 2 + k ^ 2 * s ^ 2) :
    1 - 1 / (1 + ((1 - k) * s * c / (c ^ 2 + k * s ^ 2)) ^ 2) *
      (((1 - k) * (c ^ 2 - s ^ 2) * (c ^ 2 + k * s ^ 2) -
        (1 - k) * s * c * (-(2 * (1 - k) * s * c))) / (c ^ 2 + k * s ^ 2) ^ 2) =
      k / (c ^ 2 + k ^ 2 * s ^ 2) := by
  have e1 : (1 - k) * (c ^ 2 - s ^ 2) * (c ^ 2 + k * s ^ 2) -
      (1 - k) * s * c * (-(2 * (1 - k) * s * c)) = (1 - k) * (c ^ 2 - k * s ^ 2) := by
    linear_combination (1 - k) * (c ^ 2 - k * s ^ 2) * hsc
  have e2 : 1 + ((1 - k) * s * c / (c ^ 2 + k * s ^ 2)) ^ 2 =
      (c ^ 2 + k ^ 2 * s ^ 2) / (c ^ 2 + k * s ^ 2) ^ 2 := by
    rw [div_pow, eq_div_iff (by positivity), add_mul, div_mul_cancel₀ _ (by positivity)]
    linear_combination (c ^ 2 + k ^ 2 * s ^ 2) * hsc
  rw [e1, e2]
  field_simp
  linear_combination k * hsc

lemma posE (k θ : ℝ) (hk0 : 0 < k) (hk1 : k ≤ 1) :
    0 < Real.cos θ ^ 2 + k ^ 2 * Real.sin θ ^ 2 := by
  have hsc := Real.sin_sq_add_cos_sq θ
  have hk2 : k ^ 2 ≤ 1 := by nlinarith
  have hk2' : 0 < k ^ 2 := by positivity
  have : k ^ 2 * Real.cos θ ^ 2 ≤ Real.cos θ ^ 2 := by
    nlinarith [sq_nonneg (Real.cos θ)]
  nlinarith

lemma hasDerivAt_Gk (k θ : ℝ) (hk0 : 0 < k) (hk1 : k ≤ 1) :
    HasDerivAt (Gk k) (k / (Real.cos θ ^ 2 + k ^ 2 * Real.sin θ ^ 2)) θ := by
  have hsc := Real.sin_sq_add_cos_sq θ
  have hD : 0 < Real.cos θ ^ 2 + k * Real.sin θ ^ 2 := by
    nlinarith [sq_nonneg (Real.cos θ), sq_nonneg (Real.sin θ)]
  have hE := posE k θ hk0 hk1
  have hN : HasDerivAt (fun θ => (1 - k) * Real.sin θ * Real.cos θ)
      ((1 - k) * (Real.cos θ ^ 2 - Real.sin θ ^ 2)) θ := by
    convert ((hasDerivAt_sin θ).const_mul (1 - k)).mul (hasDerivAt_cos θ) using 1
    ring
  have hDd : HasDerivAt (fun θ => Real.cos θ ^ 2 + k * Real.sin θ ^ 2)
      (-(2 * (1 - k) * Real.sin θ * Real.cos θ)) θ := by
    convert ((hasDerivAt_cos θ).pow 2).add (((hasDerivAt_sin θ).pow 2).const_mul k) using 1
    simp
    ring
  have h := (hasDerivAt_id θ).sub ((hN.fun_div hDd hD.ne').arctan)
  convert h using 1
  · ext x; simp only [Gk, Pi.sub_apply, id]
  · exact (alg_Gk k (Real.sin θ) (Real.cos θ) hk0 hsc hD hE).symm

lemma Gk_zero (k : ℝ) : Gk k 0 = 0 := by simp [Gk]

lemma Gk_two_pi (k : ℝ) : Gk k (2 * π) = 2 * π := by simp [Gk]

lemma angular_integral (lam c : ℝ) (hlam : 0 < lam) :
    ∫ θ in (0:ℝ)..(2 * π), lam / (lam ^ 2 + (c * Real.cos θ) ^ 2) =
      2 * π / Real.sqrt (lam ^ 2 + c ^ 2) := by
  set s := Real.sqrt (lam ^ 2 + c ^ 2) with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = lam ^ 2 + c ^ 2 := Real.sq_sqrt (by positivity)
  set k := lam / s with hk
  have hk0 : 0 < k := div_pos hlam hs0
  have hk1 : k ≤ 1 := by
    rw [hk, div_le_one hs0]
    rw [hs]
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg c]
  have hderiv : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * π),
      HasDerivAt (fun θ => Gk k θ / s) (lam / (lam ^ 2 + (c * Real.cos θ) ^ 2)) θ := by
    intro θ _
    have hsc := Real.sin_sq_add_cos_sq θ
    have hF : 0 < lam ^ 2 + (c * Real.cos θ) ^ 2 := by positivity
    have key : Real.cos θ ^ 2 + k ^ 2 * Real.sin θ ^ 2 =
        (lam ^ 2 + (c * Real.cos θ) ^ 2) / s ^ 2 := by
      rw [hk, div_pow, eq_div_iff (by positivity)]
      field_simp
      linear_combination (Real.cos θ ^ 2) * hs2 + lam ^ 2 * hsc
    convert (hasDerivAt_Gk k θ hk0 hk1).div_const s using 1
    rw [key, hk]
    field_simp
  have hint : IntervalIntegrable (fun θ => lam / (lam ^ 2 + (c * Real.cos θ) ^ 2)) volume 0
      (2 * π) := by
    have hc : Continuous fun θ : ℝ => lam ^ 2 + (c * Real.cos θ) ^ 2 := by fun_prop
    exact (continuous_const.div hc (fun θ => by positivity)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint, Gk_zero, Gk_two_pi]
  ring

lemma laplace_j0 (lam c : ℝ) (hlam : 0 < lam) :
    IntegrableOn (fun a => Real.exp (-(lam * a)) * J0 (a * c)) (Set.Ioi 0) ∧
    ∫ a in Set.Ioi (0 : ℝ), Real.exp (-(lam * a)) * J0 (a * c) =
      1 / Real.sqrt (lam ^ 2 + c ^ 2) := by
  have hexp : IntegrableOn (fun a => Real.exp (-(lam * a))) (Set.Ioi 0) := by
    have := exp_neg_integrableOn_Ioi 0 hlam
    simpa [neg_mul] using this
  constructor
  · refine Integrable.mono' hexp ?_ ?_
    · exact ((by fun_prop : Continuous fun a : ℝ => Real.exp (-(lam * a))).mul
        (j0_continuous.comp (by fun_prop : Continuous fun a : ℝ => a * c))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun a => ?_)
      rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (j0_abs_le_one _)
  · let F : ℝ → ℝ → ℝ := fun a θ => Real.exp (-(lam * a)) * Real.cos (a * (c * Real.cos θ))
    have hF : Integrable (Function.uncurry F)
        ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioc 0 (2 * π)))) := by
      have hg : Integrable (fun z : ℝ × ℝ => Real.exp (-(lam * z.1)) * (fun _ : ℝ => (1:ℝ)) z.2)
          ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioc 0 (2 * π)))) :=
        Integrable.mul_prod hexp continuous_const.integrableOn_Ioc
      refine Integrable.mono' hg ?_ ?_
      · exact (by fun_prop : Continuous (Function.uncurry F)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun z => ?_)
        simp only [Function.uncurry, F, mul_one]
        rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (Real.abs_cos_le_one _)
    have step1 : ∫ a in Set.Ioi (0:ℝ), Real.exp (-(lam * a)) * J0 (a * c) =
        1 / (2 * π) * ∫ a in Set.Ioi (0:ℝ), ∫ θ in Set.Ioc 0 (2 * π), F a θ := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi (fun a _ => ?_)
      simp only [J0, F]
      rw [intervalIntegral.integral_of_le (by positivity), ← integral_const_mul,
        ← integral_const_mul, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
      simp only
      ring_nf
    have step2 := integral_integral_swap hF
    have step3 : ∀ θ, ∫ a in Set.Ioi (0:ℝ), F a θ = lam / (lam ^ 2 + (c * Real.cos θ) ^ 2) := by
      intro θ
      exact (laplace_cos lam (c * Real.cos θ) hlam).2
    rw [step1, step2]
    simp_rw [step3]
    rw [← intervalIntegral.integral_of_le (by positivity), angular_integral lam c hlam]
    field_simp

lemma j0_quarter (r : ℝ) :
    J0 r = (2 / π) * ∫ θ in (0:ℝ)..(π / 2), Real.cos (r * Real.cos θ) := by
  let f : ℝ → ℝ := fun θ => Real.cos (r * Real.cos θ)
  have hcont : Continuous f := by fun_prop
  have hi : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hcont.intervalIntegrable a b
  have h1 : ∫ θ in (0:ℝ)..(2 * π), f θ = (∫ θ in (0:ℝ)..π, f θ) + ∫ θ in π..(2 * π), f θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hi 0 π) (hi π (2 * π))).symm
  have h2 : ∫ θ in π..(2 * π), f θ = ∫ θ in (0:ℝ)..π, f θ := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π) f (2 * π)
    rw [show 2 * π - π = π by ring, sub_zero] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [f, Real.cos_two_pi_sub]
  have h3 : ∫ θ in (0:ℝ)..π, f θ = (∫ θ in (0:ℝ)..(π / 2), f θ) + ∫ θ in (π / 2)..π, f θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hi 0 (π / 2)) (hi (π / 2) π)).symm
  have h4 : ∫ θ in (π / 2)..π, f θ = ∫ θ in (0:ℝ)..(π / 2), f θ := by
    have := intervalIntegral.integral_comp_sub_left (a := 0) (b := π / 2) f π
    rw [show π - π / 2 = π / 2 by ring, sub_zero] at this
    rw [← this]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [f, Real.cos_pi_sub, mul_neg, Real.cos_neg]
  unfold J0
  change 1 / (2 * π) * ∫ θ in (0:ℝ)..(2 * π), f θ = 2 / π * ∫ θ in (0:ℝ)..(π / 2), f θ
  rw [h1, h2, h3, h4]
  field_simp
  ring

lemma tail_bound (r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ) (hδ' : δ ≤ π / 2) :
    |∫ θ in δ..(π / 2), Real.cos (r * Real.cos θ)| ≤ 2 / (r * Real.sin δ) := by
  have hsinδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hsin_pos : ∀ θ ∈ Set.uIcc δ (π / 2), 0 < Real.sin θ := by
    intro θ hθ
    rw [Set.uIcc_of_le hδ'] at hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  let u : ℝ → ℝ := fun θ => -(r * Real.sin θ)⁻¹
  let u' : ℝ → ℝ := fun θ => Real.cos θ / (r * Real.sin θ ^ 2)
  let v : ℝ → ℝ := fun θ => Real.sin (r * Real.cos θ)
  let v' : ℝ → ℝ := fun θ => Real.cos (r * Real.cos θ) * (-(r * Real.sin θ))
  have hu_deriv : ∀ θ ∈ Set.uIcc δ (π / 2), HasDerivAt u (u' θ) θ := by
    intro θ hθ
    have hs := hsin_pos θ hθ
    have h := (((hasDerivAt_sin θ).const_mul r).fun_inv (by positivity)).neg
    convert h using 1
    simp only [u']
    field_simp
  have hv_deriv : ∀ θ, HasDerivAt v (v' θ) θ := by
    intro θ
    have h := ((hasDerivAt_cos θ).const_mul r).sin
    convert h using 1
    simp only [v']
    ring
  have hu'_int : IntervalIntegrable u' volume δ (π / 2) := by
    have hc1 : Continuous fun θ : ℝ => Real.cos θ := Real.continuous_cos
    have hc2 : Continuous fun θ : ℝ => r * Real.sin θ ^ 2 := by fun_prop
    have : ContinuousOn (fun θ : ℝ => Real.cos θ / (r * Real.sin θ ^ 2)) (Set.uIcc δ (π / 2)) :=
      hc1.continuousOn.div hc2.continuousOn (fun θ hθ => by
        have := hsin_pos θ hθ
        positivity)
    exact this.intervalIntegrable
  have hv'_int : IntervalIntegrable v' volume δ (π / 2) := by
    have : Continuous fun θ : ℝ => Real.cos (r * Real.cos θ) * (-(r * Real.sin θ)) := by
      fun_prop
    exact this.intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu_deriv
    (fun θ _ => hv_deriv θ) hu'_int hv'_int
  have heq : ∫ θ in δ..(π / 2), Real.cos (r * Real.cos θ) =
      ∫ θ in δ..(π / 2), u θ * v' θ := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    have hs := hsin_pos θ hθ
    simp only [u, v']
    field_simp
  rw [heq, hibp]
  have hend : u (π / 2) * v (π / 2) = 0 := by simp [u, v]
  have hstart : |u δ * v δ| ≤ 1 / (r * Real.sin δ) := by
    simp only [u, v]
    rw [abs_mul, abs_neg, abs_inv, abs_of_pos (by positivity : 0 < r * Real.sin δ), one_div]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_sin_le_one _)
  have hint_bound : |∫ θ in δ..(π / 2), u' θ * v θ| ≤ 1 / (r * Real.sin δ) := by
    have h1 : ‖∫ θ in δ..(π / 2), u' θ * v θ‖ ≤ ∫ θ in δ..(π / 2), u' θ := by
      apply intervalIntegral.norm_integral_le_of_norm_le hδ'
      · refine Filter.Eventually.of_forall (fun θ hθ => ?_)
        have hθ' : θ ∈ Set.uIcc δ (π / 2) := by
          rw [Set.uIcc_of_le hδ']; exact Set.Ioc_subset_Icc_self hθ
        have hs := hsin_pos θ hθ'
        have hc : 0 ≤ Real.cos θ :=
          Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
        have hu'0 : 0 ≤ u' θ := by simp only [u']; positivity
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu'0]
        exact mul_le_of_le_one_right hu'0 (Real.abs_sin_le_one _)
      · exact hu'_int
    have h2 : ∫ θ in δ..(π / 2), u' θ = u (π / 2) - u δ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hu_deriv hu'_int
    rw [h2, Real.norm_eq_abs] at h1
    have h3 : u (π / 2) - u δ ≤ 1 / (r * Real.sin δ) := by
      simp only [u, Real.sin_pi_div_two, mul_one]
      have : 0 < r⁻¹ := inv_pos.mpr hr
      rw [one_div]
      linarith
    linarith
  rw [hend, zero_sub]
  obtain ⟨a1, a1'⟩ := abs_le.mp hstart
  obtain ⟨a2, a2'⟩ := abs_le.mp hint_bound
  have h2 : 2 / (r * Real.sin δ) = 1 / (r * Real.sin δ) + 1 / (r * Real.sin δ) := by ring
  rw [abs_le, h2]
  constructor <;> linarith

lemma head_bound (r δ : ℝ) (hδ : 0 ≤ δ) :
    |∫ θ in (0:ℝ)..δ, Real.cos (r * Real.cos θ)| ≤ δ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ)
    (C := 1) (f := fun θ => Real.cos (r * Real.cos θ)) (fun θ _ => by
      simpa using Real.abs_cos_le_one _)
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hδ, one_mul] at h
  exact h

lemma quarter_bound (t : ℝ) (ht : 1 ≤ t) :
    |∫ θ in (0:ℝ)..(π / 2), Real.cos (t ^ 2 * Real.cos θ)| ≤ (1 + π) / t := by
  have ht0 : 0 < t := by linarith
  have hr0 : 0 < t ^ 2 := by positivity
  set δ := 1 / t with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one ht0]; exact ht
  have hδπ : δ ≤ π / 2 := by linarith [Real.pi_gt_three]
  have hcont : Continuous fun θ => Real.cos (t ^ 2 * Real.cos θ) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 δ)
    (hcont.intervalIntegrable δ (π / 2))]
  have hhead := head_bound (t ^ 2) δ hδ0.le
  have htail := tail_bound (t ^ 2) δ hr0 hδ0 hδπ
  have hjordan : 2 / π * δ ≤ Real.sin δ := Real.mul_le_sin hδ0.le hδπ
  have htail' : 2 / (t ^ 2 * Real.sin δ) ≤ π / t := by
    have hpos : 0 < 2 / π * δ := by positivity
    calc 2 / (t ^ 2 * Real.sin δ) ≤ 2 / (t ^ 2 * (2 / π * δ)) := by gcongr
      _ = π / t := by
        rw [hδdef]
        field_simp
  calc |(∫ θ in (0:ℝ)..δ, Real.cos (t ^ 2 * Real.cos θ)) +
        ∫ θ in δ..(π / 2), Real.cos (t ^ 2 * Real.cos θ)|
      ≤ |∫ θ in (0:ℝ)..δ, Real.cos (t ^ 2 * Real.cos θ)| +
        |∫ θ in δ..(π / 2), Real.cos (t ^ 2 * Real.cos θ)| := abs_add_le _ _
    _ ≤ δ + π / t := by linarith
    _ = (1 + π) / t := by rw [hδdef]; ring

lemma j0_decay : ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → |J0 r| ≤ C / Real.sqrt r := by
  refine ⟨3, by norm_num, fun r hr => ?_⟩
  have hsq : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  rcases le_or_gt 1 r with h1 | h1
  · have ht : 1 ≤ Real.sqrt r := Real.one_le_sqrt.mpr h1
    have hr_eq : r = Real.sqrt r ^ 2 := (Real.sq_sqrt hr.le).symm
    rw [j0_quarter, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / π)]
    have hq := quarter_bound (Real.sqrt r) ht
    rw [← hr_eq] at hq
    have hpi := Real.pi_gt_three
    calc 2 / π * |∫ θ in (0:ℝ)..(π / 2), Real.cos (r * Real.cos θ)|
        ≤ 2 / π * ((1 + π) / Real.sqrt r) := by gcongr
      _ = (2 / π + 2) / Real.sqrt r := by field_simp
      _ ≤ 3 / Real.sqrt r := by
          gcongr
          have : 2 / π ≤ 1 := by rw [div_le_one (by positivity)]; linarith
          linarith
  · have hsq1 : Real.sqrt r ≤ 1 := Real.sqrt_le_one.mpr h1.le
    calc |J0 r| ≤ 1 := j0_abs_le_one r
      _ ≤ 3 / Real.sqrt r := by rw [le_div_iff₀ hsq]; linarith

end ChowlaOpus.J0Aux

namespace ChowlaOpus

open J0Aux in
theorem j0Statement_holds : J0Statement :=
  ⟨j0_continuous, j0_abs_le_one, j0_neg, j0_zero, j0_sub_one, j0_decay,
    fun lam c hlam _ => laplace_j0 lam c hlam⟩

theorem besselPlaneStatement_holds : BesselPlaneStatement := J0Aux.besselPlane

end ChowlaOpus
