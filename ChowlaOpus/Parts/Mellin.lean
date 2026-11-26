module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.MellinAux

/-- `g(a) = J₀(a|x|) − J₀(a√(1+x²))`, so that `g(e^{-σ}) = G_σ(x)`. -/
noncomputable def gF (x : ℝ) (a : ℝ) : ℂ :=
  ((J0 (a * |x|) - J0 (a * Real.sqrt (1 + x ^ 2)) : ℝ) : ℂ)

/-- Laplace transform of `g`: `(λ² + A)^{-1/2} − (λ² + B)^{-1/2}`. -/
noncomputable def LF (A B : ℝ) (l : ℝ) : ℂ :=
  ((1 / Real.sqrt (l ^ 2 + A) - 1 / Real.sqrt (l ^ 2 + B) : ℝ) : ℂ)

/-- `e^{-At} − e^{-Bt}`. -/
noncomputable def hF (A B : ℝ) (t : ℝ) : ℂ :=
  ((Real.exp (-(A * t)) - Real.exp (-(B * t)) : ℝ) : ℂ)

/-- Indicator of `[A, B]`. -/
noncomputable def IF (A B : ℝ) : ℝ → ℂ := Set.indicator (Set.Icc A B) (fun _ => 1)

lemma norm_cpow_of_re_zero {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z.re = 0) :
    ‖(t : ℂ) ^ z‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, hz, Real.rpow_zero]

lemma one_div_cpow_eq {y : ℝ} (hy : 0 < y) (a : ℂ) : (1 / (y : ℂ)) ^ a = (y : ℂ) ^ (-a) := by
  rw [one_div, Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hy.le]; exact Real.pi_pos.ne),
    Complex.cpow_neg]

lemma lhs_eq_mellin (ξ x : ℝ) :
    ∫ σ, (besselG σ x : ℂ) * ee (-(ξ * σ)) =
      mellin (gF x) (Complex.I * ((2 * π * ξ : ℝ) : ℂ)) := by
  rw [mellin_eq_fourier, fourier_eq_ee]
  have h1 : (Complex.I * ((2 * π * ξ : ℝ) : ℂ)).re = 0 := by simp
  have h2 : (Complex.I * ((2 * π * ξ : ℝ) : ℂ)).im / (2 * π) = ξ := by
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
    field_simp
  rw [h1, h2]
  congr 1; ext σ
  simp [gF, besselG, mul_comm]

lemma betaF_eq_mellin (ξ x : ℝ) :
    betaF ξ x = (1 / 2 : ℂ) *
      mellin (IF (x ^ 2) (1 + x ^ 2)) (-(Complex.I * ((2 * π * ξ : ℝ) : ℂ)) / 2) := by
  have hc := mellin_comp_rpow (IF (x ^ 2) (1 + x ^ 2)) (Complex.I * ((2 * π * ξ : ℝ) : ℂ)) (-2)
  rw [show (Complex.I * ((2 * π * ξ : ℝ) : ℂ)) / ((-2 : ℝ) : ℂ) =
    -(Complex.I * ((2 * π * ξ : ℝ) : ℂ)) / 2 by push_cast; ring] at hc
  have h12 : |(-2 : ℝ)|⁻¹ = (1 / 2 : ℝ) := by norm_num
  rw [h12, Complex.real_smul, show (((1 / 2 : ℝ)) : ℂ) = (1 / 2 : ℂ) by push_cast; ring] at hc
  rw [← hc, mellin_eq_fourier, fourier_eq_ee]
  have h1 : (Complex.I * ((2 * π * ξ : ℝ) : ℂ)).re = 0 := by simp
  have h2 : (Complex.I * ((2 * π * ξ : ℝ) : ℂ)).im / (2 * π) = ξ := by
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add]
    field_simp
  rw [h1, h2]
  unfold betaF
  congr 1; ext σ
  have he : Real.exp (-σ) ^ (-2 : ℝ) = Real.exp σ ^ 2 := by
    rw [← Real.exp_mul, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have key : (|x| ≤ Real.exp σ) ↔ x ^ 2 ≤ Real.exp σ ^ 2 := by
    rw [← sq_abs]; exact (sq_le_sq₀ (abs_nonneg x) (Real.exp_pos σ).le).symm
  simp only [neg_zero, zero_mul, Real.exp_zero, one_smul, he, IF, annB, Set.indicator_apply,
    Set.mem_Icc, key]
  split_ifs <;> simp [mul_comm]

lemma gF_continuous (hJ : J0Statement) (x : ℝ) : Continuous (gF x) := by
  have hc := hJ.1
  unfold gF
  fun_prop

lemma gF_bound_small (hJ : J0Statement) (x a : ℝ) :
    ‖gF x a‖ ≤ (1 + 2 * x ^ 2) / 4 * a ^ 2 := by
  obtain ⟨-, -, -, -, hquad, -⟩ := hJ
  have h1 := hquad (a * |x|)
  have h2 := hquad (a * Real.sqrt (1 + x ^ 2))
  rw [gF, Complex.norm_real, Real.norm_eq_abs]
  have e1 : (a * |x|) ^ 2 = a ^ 2 * x ^ 2 := by rw [mul_pow, sq_abs]
  have e2 : (a * Real.sqrt (1 + x ^ 2)) ^ 2 = a ^ 2 * (1 + x ^ 2) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [e1] at h1
  rw [e2] at h2
  calc |J0 (a * |x|) - J0 (a * Real.sqrt (1 + x ^ 2))|
      = |(J0 (a * |x|) - 1) - (J0 (a * Real.sqrt (1 + x ^ 2)) - 1)| := by ring_nf
    _ ≤ |J0 (a * |x|) - 1| + |J0 (a * Real.sqrt (1 + x ^ 2)) - 1| := abs_sub _ _
    _ ≤ a ^ 2 * x ^ 2 / 4 + a ^ 2 * (1 + x ^ 2) / 4 := add_le_add h1 h2
    _ = (1 + 2 * x ^ 2) / 4 * a ^ 2 := by ring

lemma gF_bound_large (hJ : J0Statement) {x : ℝ} (hx : x ≠ 0) :
    ∃ K, 0 < K ∧ ∀ a, 0 < a → ‖gF x a‖ ≤ K * a ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨-, -, -, -, -, ⟨C, hC, hdecay⟩, -⟩ := hJ
  have hu : 0 < |x| := abs_pos.mpr hx
  refine ⟨2 * C / Real.sqrt |x|, by positivity, fun a ha => ?_⟩
  have hv : |x| ≤ Real.sqrt (1 + x ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by linarith)
  have h1 := hdecay (a * |x|) (by positivity)
  have h2 := hdecay (a * Real.sqrt (1 + x ^ 2)) (by positivity)
  have h3 : C / Real.sqrt (a * Real.sqrt (1 + x ^ 2)) ≤ C / Real.sqrt (a * |x|) := by
    apply div_le_div_of_nonneg_left hC.le (by positivity)
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hv ha.le)
  have h4 : C / Real.sqrt (a * |x|) = C / Real.sqrt |x| * a ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_mul ha.le, Real.rpow_neg ha.le, ← Real.sqrt_eq_rpow]
    have : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
    have : Real.sqrt |x| ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
    field_simp
  rw [gF, Complex.norm_real, Real.norm_eq_abs]
  calc |J0 (a * |x|) - J0 (a * Real.sqrt (1 + x ^ 2))|
      ≤ |J0 (a * |x|)| + |J0 (a * Real.sqrt (1 + x ^ 2))| := abs_sub _ _
    _ ≤ C / Real.sqrt (a * |x|) + C / Real.sqrt (a * |x|) := add_le_add h1 (h2.trans h3)
    _ = 2 * C / Real.sqrt |x| * a ^ (-(1 / 2 : ℝ)) := by rw [h4]; ring

lemma integrableOn_gF_div (hJ : J0Statement) {x : ℝ} (hx : x ≠ 0) :
    IntegrableOn (fun a => ‖gF x a‖ / a) (Set.Ioi 0) := by
  obtain ⟨K, hK, hbd⟩ := gF_bound_large hJ hx
  have hmeas : Measurable (fun a => ‖gF x a‖ / a) :=
    ((gF_continuous hJ x).measurable.norm).div measurable_id
  rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one, integrableOn_union]
  constructor
  · refine Integrable.mono' (integrable_const ((1 + 2 * x ^ 2) / 4)) hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun a ha => ?_)
    obtain ⟨ha0, ha1⟩ := ha
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ ha0]
    calc ‖gF x a‖ ≤ (1 + 2 * x ^ 2) / 4 * a ^ 2 := gF_bound_small hJ x a
      _ ≤ (1 + 2 * x ^ 2) / 4 * a := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); nlinarith
  · refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt
      (by norm_num : (-(3 / 2) : ℝ) < -1) zero_lt_one).const_mul K) hmeas.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall (fun a ha => ?_)
    have ha0 : 0 < a := lt_trans zero_lt_one ha
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ ha0]
    calc ‖gF x a‖ ≤ K * a ^ (-(1 / 2 : ℝ)) := hbd a ha0
      _ = K * a ^ (-(3 / 2) : ℝ) * a := by
        rw [mul_assoc, ← Real.rpow_add_one ha0.ne']; norm_num

lemma integrable_besselG (hJ : J0Statement) {x : ℝ} (hx : x ≠ 0) :
    Integrable (fun σ => besselG σ x) := by
  obtain ⟨K, hK, hbd⟩ := gF_bound_large hJ hx
  have hnorm : ∀ σ, ‖besselG σ x‖ = ‖gF x (Real.exp (-σ))‖ := fun σ => by
    simp only [gF, besselG, Complex.norm_real]
  have hcont : Continuous (fun σ => besselG σ x) := by
    have hc := hJ.1
    unfold besselG
    fun_prop
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0:ℝ)), integrableOn_union]
  constructor
  · refine Integrable.mono' ((integrableOn_exp_mul_Iic (by norm_num : (0:ℝ) < 1 / 2) 0).const_mul K)
      hcont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun σ => ?_)
    rw [hnorm]
    calc ‖gF x (Real.exp (-σ))‖ ≤ K * Real.exp (-σ) ^ (-(1 / 2 : ℝ)) := hbd _ (Real.exp_pos _)
      _ = K * Real.exp (1 / 2 * σ) := by rw [← Real.exp_mul]; congr 2; ring
  · refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 (by norm_num : (0:ℝ) < 2)).const_mul
      ((1 + 2 * x ^ 2) / 4)) hcont.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun σ => ?_)
    rw [hnorm]
    calc ‖gF x (Real.exp (-σ))‖ ≤ (1 + 2 * x ^ 2) / 4 * Real.exp (-σ) ^ 2 := gF_bound_small hJ x _
      _ = (1 + 2 * x ^ 2) / 4 * Real.exp (-2 * σ) := by
        rw [← Real.exp_nat_mul]; congr 2; push_cast; ring

lemma step1 (hJ : J0Statement) {x : ℝ} (hx : x ≠ 0) {s : ℂ} (hs : s.re = 0) :
    Complex.Gamma (1 - s) * mellin (gF x) s = mellin (LF (x ^ 2) (1 + x ^ 2)) (1 - s) := by
  have hlap := hJ.2.2.2.2.2.2
  set f : ℝ → ℝ → ℂ := fun a l =>
    gF x a * ((l : ℂ) ^ ((1 - s) - 1) * Complex.exp (-((a : ℂ) * l))) with hf
  have hmeas : Measurable (Function.uncurry f) := by
    have := (gF_continuous hJ x).measurable
    simp only [hf]
    fun_prop
  have hnorm : ∀ a l, 0 < l → ‖f a l‖ = ‖gF x a‖ * Real.exp (-a * l) := by
    intro a l hl
    have hn : ‖(l : ℂ) ^ ((1 - s) - 1)‖ = 1 := norm_cpow_of_re_zero hl (by simp [hs])
    simp only [hf, norm_mul, hn, one_mul, Complex.norm_exp]
    congr 2
    simp
  have hexp_int : ∀ a, 0 < a → ∫ l in Set.Ioi (0:ℝ), Real.exp (-a * l) = 1 / a := by
    intro a ha
    have := integral_exp_mul_Ioi (a := -a) (by linarith) 0
    rw [this]
    simp
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    constructor
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun a ha => ?_)
      have ha' : 0 < a := ha
      refine ((exp_neg_integrableOn_Ioi 0 ha').const_mul ‖gF x a‖).mono'
        (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Filter.Eventually.of_forall (fun l hl => (hnorm a l hl).le)
    · have heq : ∀ a ∈ Set.Ioi (0:ℝ), ∫ l in Set.Ioi (0:ℝ), ‖f a l‖ = ‖gF x a‖ / a := by
        intro a ha
        rw [setIntegral_congr_fun measurableSet_Ioi (fun l (hl : l ∈ Set.Ioi (0:ℝ)) => hnorm a l hl),
          integral_const_mul,
          hexp_int a ha]
        ring
      exact (integrableOn_gF_div hJ hx).congr ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall (fun a ha => (heq a ha).symm)))
  have hswap := integral_integral_swap hint
  have hL : ∫ a in Set.Ioi (0:ℝ), ∫ l in Set.Ioi (0:ℝ), f a l =
      Complex.Gamma (1 - s) * mellin (gF x) s := by
    unfold mellin
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun a ha => ?_)
    have ha' : 0 < a := ha
    simp only [hf]
    rw [integral_const_mul, Complex.integral_cpow_mul_exp_neg_mul_Ioi (by simp [hs]) ha',
      one_div_cpow_eq ha', smul_eq_mul, show -(1 - s) = s - 1 by ring]
    ring
  have hR : ∫ l in Set.Ioi (0:ℝ), ∫ a in Set.Ioi (0:ℝ), f a l =
      mellin (LF (x ^ 2) (1 + x ^ 2)) (1 - s) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun l hl => ?_)
    have hl' : 0 < l := hl
    have e : ∀ a, f a l = (l : ℂ) ^ ((1 - s) - 1) *
        ((Real.exp (-(l * a)) * J0 (a * |x|) -
          Real.exp (-(l * a)) * J0 (a * Real.sqrt (1 + x ^ 2)) : ℝ) : ℂ) := by
      intro a
      simp only [hf, gF]
      push_cast
      ring_nf
    simp_rw [e]
    obtain ⟨hi1, he1⟩ := hlap l |x| hl' (abs_nonneg x)
    obtain ⟨hi2, he2⟩ := hlap l (Real.sqrt (1 + x ^ 2)) hl' (Real.sqrt_nonneg _)
    rw [integral_const_mul, integral_complex_ofReal, integral_sub hi1 hi2, he1, he2, smul_eq_mul]
    simp only [LF, sq_abs, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1 + x ^ 2)]
  rw [← hL, hswap, hR]

lemma mellin_gauss {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : 0 < z.re) :
    ∫ l in Set.Ioi (0:ℝ), (l : ℂ) ^ (z - 1) * ((Real.exp (-t * l ^ 2) : ℝ) : ℂ) =
      1 / 2 * ((t : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2)) := by
  have h1 := mellin_comp_rpow (fun y => ((Real.exp (-(t * y)) : ℝ) : ℂ)) z 2
  have h2 := mellin_comp_mul_left (fun y => ((Real.exp (-y) : ℝ) : ℂ)) (z / 2) ht
  have h3 : mellin (fun y => ((Real.exp (-y) : ℝ) : ℂ)) (z / 2) = Complex.Gamma (z / 2) := by
    rw [← Complex.GammaIntegral_eq_mellin, Complex.Gamma_eq_integral (by simp; linarith)]
  rw [show z / ((2:ℝ):ℂ) = z / 2 by norm_num, h2, h3] at h1
  unfold mellin at h1
  simp_rw [smul_eq_mul, Real.rpow_two] at h1
  rw [show |(2:ℝ)|⁻¹ = 1 / 2 by norm_num, Complex.real_smul] at h1
  simp_rw [neg_mul]
  rw [h1]
  push_cast; ring

lemma sub_exp_div_le {A B t : ℝ} (hAB : A ≤ B) (ht : 0 < t) :
    0 ≤ (Real.exp (-(A * t)) - Real.exp (-(B * t))) / t ∧
      (Real.exp (-(A * t)) - Real.exp (-(B * t))) / t ≤ (B - A) * Real.exp (-(A * t)) := by
  have hle : Real.exp (-(B * t)) ≤ Real.exp (-(A * t)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  refine ⟨div_nonneg (by linarith) ht.le, ?_⟩
  rw [div_le_iff₀ ht]
  have h1 := Real.add_one_le_exp (-((B - A) * t))
  have h2 : Real.exp (-(B * t)) = Real.exp (-(A * t)) * Real.exp (-((B - A) * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2]
  have h3 := Real.exp_pos (-(A * t))
  nlinarith

lemma integral_rpow_exp_half {r : ℝ} (hr : 0 < r) :
    ∫ t in Set.Ioi (0:ℝ), t ^ (-(1 / 2 : ℝ)) * Real.exp (-(r * t)) = Real.sqrt π / Real.sqrt r := by
  have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (r := r) (by norm_num) hr
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.Gamma_one_half_eq] at this
  rw [this, Real.sqrt_eq_rpow r, Real.div_rpow zero_le_one hr.le, Real.one_rpow]
  ring

lemma integrableOn_rpow_exp_half {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (-(1 / 2 : ℝ)) * Real.exp (-(r * t))) (Set.Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 2)) (p := 1) (b := r)
    (by norm_num) one_pos hr
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, neg_mul]

lemma step2 {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) {s : ℂ} (hs : s.re = 0) :
    mellin (LF A B) (1 - s) * (Real.sqrt π : ℂ) =
      Complex.Gamma ((1 - s) / 2) / 2 * mellin (hF A B) (s / 2) := by
  set k : ℝ → ℝ → ℝ := fun l t => t ^ (-(1 / 2 : ℝ)) * Real.exp (-t * l ^ 2) *
    (Real.exp (-(A * t)) - Real.exp (-(B * t))) with hk
  set f : ℝ → ℝ → ℂ := fun l t => (l : ℂ) ^ (-s) * (k l t : ℂ) with hf
  have hk_nonneg : ∀ l t, 0 < t → 0 ≤ k l t := by
    intro l t ht
    have hle : Real.exp (-(B * t)) ≤ Real.exp (-(A * t)) := by
      apply Real.exp_le_exp.mpr; nlinarith
    simp only [hk]
    have := Real.rpow_pos_of_pos ht (-(1 / 2 : ℝ))
    have := Real.exp_pos (-t * l ^ 2)
    apply mul_nonneg (by positivity) (by linarith)
  have hnorm : ∀ l t, 0 < l → 0 < t → ‖f l t‖ = k l t := by
    intro l t hl ht
    simp only [hf, norm_mul, norm_cpow_of_re_zero hl (z := -s) (by simp [hs]), one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hk_nonneg l t ht)]
  have hmeas : Measurable (Function.uncurry f) := by
    simp only [hf, hk]
    fun_prop
  have hkint : ∀ t, 0 < t → ∫ l in Set.Ioi (0:ℝ), k l t =
      Real.sqrt π / 2 * ((Real.exp (-(A * t)) - Real.exp (-(B * t))) / t) := by
    intro t ht
    have e : ∀ l, k l t = (t ^ (-(1 / 2 : ℝ)) * (Real.exp (-(A * t)) - Real.exp (-(B * t)))) *
        Real.exp (-t * l ^ 2) := fun l => by simp only [hk]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_gaussian_Ioi, Real.sqrt_div' _ ht.le,
      Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
    have hst : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
    field_simp
    rw [Real.sq_sqrt ht.le]
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
    constructor
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have ht' : 0 < t := ht
      have hbd : Integrable (fun l => k l t) (volume.restrict (Set.Ioi 0)) := by
        have := ((integrable_exp_neg_mul_sq ht').integrableOn (s := Set.Ioi 0)).const_mul
          (t ^ (-(1 / 2 : ℝ)) * (Real.exp (-(A * t)) - Real.exp (-(B * t))))
        refine this.congr (Filter.Eventually.of_forall (fun l => ?_))
        simp only [hk]; ring
      refine hbd.mono' (hmeas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun l hl => ?_)
      exact (hnorm l t hl ht').le
    · have heq : ∀ t ∈ Set.Ioi (0:ℝ), ∫ l in Set.Ioi (0:ℝ), ‖f l t‖ =
          Real.sqrt π / 2 * ((Real.exp (-(A * t)) - Real.exp (-(B * t))) / t) := by
        intro t ht
        rw [← hkint t ht]
        exact setIntegral_congr_fun measurableSet_Ioi (fun l hl => hnorm l t hl ht)
      refine Integrable.congr ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Filter.Eventually.of_forall (fun t ht => (heq t ht).symm)))
      refine Integrable.mono' ((exp_neg_integrableOn_Ioi 0 hA).const_mul
        (Real.sqrt π / 2 * (B - A))) (Measurable.aestronglyMeasurable (by fun_prop)) ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      obtain ⟨h0, h1⟩ := sub_exp_div_le hAB (show 0 < t from ht)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hpi : 0 ≤ Real.sqrt π / 2 := by positivity
      calc Real.sqrt π / 2 * ((Real.exp (-(A * t)) - Real.exp (-(B * t))) / t)
          ≤ Real.sqrt π / 2 * ((B - A) * Real.exp (-(A * t))) :=
            mul_le_mul_of_nonneg_left h1 hpi
        _ = Real.sqrt π / 2 * (B - A) * Real.exp (-A * t) := by rw [neg_mul]; ring
  have hswap := integral_integral_swap hint
  have hL : ∫ l in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ), f l t =
      mellin (LF A B) (1 - s) * (Real.sqrt π : ℂ) := by
    unfold mellin
    rw [← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ioi (fun l hl => ?_)
    have hl' : 0 < l := hl
    simp only [hf]
    rw [integral_const_mul, integral_complex_ofReal]
    have e : ∀ t, k l t = t ^ (-(1 / 2 : ℝ)) * Real.exp (-((l ^ 2 + A) * t)) -
        t ^ (-(1 / 2 : ℝ)) * Real.exp (-((l ^ 2 + B) * t)) := by
      intro t
      simp only [hk]
      rw [mul_assoc, mul_sub, ← Real.exp_add, ← Real.exp_add]
      ring_nf
    simp_rw [e]
    have hA' : 0 < l ^ 2 + A := by nlinarith [sq_nonneg l]
    have hB' : 0 < l ^ 2 + B := by nlinarith [sq_nonneg l]
    rw [integral_sub (integrableOn_rpow_exp_half hA') (integrableOn_rpow_exp_half hB'),
      integral_rpow_exp_half hA', integral_rpow_exp_half hB']
    simp only [LF, smul_eq_mul, show (1 : ℂ) - s - 1 = -s by ring]
    push_cast
    ring
  have hR : ∫ t in Set.Ioi (0:ℝ), ∫ l in Set.Ioi (0:ℝ), f l t =
      Complex.Gamma ((1 - s) / 2) / 2 * mellin (hF A B) (s / 2) := by
    unfold mellin
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : 0 < t := ht
    have e : ∀ l, f l t = ((l : ℂ) ^ ((1 - s) - 1) * ((Real.exp (-t * l ^ 2) : ℝ) : ℂ)) *
        ((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * hF A B t := by
      intro l
      simp only [hf, hk, hF, show (1 : ℂ) - s - 1 = -s by ring]
      push_cast; ring
    simp_rw [e]
    rw [integral_mul_const, integral_mul_const, mellin_gauss ht' (by simp [hs])]
    rw [Complex.ofReal_cpow ht'.le, smul_eq_mul]
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht'.ne'
    have hc : (t : ℂ) ^ (s / 2 - 1) = (t : ℂ) ^ (-((1 - s) / 2)) * (t : ℂ) ^ ((-(1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [← Complex.cpow_add _ _ htc]; congr 1; push_cast; ring
    rw [hc]
    ring
  rw [← hL, hswap, hR]

lemma integral_Icc_cexp {A B t : ℝ} (hAB : A ≤ B) (ht : 0 < t) :
    ∫ y in Set.Icc A B, Complex.exp (-((y : ℂ) * t)) =
      (Complex.exp (-(A * t)) - Complex.exp (-(B * t))) / t := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hAB]
  have hc : (-(t : ℂ)) ≠ 0 := by simp [ht.ne']
  have := integral_exp_mul_complex (a := A) (b := B) hc
  simp_rw [show ∀ y : ℝ, -((y : ℂ) * t) = -(t : ℂ) * y from fun y => by ring]
  rw [this]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  field_simp
  ring_nf

lemma mellin_IF {A B : ℝ} (hA : 0 < A) (z : ℂ) :
    mellin (IF A B) z = ∫ y in Set.Icc A B, (y : ℂ) ^ (z - 1) := by
  unfold mellin
  rw [show (fun y : ℝ => (y : ℂ) ^ (z - 1) • IF A B y) =
      Set.indicator (Set.Icc A B) (fun y => (y : ℂ) ^ (z - 1)) from ?_]
  · rw [setIntegral_indicator measurableSet_Icc,
      Set.inter_eq_right.mpr (fun y (hy : y ∈ Set.Icc A B) =>
        (lt_of_lt_of_le hA hy.1 : y ∈ Set.Ioi 0))]
  · ext y
    simp only [IF, Set.indicator_apply, smul_eq_mul]
    split_ifs <;> simp

lemma step3 {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) {s : ℂ} (hs : s.re = 0) :
    mellin (hF A B) (s / 2) = Complex.Gamma (1 + s / 2) * mellin (IF A B) (-s / 2) := by
  set f : ℝ → ℝ → ℂ := fun t y => (t : ℂ) ^ (s / 2) * Complex.exp (-((y : ℂ) * t)) with hf
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Icc A B))) := by
    have hbound : Integrable (fun p : ℝ × ℝ => Real.exp (-A * p.1) * (1 : ℝ))
        ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Icc A B))) := by
      exact Integrable.mul_prod (f := fun t => Real.exp (-A * t)) (g := fun _ => (1:ℝ))
        (exp_neg_integrableOn_Ioi 0 hA) (integrable_const _)
    refine hbound.mono' ?_ ?_
    · apply Measurable.aestronglyMeasurable
      simp only [hf]
      fun_prop
    · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Icc)]
      refine Filter.Eventually.of_forall (fun p hp => ?_)
      obtain ⟨hp1, hp2⟩ := hp
      simp only [Set.mem_Ioi] at hp1
      simp only [Set.mem_Icc] at hp2
      have hn : ‖(p.1 : ℂ) ^ (s / 2)‖ = 1 := norm_cpow_of_re_zero hp1 (by simp [hs])
      simp only [Function.uncurry, hf, norm_mul, hn, Complex.norm_exp, mul_one, one_mul]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        sub_zero]
      apply Real.exp_le_exp.mpr; nlinarith
  have hswap := integral_integral_swap hint
  have hL : ∫ t in Set.Ioi (0:ℝ), ∫ y in Set.Icc A B, f t y = mellin (hF A B) (s / 2) := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [hf]
    rw [integral_const_mul, integral_Icc_cexp hAB ht]
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (Set.mem_Ioi.mp ht))
    rw [smul_eq_mul, Complex.cpow_sub _ _ ht', Complex.cpow_one]
    simp only [hF]; push_cast
    field_simp
  have hR : ∫ y in Set.Icc A B, ∫ t in Set.Ioi (0:ℝ), f t y =
      Complex.Gamma (1 + s / 2) * mellin (IF A B) (-s / 2) := by
    have h1 : ∀ y ∈ Set.Icc A B, ∫ t in Set.Ioi (0:ℝ), f t y =
        Complex.Gamma (1 + s / 2) * (y : ℂ) ^ (-s / 2 - 1) := by
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le hA hy.1
      have := Complex.integral_cpow_mul_exp_neg_mul_Ioi (a := 1 + s / 2) (r := y)
        (by simp [hs]) hy0
      rw [show (1 + s / 2 - 1) = s / 2 by ring] at this
      simp only [hf]
      rw [this, one_div_cpow_eq hy0, mul_comm]
      congr 2; ring
    rw [setIntegral_congr_fun measurableSet_Icc h1, integral_const_mul, mellin_IF hA]
  rw [← hL, hswap, hR]

lemma gamma_identity {s : ℂ} (hs : s.re = 0) :
    Complex.Gamma ((1 - s) / 2) * Complex.Gamma (1 + s / 2) =
      (Real.sqrt π : ℂ) * Complex.Gamma (1 - s) *
        ((2 : ℂ) ^ s * Complex.Gamma (1 + s / 2) / Complex.Gamma (1 - s / 2)) := by
  have h := Complex.Gamma_mul_Gamma_add_half ((1 - s) / 2)
  rw [show (1 - s) / 2 + 1 / 2 = 1 - s / 2 by ring, show 2 * ((1 - s) / 2) = 1 - s by ring,
    show (1 : ℂ) - (1 - s) = s by ring] at h
  have hne : Complex.Gamma (1 - s / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hs])
  rw [mul_div_assoc', eq_div_iff hne]
  linear_combination Complex.Gamma (1 + s / 2) * h

end ChowlaOpus.MellinAux

namespace ChowlaOpus

theorem multStatement_holds : MultStatement := by
  have hconj : ∀ τ : ℝ, starRingEnd ℂ (1 + Complex.I * τ / 2) = 1 - Complex.I * (τ : ℂ) / 2 := by
    intro τ
    simp only [map_add, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_one, map_ofNat]
    ring
  have hre : ∀ τ : ℝ, 0 < (1 - Complex.I * (τ : ℂ) / 2).re := by
    intro τ; simp
  have h2 : ∀ τ : ℝ, ‖(2 : ℂ) ^ (Complex.I * τ)‖ = 1 := by
    intro τ
    have := Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2) (Complex.I * τ)
    simpa using this
  refine ⟨?_, ?_, ?_⟩
  · intro τ
    unfold mult
    rw [norm_div, norm_mul, h2, one_mul, ← hconj, Complex.Gamma_conj, Complex.norm_conj]
    apply div_self
    rw [norm_ne_zero_iff]
    have := Complex.Gamma_ne_zero_of_re_pos (hre τ)
    rwa [← hconj, Complex.Gamma_conj, map_ne_zero] at this
  · simp [mult]
  · intro τ
    unfold mult
    rw [map_div₀, map_mul, ← Complex.Gamma_conj, ← Complex.Gamma_conj, hconj]
    have harg : (2 : ℂ).arg ≠ Real.pi := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.arg_ofReal_of_nonneg (by norm_num)]
      exact Real.pi_pos.ne
    have e1 : starRingEnd ℂ ((2 : ℂ) ^ (Complex.I * τ)) = (2 : ℂ) ^ (Complex.I * ((-τ : ℝ) : ℂ)) := by
      have := Complex.conj_cpow 2 (starRingEnd ℂ (Complex.I * τ)) harg
      rw [Complex.conj_conj, map_ofNat] at this
      rw [← this]
      congr 1
      simp
    have e2 : starRingEnd ℂ (1 - Complex.I * (τ : ℂ) / 2) = 1 - Complex.I * ((-τ : ℝ) : ℂ) / 2 := by
      simp only [map_sub, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_one,
        map_ofNat, Complex.ofReal_neg]
      ring
    rw [e1, e2, show (1:ℂ) - Complex.I * τ / 2 = 1 + Complex.I * ((-τ:ℝ):ℂ) / 2 by push_cast; ring]

theorem mellinStatement_holds (hJ : J0Statement) (_hB : BesselPlaneStatement) :
    MellinStatement := by
  intro ξ x hx
  refine ⟨MellinAux.integrable_besselG hJ hx, ?_⟩
  set s : ℂ := Complex.I * ((2 * π * ξ : ℝ) : ℂ) with hs_def
  have hs : s.re = 0 := by simp [s]
  have hA : 0 < x ^ 2 := by positivity
  have hAB : x ^ 2 ≤ 1 + x ^ 2 := by linarith
  rw [MellinAux.lhs_eq_mellin, MellinAux.betaF_eq_mellin]
  have h1 := MellinAux.step1 hJ hx hs
  have h2 := MellinAux.step2 hA hAB hs
  have h3 := MellinAux.step3 hA hAB hs
  have h4 := MellinAux.gamma_identity hs
  have hmult : mult (2 * π * ξ) =
      (2 : ℂ) ^ s * Complex.Gamma (1 + s / 2) / Complex.Gamma (1 - s / 2) := rfl
  rw [hmult]
  have hG : Complex.Gamma (1 - s) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp [hs])
  have hpi : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  apply mul_left_cancel₀ (mul_ne_zero hpi hG)
  linear_combination (Real.sqrt π : ℂ) * h1 + h2 + Complex.Gamma ((1 - s) / 2) / 2 * h3 +
    (mellin (MellinAux.IF (x ^ 2) (1 + x ^ 2)) (-s / 2) / 2) * h4

end ChowlaOpus
