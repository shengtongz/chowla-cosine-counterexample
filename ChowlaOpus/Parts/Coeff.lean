module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

namespace CoeffAux

variable {ρ : ℝ → ℝ}

/-! ### The bump `ρ`, the cutoff `ψ` and the mollifier `ρ_h` -/

lemma rho0_pos (hρ : IsBump ρ) : 0 < ρ 0 := by
  by_contra h
  push Not at h
  have h0 : ∀ x, ρ x = 0 := fun x => le_antisymm ((hρ.le_at_zero x).trans h) (hρ.nonneg x)
  have h1 := hρ.integral_eq
  simp [h0] at h1

lemma psi_nonneg (hρ : IsBump ρ) (u : ℝ) : 0 ≤ psiF ρ u :=
  div_nonneg (hρ.nonneg u) (rho0_pos hρ).le

lemma psi_le_one (hρ : IsBump ρ) (u : ℝ) : psiF ρ u ≤ 1 :=
  div_le_one_of_le₀ (hρ.le_at_zero u) (rho0_pos hρ).le

lemma psi_zero (hρ : IsBump ρ) : psiF ρ 0 = 1 := div_self (rho0_pos hρ).ne'

lemma psi_supp (hρ : IsBump ρ) (u : ℝ) (hu : 1 ≤ |u|) : psiF ρ u = 0 := by
  simp [psiF, hρ.supp u hu]

lemma psi_even (hρ : IsBump ρ) (u : ℝ) : psiF ρ (-u) = psiF ρ u := by
  simp [psiF, hρ.even u]

lemma psi_contDiff (hρ : IsBump ρ) : ContDiff ℝ ∞ (psiF ρ) :=
  hρ.smooth.div_const _

lemma rhoH_nonneg (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (y : ℝ) : 0 ≤ rhoH ρ h y :=
  div_nonneg (hρ.nonneg _) hh.le

lemma rhoH_even (hρ : IsBump ρ) (h y : ℝ) : rhoH ρ h (-y) = rhoH ρ h y := by
  simp [rhoH, neg_div, hρ.even]

lemma rhoH_supp (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (y : ℝ) (hy : h ≤ |y|) :
    rhoH ρ h y = 0 := by
  have : 1 ≤ |y / h| := by
    rw [abs_div, abs_of_pos hh, le_div_iff₀ hh]; linarith
  simp [rhoH, hρ.supp _ this]

lemma rhoH_le (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (y : ℝ) : rhoH ρ h y ≤ ρ 0 / h :=
  div_le_div_of_nonneg_right (hρ.le_at_zero _) hh.le

lemma rhoH_contDiff (hρ : IsBump ρ) (h : ℝ) : ContDiff ℝ ∞ (rhoH ρ h) :=
  (hρ.smooth.comp (contDiff_id.div_const h)).div_const h

lemma rhoH_continuous (hρ : IsBump ρ) (h : ℝ) : Continuous (rhoH ρ h) :=
  (rhoH_contDiff hρ h).continuous

lemma rhoH_hasCompactSupport (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) :
    HasCompactSupport (rhoH ρ h) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -h) (b := h)) (fun y hy => ?_)
  apply rhoH_supp hρ hh
  simp only [Set.mem_Icc, not_and_or, not_le] at hy
  rcases hy with hy | hy
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

lemma rhoH_integral (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : ∫ y, rhoH ρ h y = 1 := by
  unfold rhoH
  rw [integral_div, Measure.integral_comp_div (fun y => ρ y) h, hρ.integral_eq, abs_of_pos hh,
    smul_eq_mul, mul_one, div_self hh.ne']

lemma rhoH_integrable (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : Integrable (rhoH ρ h) :=
  (rhoH_continuous hρ h).integrable_of_hasCompactSupport (rhoH_hasCompactSupport hρ hh)

lemma hT_pos {T : ℝ} (hTpos : 0 < T) : 0 < hT T := by unfold hT; positivity

lemma aT_nonneg (hρ : IsBump ρ) (T : ℝ) : 0 ≤ aT ρ T := by
  unfold aT; have := (rho0_pos hρ).le; positivity

/-- Integrability of `ρ_h · g(x - ·)` for integrable `g`. -/
lemma integrable_rhoH_mul (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) {g : ℝ → ℝ}
    (hg : Integrable g) (x : ℝ) : Integrable (fun y => rhoH ρ h y * g (x - y)) := by
  refine (hg.comp_sub_left x).bdd_mul (c := ρ 0 / h)
    (rhoH_continuous hρ h).aestronglyMeasurable ?_
  refine ae_of_all _ (fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (rhoH_nonneg hρ hh y)]
  exact rhoH_le hρ hh y

/-! ### Consequences of `AnnulusStatement` -/

lemma ellF_nonneg (hA : AnnulusStatement) (x : ℝ) : 0 ≤ ellF x := hA.2.2.2.2.2.1 x

lemma ellF_integrable (hA : AnnulusStatement) : Integrable ellF := hA.2.2.2.2.2.2.2.1

lemma ellF_even (hA : AnnulusStatement) (x : ℝ) : ellF (-x) = ellF x := by
  obtain ⟨-, -, hBeven, -⟩ := hA
  simp [ellF, hBeven]

lemma betaF_integrable (hA : AnnulusStatement) (ξ : ℝ) : Integrable (betaF ξ) := by
  obtain ⟨-, -, -, -, -, -, -, hellint, -, -, -, -, -, -, hβm, hβle, -⟩ := hA
  exact hellint.mono' (hβm ξ).aestronglyMeasurable (ae_of_all _ (hβle ξ))

/-! ### Smoothness -/

lemma conv_contDiff (hA : AnnulusStatement) (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (ξ : ℝ) :
    ContDiff ℝ 2 (fun x => ∫ y, (rhoH ρ h y : ℂ) * betaF ξ (x - y)) := by
  have heq : (fun x => ∫ y, (rhoH ρ h y : ℂ) * betaF ξ (x - y)) =
      convolution (rhoH ρ h) (betaF ξ) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    ext x
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, Complex.real_smul]
  rw [heq]
  exact (rhoH_hasCompactSupport hρ hh).contDiff_convolution_left (n := 2) _
    ((rhoH_contDiff hρ h).of_le (by norm_cast))
    (betaF_integrable hA ξ).locallyIntegrable

lemma psi_scaled_contDiff (hρ : IsBump ρ) (c T : ℝ) :
    ContDiff ℝ 2 (fun x => ((c * psiF ρ (x / T ^ 2) : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_const.mul
    (((psi_contDiff hρ).of_le (by norm_cast)).comp (contDiff_id.div_const _)))

/-! ### The zeroth coefficient -/

/-- The smoothed label mean `(ρ_h ∗ ℓ)(x)`. -/
noncomputable def Sm (ρ : ℝ → ℝ) (h x : ℝ) : ℝ := ∫ y, rhoH ρ h y * ellF (x - y)

lemma bL_zero_eq (hA : AnnulusStatement) (ρ : ℝ → ℝ) (T : ℝ) (J : ℕ) (x : ℝ) :
    bL ρ T J 0 x = ((psiF ρ (x / T ^ 2) / (T * (1 + aT ρ T)) * Sm ρ (hT T) x : ℝ) : ℂ) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hβ0, -⟩ := hA
  unfold bL Sm
  simp only [Int.cast_zero, zero_div, hβ0, fejerCoeff_zero]
  simp_rw [← Complex.ofReal_mul]
  rw [integral_complex_ofReal, ← Complex.ofReal_mul]
  congr 1; ring

lemma Sm_nonneg (hA : AnnulusStatement) (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    0 ≤ Sm ρ h x :=
  integral_nonneg (fun y => mul_nonneg (rhoH_nonneg hρ hh y) (ellF_nonneg hA _))

lemma ellF_le_log_add (hA : AnnulusStatement) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (y : ℝ)
    (hy : y ≠ 0) : ellF y ≤ Real.log h⁻¹ + ellF (y / h) := by
  obtain ⟨-, -, -, -, hell, -⟩ := hA
  have hyh : y / h ≠ 0 := div_ne_zero hy hh.ne'
  rw [hell y hy, hell _ hyh]
  have hy2 : 0 < y ^ 2 := by positivity
  have h1 : 1 ≤ h⁻¹ ^ 2 := by
    have : 1 ≤ h⁻¹ := one_le_inv_iff₀.mpr ⟨hh, hh1⟩
    nlinarith
  have heq : h⁻¹ ^ 2 * (1 + ((y / h) ^ 2)⁻¹) = h⁻¹ ^ 2 + (y ^ 2)⁻¹ := by
    field_simp
  have hle : Real.log (1 + (y ^ 2)⁻¹) ≤ Real.log (h⁻¹ ^ 2 * (1 + ((y / h) ^ 2)⁻¹)) := by
    apply Real.log_le_log (by positivity)
    rw [heq]; linarith
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow] at hle
  push_cast at hle
  linarith

lemma Sm_zero_le (hA : AnnulusStatement) (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    Sm ρ h 0 ≤ Real.log h⁻¹ + ρ 0 * π := by
  have hellint := ellF_integrable hA
  have hellpi : ∫ x, ellF x = π := hA.2.2.2.2.2.2.2.2.1
  have hρint : Integrable (fun z => ρ z * ellF z) := by
    refine hellint.bdd_mul (c := ρ 0) hρ.smooth.continuous.aestronglyMeasurable
      (ae_of_all _ (fun z => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg z)]
    exact hρ.le_at_zero z
  have i2 : Integrable (fun y => rhoH ρ h y * ellF (y / h)) := by
    refine (hellint.comp_div hh.ne').bdd_mul (c := ρ 0 / h)
      (rhoH_continuous hρ h).aestronglyMeasurable (ae_of_all _ (fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (rhoH_nonneg hρ hh y)]
    exact rhoH_le hρ hh y
  have i1 : Integrable (fun y => rhoH ρ h y * Real.log h⁻¹) :=
    (rhoH_integrable hρ hh).mul_const _
  have h1 : Sm ρ h 0 ≤ ∫ y, rhoH ρ h y * (Real.log h⁻¹ + ellF (y / h)) := by
    unfold Sm
    refine integral_mono_ae (integrable_rhoH_mul hρ hh hellint 0) ?_ ?_
    · simp_rw [mul_add]
      exact i1.add i2
    · filter_upwards [Measure.ae_ne volume 0] with y hy
      rw [zero_sub, ellF_even hA]
      exact mul_le_mul_of_nonneg_left (ellF_le_log_add hA hh hh1 y hy) (rhoH_nonneg hρ hh y)
  have h2 : ∫ y, rhoH ρ h y * (Real.log h⁻¹ + ellF (y / h)) =
      Real.log h⁻¹ + ∫ z, ρ z * ellF z := by
    simp_rw [mul_add]
    rw [integral_add i1 i2, integral_mul_const, rhoH_integral hρ hh, one_mul]
    congr 1
    unfold rhoH
    have : (fun y => ρ (y / h) / h * ellF (y / h)) =
        fun y => h⁻¹ * ((fun z => ρ z * ellF z) (y / h)) := by
      ext y; simp only; ring
    rw [this, integral_const_mul, Measure.integral_comp_div (fun z => ρ z * ellF z) h, abs_of_pos hh,
      smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hh.ne', one_mul]
  have h3 : ∫ z, ρ z * ellF z ≤ ρ 0 * π := by
    rw [← hellpi, ← integral_const_mul]
    refine integral_mono hρint (hellint.const_mul _) (fun z => ?_)
    exact mul_le_mul_of_nonneg_right (hρ.le_at_zero z) (ellF_nonneg hA z)
  linarith

lemma Sm_int_le (hA : AnnulusStatement) (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (hh2 : h ≤ 1 / 2)
    (j : ℤ) (hj : j ≠ 0) : Sm ρ h j ≤ 2 / (j : ℝ) ^ 2 := by
  have hellint := ellF_integrable hA
  have hellle : ∀ x, x ≠ 0 → ellF x ≤ 1 / (2 * x ^ 2) := hA.2.2.2.2.2.2.1
  have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hj
  have pw : ∀ y, rhoH ρ h y * ellF (j - y) ≤ rhoH ρ h y * (2 / (j : ℝ) ^ 2) := by
    intro y
    by_cases hy : h ≤ |y|
    · rw [rhoH_supp hρ hh y hy]; simp
    · push Not at hy
      apply mul_le_mul_of_nonneg_left _ (rhoH_nonneg hρ hh y)
      have hjy : |(j : ℝ)| / 2 ≤ |(j : ℝ) - y| := by
        have := abs_sub_abs_le_abs_sub (j : ℝ) y
        linarith
      have hpos : 0 < |(j : ℝ)| / 2 := by linarith
      have hne : (j : ℝ) - y ≠ 0 := by
        intro h0; rw [h0, abs_zero] at hjy; linarith
      calc ellF (j - y) ≤ 1 / (2 * ((j : ℝ) - y) ^ 2) := hellle _ hne
        _ ≤ 1 / (2 * (|(j : ℝ)| / 2) ^ 2) := by
          apply one_div_le_one_div_of_le (by positivity)
          have : (|(j : ℝ)| / 2) ^ 2 ≤ ((j : ℝ) - y) ^ 2 := by
            rw [← sq_abs ((j : ℝ) - y)]; exact pow_le_pow_left₀ hpos.le hjy 2
          linarith
        _ = 2 / (j : ℝ) ^ 2 := by
          rw [div_pow, sq_abs]
          have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
          field_simp
  unfold Sm
  calc ∫ y, rhoH ρ h y * ellF (j - y) ≤ ∫ y, rhoH ρ h y * (2 / (j : ℝ) ^ 2) :=
        integral_mono (integrable_rhoH_mul hρ hh hellint _)
          ((rhoH_integrable hρ hh).mul_const _) pw
    _ = 2 / (j : ℝ) ^ 2 := by rw [integral_mul_const, rhoH_integral hρ hh, one_mul]

lemma Sm_ge (hA : AnnulusStatement) (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (hh2 : h ≤ 1 / 2)
    (x : ℝ) (hx : |x| ≤ 1 / 2) : Real.log 2 / 2 ≤ Sm ρ h x := by
  have hellint := ellF_integrable hA
  have hell : ∀ x, x ≠ 0 → ellF x = Real.log (1 + (x ^ 2)⁻¹) / 2 := hA.2.2.2.2.1
  have pw : ∀ᵐ y, rhoH ρ h y * (Real.log 2 / 2) ≤ rhoH ρ h y * ellF (x - y) := by
    filter_upwards [Measure.ae_ne volume x] with y hyx
    by_cases hy : h ≤ |y|
    · rw [rhoH_supp hρ hh y hy]; simp
    · push Not at hy
      apply mul_le_mul_of_nonneg_left _ (rhoH_nonneg hρ hh y)
      have hne : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hyx)
      rw [hell _ hne]
      have h1 : |x - y| ≤ 1 := by
        have := abs_sub x y
        linarith
      have h2 : (x - y) ^ 2 ≤ 1 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (x - y)]
      have h3 : 1 ≤ ((x - y) ^ 2)⁻¹ := one_le_inv_iff₀.mpr ⟨by positivity, h2⟩
      have : Real.log 2 ≤ Real.log (1 + ((x - y) ^ 2)⁻¹) :=
        Real.log_le_log (by norm_num) (by linarith)
      linarith
  unfold Sm
  calc Real.log 2 / 2 = ∫ y, rhoH ρ h y * (Real.log 2 / 2) := by
        rw [integral_mul_const, rhoH_integral hρ hh, one_mul]
    _ ≤ _ := integral_mono_ae ((rhoH_integrable hρ hh).mul_const _)
          (integrable_rhoH_mul hρ hh hellint x) pw

lemma hasSum_int_inv_sq : HasSum (fun j : ℤ => 1 / (j : ℝ) ^ 2) (π ^ 2 / 3) := by
  have h1 : HasSum (fun n : ℕ => 1 / (((n : ℤ) : ℝ)) ^ 2) (π ^ 2 / 6) := by
    have := hasSum_zeta_two
    simp only [Int.cast_natCast]
    exact this
  have h2 : HasSum (fun n : ℕ => 1 / (((-((n : ℤ) + 1)) : ℤ) : ℝ) ^ 2) (π ^ 2 / 6) := by
    have h0 := (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
    have e : (fun n : ℕ => 1 / (((-((n : ℤ) + 1)) : ℤ) : ℝ) ^ 2) =
        fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
      ext n; push_cast; ring
    rw [e]
    simpa using h0
  have := HasSum.of_nat_of_neg_add_one (f := fun j : ℤ => 1 / (j : ℝ) ^ 2) h1 h2
  rw [show π ^ 2 / 3 = π ^ 2 / 6 + π ^ 2 / 6 by ring]
  exact this

end CoeffAux

open CoeffAux in
theorem coeffStatement_holds (hA : AnnulusStatement) : CoeffStatement := by
  intro ρ hρ T hT1 J l
  have hT0 : 0 < T := by linarith
  have hh : 0 < hT T := hT_pos hT0
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hβc, hβe⟩ := id hA
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (psi_scaled_contDiff hρ _ _).mul (conv_contDiff hA hρ hh _)
  · intro x hx
    have hT2 : 0 < T ^ 2 := by positivity
    have : 1 ≤ |x / T ^ 2| := by
      rw [abs_div, abs_of_pos hT2, le_div_iff₀ hT2]; linarith
    simp [bL, psi_supp hρ _ this]
  · intro x
    unfold bL
    rw [neg_div, psi_even hρ]
    congr 1
    rw [← integral_neg_eq_self]
    congr 1; ext y
    rw [rhoH_even hρ, show -x - -y = -(x - y) by ring, hβe]
  · intro x
    unfold bL
    rw [fejerCoeff_neg, Int.cast_neg, neg_div]
    simp_rw [hβc]
    rw [map_mul, Complex.conj_ofReal, ← integral_conj]
    congr 1; congr 1; ext y
    rw [map_mul, Complex.conj_ofReal]
  · intro x
    rw [bL_zero_eq hA]
    refine ⟨Complex.ofReal_im _, ?_⟩
    rw [Complex.ofReal_re]
    have ha := aT_nonneg hρ T
    exact mul_nonneg (div_nonneg (psi_nonneg hρ _) (by positivity)) (Sm_nonneg hA hρ hh x)
  · intro hl
    funext x
    simp [bL, fejerCoeff_eq_zero J l hl]

open CoeffAux in
theorem coeffMassStatement_holds (hA : AnnulusStatement) : CoeffMassStatement := by
  intro ρ hρ
  have hρ0 := rho0_pos hρ
  -- `ψ ≥ 1/2` near `0`
  obtain ⟨δ, hδ, hψδ⟩ : ∃ δ > 0, ∀ u, |u| < δ → 1 / 2 ≤ psiF ρ u := by
    have hc : ContinuousAt (psiF ρ) 0 := (psi_contDiff hρ).continuous.continuousAt
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, hδ, hδ'⟩ := hc (1 / 2) (by norm_num)
    refine ⟨δ, hδ, fun u hu => ?_⟩
    have := hδ' (x := u) (by simpa [Real.dist_eq] using hu)
    rw [Real.dist_eq, psi_zero hρ] at this
    have := (abs_lt.mp this).1
    linarith
  -- `a → 0`
  obtain ⟨T₁, hT₁⟩ : ∃ T₁, ∀ T ≥ T₁, aT ρ T ≤ 1 := by
    have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul (8 * ρ 0)
    rw [mul_zero] at ht
    obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp
      (ht.eventually (ge_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
    refine ⟨T₁, fun T hT => ?_⟩
    have := hT₁ T hT
    unfold aT
    linarith [this, show 8 * ρ 0 * T ^ 2 * Real.exp (-T) = 8 * ρ 0 * (T ^ 2 * Real.exp (-T))
      by ring]
  refine ⟨9 + ρ 0 * π, Real.log 2 / 8, max (max 3 T₁) (1 / δ), by positivity, by positivity, ?_⟩
  intro T hTle J
  have hT3 : 3 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTle
  have hTT₁ : T₁ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hTle
  have hTδ : 1 / δ ≤ T := le_trans (le_max_right _ _) hTle
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hh : 0 < hT T := hT_pos hT0
  have hh2 : hT T ≤ 1 / 2 := by
    unfold hT
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨hsmooth, hsupp, -, -, hb0, -⟩ := coeffStatement_holds hA ρ hρ T hT1 J 0
  have ha0 := aT_nonneg hρ T
  set b : ℝ → ℝ := fun x => (bL ρ T J 0 x).re with hb
  have hbeq : ∀ x, b x = psiF ρ (x / T ^ 2) / (T * (1 + aT ρ T)) * Sm ρ (hT T) x := by
    intro x; simp only [hb, bL_zero_eq hA, Complex.ofReal_re]
  have hbnn : ∀ x, 0 ≤ b x := fun x => (hb0 x).2
  have hble : ∀ x, b x ≤ Sm ρ (hT T) x / T := by
    intro x
    rw [hbeq]
    have hS := Sm_nonneg hA hρ hh x
    have : psiF ρ (x / T ^ 2) / (T * (1 + aT ρ T)) ≤ 1 / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]
      nlinarith [psi_le_one hρ (x / T ^ 2), psi_nonneg hρ (x / T ^ 2)]
    calc _ ≤ 1 / T * Sm ρ (hT T) x := mul_le_mul_of_nonneg_right this hS
      _ = Sm ρ (hT T) x / T := by ring
  -- comparison function on `ℤ`
  set A := (2 * Real.log T + ρ 0 * π) / T with hA_def
  set g : ℤ → ℝ := fun j => (2 / T) * (1 / (j : ℝ) ^ 2) + (if j = 0 then A else 0) with hg
  have hg_sum : HasSum g ((2 / T) * (π ^ 2 / 3) + A) :=
    (hasSum_int_inv_sq.mul_left (2 / T)).add (hasSum_ite_eq 0 A)
  have hbg : ∀ j : ℤ, b j ≤ g j := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp only [hg, Int.cast_zero, ite_true]
      have := Sm_zero_le hA hρ hh (by linarith)
      calc b 0 ≤ Sm ρ (hT T) 0 / T := by simpa using hble 0
        _ ≤ (Real.log (hT T)⁻¹ + ρ 0 * π) / T := div_le_div_of_nonneg_right this hT0.le
        _ = 2 / T * (1 / 0 ^ 2) + A := by
          rw [hA_def]; unfold hT; rw [inv_inv, Real.log_pow]; push_cast; ring
    · have := Sm_int_le hA hρ hh hh2 j hj
      simp only [hg, hj, ite_false, add_zero]
      calc b j ≤ Sm ρ (hT T) j / T := hble j
        _ ≤ (2 / (j : ℝ) ^ 2) / T := div_le_div_of_nonneg_right this hT0.le
        _ = 2 / T * (1 / (j : ℝ) ^ 2) := by ring
  have hbsum : Summable (fun j : ℤ => b j) :=
    Summable.of_nonneg_of_le (fun j => hbnn j) hbg hg_sum.summable
  refine ⟨hbsum, ?_, ?_⟩
  · have hlog : 1 ≤ Real.log T := by
      rw [Real.le_log_iff_exp_le hT0]
      have := Real.exp_one_lt_d9
      linarith
    have hpi : π < 3.15 := Real.pi_lt_d2
    have hpi0 : 0 < π := Real.pi_pos
    calc ∑' j : ℤ, b j ≤ ∑' j, g j := hbsum.tsum_le_tsum hbg hg_sum.summable
      _ = (2 / T) * (π ^ 2 / 3) + A := hg_sum.tsum_eq
      _ = (2 * π ^ 2 / 3 + 2 * Real.log T + ρ 0 * π) / T := by rw [hA_def]; ring
      _ ≤ (9 + ρ 0 * π) * Real.log T / T := by
        apply div_le_div_of_nonneg_right _ hT0.le
        have : ρ 0 * π ≤ ρ 0 * π * Real.log T := by
          have := mul_pos hρ0 hpi0
          nlinarith
        nlinarith
  · have hbcont : Continuous b := Complex.continuous_re.comp hsmooth.continuous
    have hbcs : HasCompactSupport b := by
      refine HasCompactSupport.intro (isCompact_Icc (a := -T ^ 2) (b := T ^ 2)) (fun x hx => ?_)
      have hT2 : 0 < T ^ 2 := by positivity
      have : T ^ 2 < |x| := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      simp [hb, hsupp x this]
    have hbint : Integrable b := hbcont.integrable_of_hasCompactSupport hbcs
    have hlow : ∀ x ∈ Set.Icc (-(1 / 2 : ℝ)) (1 / 2), Real.log 2 / 8 / T ≤ b x := by
      intro x hx
      have hx' : |x| ≤ 1 / 2 := abs_le.mpr hx
      rw [hbeq]
      have hψ : 1 / 2 ≤ psiF ρ (x / T ^ 2) := by
        apply hψδ
        rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < T ^ 2),
          div_lt_iff₀ (by positivity)]
        have : 1 ≤ δ * T := by rw [div_le_iff₀ hδ] at hTδ; linarith
        nlinarith
      have hS := Sm_ge hA hρ hh hh2 x hx'
      have ha1 := hT₁ T hTT₁
      have h1 : 1 / 2 / (2 * T) ≤ psiF ρ (x / T ^ 2) / (T * (1 + aT ρ T)) :=
        div_le_div₀ (psi_nonneg hρ _) hψ (by positivity) (by nlinarith)
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      calc Real.log 2 / 8 / T = (1 / 2 / (2 * T)) * (Real.log 2 / 2) := by
            field_simp; ring
        _ ≤ _ := mul_le_mul h1 hS (by positivity)
            (div_nonneg (psi_nonneg hρ _) (by positivity))
    calc Real.log 2 / 8 / T
        = Real.log 2 / 8 / T * volume.real (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
          rw [Real.volume_real_Icc_of_le (by norm_num)]; ring
      _ ≤ ∫ x in Set.Icc (-(1 / 2 : ℝ)) (1 / 2), b x :=
          setIntegral_ge_of_const_le_real measurableSet_Icc (by simp) hlow hbint.integrableOn
      _ ≤ ∫ x, b x := setIntegral_le_integral hbint (ae_of_all _ hbnn)

end ChowlaOpus
