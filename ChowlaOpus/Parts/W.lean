module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.WAux

open ChowlaOpus

variable {ρ : ℝ → ℝ}

lemma rho_integrable (hρ : IsBump ρ) : Integrable ρ :=
  Integrable.of_integral_ne_zero (by rw [hρ.integral_eq]; norm_num)

lemma hT_pos {T : ℝ} (hT1 : 1 ≤ T) : 0 < hT T := by unfold hT; positivity

lemma rhoH_eq {T : ℝ} (y : ℝ) : rhoH ρ (hT T) y = ρ (y * T ^ 2) * T ^ 2 := by
  unfold rhoH hT; simp [div_inv_eq_mul]

lemma rhoH_nonneg (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) (y : ℝ) : 0 ≤ rhoH ρ (hT T) y := by
  unfold rhoH; exact div_nonneg (hρ.nonneg _) (hT_pos hT1).le

lemma rhoH_le (hρ : IsBump ρ) {T : ℝ} (y : ℝ) : rhoH ρ (hT T) y ≤ ρ 0 * T ^ 2 := by
  rw [rhoH_eq]; exact mul_le_mul_of_nonneg_right (hρ.le_at_zero _) (by positivity)

lemma rhoH_continuous (hρ : IsBump ρ) (T : ℝ) : Continuous (rhoH ρ (hT T)) := by
  unfold rhoH; exact (hρ.smooth.continuous.comp (continuous_id.div_const _)).div_const _

lemma rhoH_integrable (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) : Integrable (rhoH ρ (hT T)) := by
  unfold rhoH; exact ((rho_integrable hρ).comp_div (hT_pos hT1).ne').div_const _

lemma rhoH_integral (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) : ∫ y, rhoH ρ (hT T) y = 1 := by
  unfold rhoH
  rw [integral_div, Measure.integral_comp_div, hρ.integral_eq, abs_of_pos (hT_pos hT1)]
  simp [(hT_pos hT1).ne']

lemma ee_continuous : Continuous ee := by unfold ee; fun_prop

lemma fejer_abs_le (J : ℕ) (t : ℝ) : |fejer J t| ≤ (Finset.Icc (-(J : ℤ)) J).card := by
  unfold fejer
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [abs_mul, abs_of_nonneg (fejerCoeff_nonneg _ _)]
  calc fejerCoeff J k * |Real.cos (2 * Real.pi * k * t)| ≤ 1 * 1 :=
        mul_le_mul (fejerCoeff_le_one J k) (abs_cos_le_one _) (abs_nonneg _) zero_le_one
    _ = ((1 : ℕ) : ℝ) := by norm_num

variable (ρ) in
/-- The integrand `(σ, y) ↦ ρ_h(y) B_σ(x - y)`. -/
noncomputable def G (T x : ℝ) (p : ℝ × ℝ) : ℝ := rhoH ρ (hT T) p.2 * annB p.1 (x - p.2)

lemma annB_measurable_snd (hA : AnnulusStatement) (σ : ℝ) : Measurable (annB σ) := by
  have h : Measurable (Function.uncurry annB) := hA.1
  have e : annB σ = Function.uncurry annB ∘ (fun y => (σ, y)) := rfl
  rw [e]; exact h.comp (measurable_const.prodMk measurable_id)

lemma G_measurable (hA : AnnulusStatement) (hρ : IsBump ρ) (T x : ℝ) :
    Measurable (G ρ T x) := by
  have h : Measurable (Function.uncurry annB) := hA.1
  have h1 : Measurable fun p : ℝ × ℝ => rhoH ρ (hT T) p.2 :=
    (rhoH_continuous hρ T).measurable.comp measurable_snd
  have e : (fun p : ℝ × ℝ => annB p.1 (x - p.2)) =
      Function.uncurry annB ∘ (fun p : ℝ × ℝ => (p.1, x - p.2)) := rfl
  have h2 : Measurable fun p : ℝ × ℝ => annB p.1 (x - p.2) := by
    rw [e]; exact h.comp (measurable_fst.prodMk (measurable_const.sub measurable_snd))
  exact h1.mul h2

lemma G_integrable (hA : AnnulusStatement) (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) (x : ℝ) :
    Integrable (G ρ T x) (volume.prod volume) := by
  rw [integrable_prod_iff' (G_measurable hA hρ T x).aestronglyMeasurable]
  constructor
  · filter_upwards [Measure.ae_ne volume x] with y hy
    have hi : Integrable (fun σ => annB σ (x - y)) :=
      hA.2.2.2.1 (x - y) (sub_ne_zero.mpr (Ne.symm hy))
    have e : (fun σ => G ρ T x (σ, y)) = fun σ => rhoH ρ (hT T) y * annB σ (x - y) := rfl
    rw [e]; exact hi.const_mul _
  · have : (fun y => ∫ σ, ‖G ρ T x (σ, y)‖) = fun y => rhoH ρ (hT T) y * ellF (x - y) := by
      ext y
      simp only [G, norm_mul, Real.norm_eq_abs, abs_of_nonneg (rhoH_nonneg hρ hT1 y),
        abs_of_nonneg (hA.2.1 _ _).1]
      rw [integral_const_mul]; rfl
    rw [this]
    refine (hA.2.2.2.2.2.2.2.1.comp_sub_left x).bdd_mul (c := ρ 0 * T ^ 2)
      (rhoH_continuous hρ T).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (rhoH_nonneg hρ hT1 y)]
    exact rhoH_le hρ y

lemma smB_eq (T σ x : ℝ) : smB ρ T σ x = ∫ y, G ρ T x (σ, y) := rfl

lemma smB_integrable (hA : AnnulusStatement) (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) (x : ℝ) :
    Integrable (fun σ => smB ρ T σ x) :=
  (G_integrable hA hρ hT1 x).integral_prod_left

lemma smB_nonneg (hA : AnnulusStatement) (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) (σ x : ℝ) :
    0 ≤ smB ρ T σ x :=
  integral_nonneg fun y => mul_nonneg (rhoH_nonneg hρ hT1 y) (hA.2.1 _ _).1

lemma fubini_beta (hA : AnnulusStatement) (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T) (x ξ : ℝ) :
    ∫ y, (rhoH ρ (hT T) y : ℂ) * betaF ξ (x - y) =
      ∫ σ, ee (-(ξ * σ)) * (smB ρ T σ x : ℂ) := by
  set F : ℝ → ℝ → ℂ := fun σ y => (G ρ T x (σ, y) : ℂ) * ee (-(ξ * σ)) with hFdef
  have hFm : Measurable (Function.uncurry F) := by
    have : Function.uncurry F = fun p : ℝ × ℝ => (G ρ T x p : ℂ) * ee (-(ξ * p.1)) := rfl
    rw [this]
    exact (Complex.measurable_ofReal.comp (G_measurable hA hρ T x)).mul
      ((ee_continuous.comp (continuous_fst.const_mul ξ).neg).measurable)
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) := by
    refine (G_integrable hA hρ hT1 x).mono' hFm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    have : Function.uncurry F p = (G ρ T x p : ℂ) * ee (-(ξ * p.1)) := rfl
    rw [this, norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact le_of_eq (abs_of_nonneg (mul_nonneg (rhoH_nonneg hρ hT1 _) (hA.2.1 _ _).1))
  have hswap := integral_integral_swap hFi
  have hL : ∀ y, ∫ σ, F σ y = (rhoH ρ (hT T) y : ℂ) * betaF ξ (x - y) := by
    intro y
    unfold betaF
    rw [← integral_const_mul]
    congr 1; ext σ
    simp only [hFdef, G]; push_cast; ring
  have hR : ∀ σ, ∫ y, F σ y = ee (-(ξ * σ)) * (smB ρ T σ x : ℂ) := by
    intro σ
    simp only [hFdef]
    rw [integral_mul_const, integral_complex_ofReal, smB_eq, mul_comm]
  simp_rw [hL, hR] at hswap
  exact hswap.symm

lemma smB_measurable (hA : AnnulusStatement) (hρ : IsBump ρ) (T x : ℝ) :
    Measurable (fun σ => smB ρ T σ x) :=
  (G_measurable hA hρ T x).stronglyMeasurable.integral_prod_right'.measurable

lemma fejer_smB_integrable (hA : AnnulusStatement) (hF : FejerStatement) (hρ : IsBump ρ)
    {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ) (s x : ℝ) :
    Integrable (fun σ => fejer J (s - σ / T) * smB ρ T σ x) := by
  refine (smB_integrable hA hρ hT1 x).bdd_mul (c := (Finset.Icc (-(J : ℤ)) J).card) ?_ ?_
  · exact ((hF.1 J).comp (continuous_const.sub (continuous_id.div_const T))).aestronglyMeasurable
  · exact ae_of_all _ fun σ => fejer_abs_le J _

lemma lintegral_unfold {T : ℝ} (hT : 0 < T) (g : ℝ → ENNReal) :
    ∫⁻ σ, g σ = ∑' n : ℤ, ∫⁻ σ in Set.Ico 0 T, g (σ + n * T) := by
  have hU := iUnion_Ico_add_zsmul hT (0 : ℝ)
  rw [← setLIntegral_univ, ← hU, lintegral_iUnion (fun n => measurableSet_Ico)
    (Set.pairwise_disjoint_Ico_add_zsmul (0 : ℝ) T)]
  congr 1; ext n
  rw [← lintegral_indicator measurableSet_Ico, ← lintegral_indicator measurableSet_Ico,
    ← lintegral_add_right_eq_self _ ((n : ℝ) * T)]
  congr 1; ext σ
  simp only [Set.indicator, Set.mem_Ico, zsmul_eq_mul, zero_add]
  push_cast
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; exact h2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
  · exfalso; exact h1 ⟨by linarith [h2.1], by linarith [h2.2]⟩
  · rfl

lemma fejer_integral_Ico (hF : FejerStatement) {T : ℝ} (hT : 0 < T) (J : ℕ) (s : ℝ) :
    ∫ σ in Set.Ico 0 T, fejer J (s - σ / T) = T := by
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT.le]
  have hper : Function.Periodic (fejer J) 1 := hF.2.2.1 J
  rw [intervalIntegral.integral_comp_div (fun u => fejer J (s - u)) hT.ne',
    intervalIntegral.integral_comp_sub_left (fun u => fejer J u)]
  simp only [zero_div, div_self hT.ne', sub_zero, smul_eq_mul]
  have := hper.intervalIntegral_add_eq (s - 1) 0
  rw [sub_add_cancel, zero_add] at this
  rw [this, hF.2.2.2.2.1 J, mul_one]

lemma smB_periodized_le (hA : AnnulusStatement) (hρ : IsBump ρ) {T : ℝ} (hT1 : 1 ≤ T)
    (σ x : ℝ) :
    ∑' n : ℤ, ENNReal.ofReal (smB ρ T (σ + n * T) x) ≤ ENNReal.ofReal (1 + aT ρ T) := by
  have hannm : ∀ τ, Measurable (fun y => annB τ (x - y)) := fun τ =>
    (annB_measurable_snd hA τ).comp (measurable_const.sub measurable_id)
  have hint : ∀ τ, Integrable (fun y => rhoH ρ (hT T) y * annB τ (x - y)) := fun τ =>
    (rhoH_integrable hρ hT1).mul_bdd (c := 1) (hannm τ).aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hA.2.1 _ _).1]; exact (hA.2.1 _ _).2)
  have hmeas : ∀ τ, Measurable (fun y => ENNReal.ofReal (rhoH ρ (hT T) y * annB τ (x - y))) :=
    fun τ => ENNReal.measurable_ofReal.comp ((rhoH_continuous hρ T).measurable.mul (hannm τ))
  have h1 : ∀ n : ℤ, ENNReal.ofReal (smB ρ T (σ + n * T) x) =
      ∫⁻ y, ENNReal.ofReal (rhoH ρ (hT T) y * annB (σ + n * T) (x - y)) := fun n =>
    ofReal_integral_eq_lintegral_ofReal (hint _)
      (ae_of_all _ fun y => mul_nonneg (rhoH_nonneg hρ hT1 y) (hA.2.1 _ _).1)
  simp_rw [h1]
  rw [← lintegral_tsum (fun n => (hmeas _).aemeasurable)]
  set m : ℝ → ℝ := fun z => max (perB T σ z - 1) 0 with hm
  have h2 : ∀ᵐ y ∂volume, ∑' n : ℤ, ENNReal.ofReal (rhoH ρ (hT T) y * annB (σ + n * T) (x - y))
      ≤ ENNReal.ofReal (rhoH ρ (hT T) y) +
        ENNReal.ofReal (ρ 0 * T ^ 2) * ENNReal.ofReal (m (x - y)) := by
    filter_upwards [Measure.ae_ne volume x] with y hy
    have hz : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
    simp_rw [ENNReal.ofReal_mul (rhoH_nonneg hρ hT1 y)]
    rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun n => (hA.2.1 _ _).1)
      (hA.2.2.2.2.2.2.2.2.2.2.2.2.1 T σ (x - y) hT1 hz)]
    have hP : perB T σ (x - y) ≤ 1 + m (x - y) := by
      simp only [hm]; linarith [le_max_left (perB T σ (x - y) - 1) 0]
    calc ENNReal.ofReal (rhoH ρ (hT T) y) * ENNReal.ofReal (perB T σ (x - y))
        ≤ ENNReal.ofReal (rhoH ρ (hT T) y) * ENNReal.ofReal (1 + m (x - y)) :=
          mul_le_mul_right (ENNReal.ofReal_le_ofReal hP) _
      _ = ENNReal.ofReal (rhoH ρ (hT T) y) +
          ENNReal.ofReal (rhoH ρ (hT T) y) * ENNReal.ofReal (m (x - y)) := by
          rw [ENNReal.ofReal_add zero_le_one (le_max_right _ _), ENNReal.ofReal_one, mul_add,
            mul_one]
      _ ≤ ENNReal.ofReal (rhoH ρ (hT T) y) +
          ENNReal.ofReal (ρ 0 * T ^ 2) * ENNReal.ofReal (m (x - y)) := by
          gcongr
          exact rhoH_le hρ y
  refine (lintegral_mono_ae h2).trans ?_
  rw [lintegral_add_left (show Measurable (fun a => ENNReal.ofReal (rhoH ρ (hT T) a)) from
      ENNReal.measurable_ofReal.comp (rhoH_continuous hρ T).measurable),
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal (rhoH_integrable hρ hT1)
      (ae_of_all _ (rhoH_nonneg hρ hT1)), rhoH_integral hρ hT1,
    lintegral_sub_left_eq_self (fun z => ENNReal.ofReal (m z)) x]
  obtain ⟨hmI, hm5⟩ := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.1 T σ hT1
  have hρ0 : 0 ≤ ρ 0 * T ^ 2 := mul_nonneg (hρ.nonneg 0) (sq_nonneg T)
  have hmI0 : 0 ≤ ∫ z, m z := integral_nonneg fun z => le_max_right _ _
  rw [← ofReal_integral_eq_lintegral_ofReal hmI (ae_of_all _ fun z => le_max_right _ _),
    ← ENNReal.ofReal_mul hρ0, ← ENNReal.ofReal_add zero_le_one (mul_nonneg hρ0 hmI0)]
  apply ENNReal.ofReal_le_ofReal
  have h5 := mul_le_mul_of_nonneg_left hm5 hρ0
  have he : 0 ≤ ρ 0 * T ^ 2 * Real.exp (-T) := mul_nonneg hρ0 (Real.exp_pos _).le
  unfold aT
  nlinarith

lemma integral_fejer_smB_le (hA : AnnulusStatement) (hF : FejerStatement) (hρ : IsBump ρ)
    {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ) (s x : ℝ) :
    ∫ σ, fejer J (s - σ / T) * smB ρ T σ x ≤ T * (1 + aT ρ T) := by
  have hT0 : 0 < T := by linarith
  have haT : 0 ≤ aT ρ T := by
    unfold aT; have := hρ.nonneg 0; positivity
  have hnn : ∀ σ, 0 ≤ fejer J (s - σ / T) * smB ρ T σ x := fun σ =>
    mul_nonneg (hF.2.1 _ _) (smB_nonneg hA hρ hT1 σ x)
  have hFc : Continuous (fun σ => fejer J (s - σ / T)) :=
    (hF.1 J).comp (continuous_const.sub (continuous_id.div_const T))
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hnn)
    (fejer_smB_integrable hA hF hρ hT1 J s x).aestronglyMeasurable]
  apply ENNReal.toReal_le_of_le_ofReal (by positivity)
  rw [lintegral_unfold hT0]
  have hper : ∀ σ (n : ℤ), fejer J (s - (σ + n * T) / T) = fejer J (s - σ / T) := by
    intro σ n
    rw [show s - (σ + n * T) / T = (s - σ / T) - n * 1 by field_simp; ring]
    exact (show Function.Periodic (fejer J) 1 from hF.2.2.1 J).sub_int_mul_eq n
  simp_rw [hper, ENNReal.ofReal_mul (hF.2.1 _ _)]
  rw [← lintegral_tsum (fun n : ℤ => (show Measurable (fun σ => ENNReal.ofReal (fejer J (s - σ / T)) *
      ENNReal.ofReal (smB ρ T (σ + (n : ℝ) * T) x)) from
    (ENNReal.measurable_ofReal.comp hFc.measurable).mul
    (ENNReal.measurable_ofReal.comp ((smB_measurable hA hρ T x).comp
      (measurable_id.add_const _)))).aemeasurable)]
  simp_rw [ENNReal.tsum_mul_left]
  calc ∫⁻ σ in Set.Ico 0 T, ENNReal.ofReal (fejer J (s - σ / T)) *
        ∑' n : ℤ, ENNReal.ofReal (smB ρ T (σ + n * T) x)
      ≤ ∫⁻ σ in Set.Ico 0 T, ENNReal.ofReal (fejer J (s - σ / T)) *
        ENNReal.ofReal (1 + aT ρ T) :=
        lintegral_mono fun σ => mul_le_mul_right (smB_periodized_le hA hρ hT1 σ x) _
    _ = ENNReal.ofReal (∫ σ in Set.Ico 0 T, fejer J (s - σ / T)) *
        ENNReal.ofReal (1 + aT ρ T) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          ofReal_integral_eq_lintegral_ofReal
            ((hFc.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self)
            (ae_of_all _ fun σ => hF.2.1 _ _)]
    _ = ENNReal.ofReal (T * (1 + aT ρ T)) := by
        rw [fejer_integral_Ico hF hT0, ← ENNReal.ofReal_mul hT0.le]

end ChowlaOpus.WAux

namespace ChowlaOpus

open WAux

theorem wrepStatement_holds (hA : AnnulusStatement) (hF : FejerStatement) :
    WrepStatement := by
  intro ρ hρ T hT1 J s x
  have hsmI := smB_integrable hA hρ hT1 x
  have hfejI : Integrable (fun σ => fejer J (s - σ / T) * smB ρ T σ x) := by
    refine hsmI.bdd_mul (c := (Finset.Icc (-(J : ℤ)) J).card) ?_ ?_
    · exact ((hF.1 J).comp (continuous_const.sub (continuous_id.div_const T))).aestronglyMeasurable
    · exact ae_of_all _ fun σ => fejer_abs_le J _
  refine ⟨hfejI, ?_⟩
  unfold Wsum bL
  simp_rw [fubini_beta hA hρ hT1 x]
  have hfe := hF.2.2.2.2.2.1 J
  set K : ℝ := T * (1 + aT ρ T)
  set ψ : ℝ := psiF ρ (x / T ^ 2)
  have key : ∀ l ∈ Finset.Icc (-(J : ℤ)) J,
      ((fejerCoeff J l / K * ψ : ℝ) : ℂ) *
        (∫ σ, ee (-((l : ℝ) / T * σ)) * (smB ρ T σ x : ℂ)) * ee (l * s) =
      ((ψ / K : ℝ) : ℂ) *
        ∫ σ, ((fejerCoeff J l : ℂ) * ee (l * (s - σ / T))) * (smB ρ T σ x : ℂ) := by
    intro l _
    rw [← integral_const_mul, ← integral_mul_const, ← integral_const_mul]
    congr 1; ext σ
    rw [show (l : ℝ) * (s - σ / T) = l * s + (-((l : ℝ) / T * σ)) by ring, ee_add]
    push_cast; ring
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, ← integral_finsetSum]
  · simp_rw [← Finset.sum_mul, hfe]
    rw [show (fun σ => (fejer J (s - σ / T) : ℂ) * (smB ρ T σ x : ℂ)) =
      fun σ => ((fejer J (s - σ / T) * smB ρ T σ x : ℝ) : ℂ) by ext; push_cast; rfl]
    rw [integral_complex_ofReal]; push_cast; ring
  · intro l _
    refine (hsmI.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) ?_ (ae_of_all _ fun σ => ?_)
    · exact (continuous_const.mul (ee_continuous.comp
        (continuous_const.mul (continuous_const.sub (continuous_id.div_const T))))).aestronglyMeasurable
    · rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (fejerCoeff_nonneg _ _)]
      exact fejerCoeff_le_one _ _

theorem wboundStatement_holds (hA : AnnulusStatement) (hF : FejerStatement) :
    WboundStatement := by
  intro ρ hρ T hT1 J s x
  obtain ⟨_, hW⟩ := wrepStatement_holds hA hF ρ hρ T hT1 J s x
  rw [hW, Complex.ofReal_im, Complex.ofReal_re]
  have hψ0 : 0 ≤ psiF ρ (x / T ^ 2) := div_nonneg (hρ.nonneg _) (hρ.nonneg 0)
  have hψ1 : psiF ρ (x / T ^ 2) ≤ 1 := div_le_one_of_le₀ (hρ.le_at_zero _) (hρ.nonneg 0)
  have haT : 0 ≤ aT ρ T := by
    unfold aT; have := hρ.nonneg 0; positivity
  have hK : 0 < T * (1 + aT ρ T) := by positivity
  have hI0 : 0 ≤ ∫ σ, fejer J (s - σ / T) * smB ρ T σ x :=
    integral_nonneg fun σ => mul_nonneg (hF.2.1 _ _) (smB_nonneg hA hρ hT1 σ x)
  have hI := integral_fejer_smB_le hA hF hρ hT1 J s x
  refine ⟨rfl, mul_nonneg (div_nonneg hψ0 hK.le) hI0, ?_⟩
  rw [div_mul_eq_mul_div, div_le_one hK]
  calc psiF ρ (x / T ^ 2) * ∫ σ, fejer J (s - σ / T) * smB ρ T σ x
      ≤ 1 * ∫ σ, fejer J (s - σ / T) * smB ρ T σ x := mul_le_mul_of_nonneg_right hψ1 hI0
    _ ≤ T * (1 + aT ρ T) := by rw [one_mul]; exact hI

end ChowlaOpus
