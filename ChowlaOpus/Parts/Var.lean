module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff ENNReal
open Real MeasureTheory Set

namespace ChowlaOpus.VarAux

/-! ### Generic tools -/

lemma lintegral_comp_mul_left' (g : ℝ → ℝ≥0∞) {a : ℝ} (ha : 0 < a) :
    ∫⁻ x, g (a * x) = ENNReal.ofReal a⁻¹ * ∫⁻ y, g y := by
  have h1 : ∫⁻ y, g y ∂(Measure.map (a * ·) volume) = ∫⁻ x, g (a * x) :=
    lintegral_map_equiv g (Homeomorph.mulLeft₀ a ha.ne').toMeasurableEquiv
  rw [← h1, Real.map_volume_mul_left ha.ne', lintegral_smul_measure, abs_of_pos (inv_pos.mpr ha)]
  rfl

lemma lintegral_unfold (f : ℝ → ℝ≥0∞) (c : ℝ) :
    ∫⁻ r, f r = ∑' j : ℤ, ∫⁻ r in Ioc c (c + 1), f (r + j) := by
  rw [← setLIntegral_univ, ← iUnion_Ioc_add_intCast c,
    lintegral_iUnion (fun n => measurableSet_Ioc) (pairwise_disjoint_Ioc_add_intCast c)]
  congr 1; ext j
  rw [← lintegral_indicator measurableSet_Ioc, ← lintegral_indicator measurableSet_Ioc,
    ← lintegral_add_right_eq_self _ (j : ℝ)]
  congr 1; ext r
  simp only [indicator, mem_Ioc]
  have : (c + j < r + j ∧ r + j ≤ c + j + 1) ↔ (c < r ∧ r ≤ c + 1) := by
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp only [this]

lemma lintegral_unfold' (f : ℝ → ℝ≥0∞) (c : ℝ) :
    ∫⁻ r, f r = ∑' j : ℤ, ∫⁻ r in Ioc c (c + 1), f (r - j) := by
  rw [lintegral_unfold f c, ← (Equiv.neg ℤ).tsum_eq]
  congr 1
  ext j
  simp [sub_eq_add_neg]

lemma lintegral_unfold_T (g : ℝ → ℝ≥0∞) {T : ℝ} (hT : 0 < T) :
    ∑' j : ℤ, ∫⁻ s in Ioc 0 1, g (T * s + j * T) = ENNReal.ofReal T⁻¹ * ∫⁻ σ, g σ := by
  rw [← lintegral_comp_mul_left' g hT, lintegral_unfold (fun u => g (T * u)) 0]
  simp only [zero_add]
  congr 1; ext j; congr 1; ext s; ring_nf

lemma ofReal_abs_sub_le {a p : ℝ} {Γ : ℝ≥0∞} (ha : 0 ≤ a) (hp : 0 ≤ p)
    (h1 : ENNReal.ofReal a ≤ ENNReal.ofReal p + Γ) (h2 : ENNReal.ofReal p ≤ ENNReal.ofReal a + Γ) :
    ENNReal.ofReal |a - p| ≤ Γ := by
  rcases eq_or_ne Γ ⊤ with h | h
  · simp [h]
  · have hg : 0 ≤ Γ.toReal := ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_toReal h] at h1 h2 ⊢
    rw [← ENNReal.ofReal_add hp hg, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h1
    rw [← ENNReal.ofReal_add ha hg, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
    exact ENNReal.ofReal_le_ofReal (abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩)

lemma mul_one_sub_le_abs_sub_nat {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) (n : ℕ) :
    w * (1 - w) ≤ |w - n| := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [CharP.cast_eq_zero, sub_zero]; rw [abs_of_nonneg h0]; nlinarith
  · have : (1:ℝ) ≤ n := by exact_mod_cast hn
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; nlinarith

lemma annB_eq_zero_or_one (σ x : ℝ) : annB σ x = 0 ∨ annB σ x = 1 := by
  unfold annB; split_ifs <;> simp

lemma annB_nonneg (σ x : ℝ) : 0 ≤ annB σ x := by
  rcases annB_eq_zero_or_one σ x with h | h <;> rw [h] <;> norm_num

lemma annB_le_one (σ x : ℝ) : annB σ x ≤ 1 := by
  rcases annB_eq_zero_or_one σ x with h | h <;> rw [h] <;> norm_num

lemma annB_support {σ x : ℝ} (h : annB σ x ≠ 0) : |x| ≤ Real.exp σ := by
  unfold annB at h
  split_ifs at h with h'
  · exact h'.1
  · exact absurd rfl h

lemma perB_nat {T σ x : ℝ} (hs : Summable (fun j : ℤ => annB (σ + j * T) x)) :
    ∃ n : ℕ, perB T σ x = n := by
  have hfin : {j : ℤ | annB (σ + j * T) x ≠ 0}.Finite := by
    have h2 : ∀ᶠ j : ℤ in Filter.cofinite, annB (σ + (j:ℝ) * T) x ∈ Ioo (-1/2 : ℝ) (1/2) :=
      hs.tendsto_cofinite_zero (Ioo_mem_nhds (by norm_num : (-1/2:ℝ) < 0)
        (by norm_num : (0:ℝ) < 1/2))
    rw [Filter.eventually_cofinite] at h2
    refine h2.subset ?_
    intro j hj
    simp only [mem_setOf_eq, mem_Ioo] at hj ⊢
    rcases annB_eq_zero_or_one (σ + j*T) x with h | h
    · exact absurd h hj
    · rw [h]; norm_num
  refine ⟨hfin.toFinset.card, ?_⟩
  unfold perB
  rw [tsum_eq_sum (s := hfin.toFinset) (fun j hj => by simpa using hj)]
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Set.Finite.mem_toFinset, mem_setOf_eq] at hj
  rcases annB_eq_zero_or_one (σ + j*T) x with h | h
  · exact absurd h hj
  · simp [h]

lemma continuous_ee : Continuous ee := by
  unfold ee; fun_prop

lemma integral_ee_int (k : ℤ) :
    ∫ s in (0:ℝ)..1, ee (k * s) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp [ee_zero]
  · have hc : (2 * π * Complex.I * k : ℂ) ≠ 0 := by
      have : (k : ℂ) ≠ 0 := by exact_mod_cast hk
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    have : ∀ s : ℝ, ee (k * s) = Complex.exp ((2 * π * Complex.I * k) * s) := by
      intro s; unfold ee; congr 1; push_cast; ring
    simp_rw [this]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * k) = 1 := by
      have := ee_intCast k; unfold ee at this; rw [← this]; congr 1
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero, h1,
      sub_self, zero_div]

lemma parseval (J : ℕ) (b : ℤ → ℂ)
    (hW : ∀ s : ℝ, (∑ l ∈ Finset.Icc (-(J:ℤ)) J, b l * ee (l * s)).im = 0) :
    ∫ s in (0:ℝ)..1, (∑ l ∈ Finset.Icc (-(J:ℤ)) J, b l * ee (l * s)).re *
        (1 - (∑ l ∈ Finset.Icc (-(J:ℤ)) J, b l * ee (l * s)).re)
      = (b 0).re - ∑ l ∈ Finset.Icc (-(J:ℤ)) J, ‖b l‖ ^ 2 := by
  set S := Finset.Icc (-(J:ℤ)) J with hS
  set W : ℝ → ℂ := fun s => ∑ l ∈ S, b l * ee (l * s) with hWdef
  have hee : ∀ l : ℤ, Continuous (fun s : ℝ => ee (l * s)) :=
    fun l => continuous_ee.comp (continuous_const.mul continuous_id)
  have hWc : Continuous W := continuous_finsetSum _ (fun l _ => continuous_const.mul (hee l))
  have h0S : (0:ℤ) ∈ S := by simp [hS]
  have hpt : ∀ s, (((W s).re * (1 - (W s).re) : ℝ) : ℂ) = W s - W s * starRingEnd ℂ (W s) := by
    intro s
    have hre : W s = ((W s).re : ℂ) := by apply Complex.ext <;> simp [hW s, hWdef]
    rw [hre]; simp only [Complex.ofReal_re, Complex.conj_ofReal]; push_cast; ring
  have h1 : ∫ s in (0:ℝ)..1, W s = b 0 := by
    simp only [hWdef]
    rw [intervalIntegral.integral_finsetSum
      (fun l _ => ((hee l).const_mul (b l) |>.intervalIntegrable _ _))]
    simp_rw [intervalIntegral.integral_const_mul, integral_ee_int]
    simp [Finset.sum_ite_eq', h0S]
  have hprod : ∀ s, W s * starRingEnd ℂ (W s) =
      ∑ l ∈ S, ∑ m ∈ S, b l * starRingEnd ℂ (b m) * ee (((l - m : ℤ) : ℝ) * s) := by
    intro s
    have hc : starRingEnd ℂ (W s) = ∑ m ∈ S, starRingEnd ℂ (b m) * ee (-(m * s)) := by
      simp only [hWdef, map_sum, map_mul, ee_neg]
    rw [hc]
    show (∑ l ∈ S, b l * ee (l * s)) * _ = _
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro l _; apply Finset.sum_congr rfl; intro m _
    rw [show ee (((l - m : ℤ) : ℝ) * s) = ee (l * s) * ee (-(m * s)) by
      rw [← ee_add]; congr 1; push_cast; ring]
    ring
  have h2 : ∫ s in (0:ℝ)..1, W s * starRingEnd ℂ (W s) = ∑ l ∈ S, ((‖b l‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hprod]
    rw [intervalIntegral.integral_finsetSum
      (f := fun l s => ∑ m ∈ S, b l * starRingEnd ℂ (b m) * ee (((l - m : ℤ) : ℝ) * s))
      (fun l _ => (continuous_finsetSum _ (fun m _ =>
      continuous_const.mul (hee (l - m)))).intervalIntegrable _ _)]
    apply Finset.sum_congr rfl; intro l hl
    rw [intervalIntegral.integral_finsetSum
      (f := fun m s => b l * starRingEnd ℂ (b m) * ee (((l - m : ℤ) : ℝ) * s))
      (fun m _ => ((hee (l - m)).const_mul _ |>.intervalIntegrable _ _))]
    simp_rw [intervalIntegral.integral_const_mul, integral_ee_int, sub_eq_zero]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [hl, if_true]
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hint : ∫ s in (0:ℝ)..1, (((W s).re * (1 - (W s).re) : ℝ) : ℂ)
      = b 0 - ∑ l ∈ S, ((‖b l‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hpt]
    have hi1 : IntervalIntegrable W volume 0 1 := hWc.intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun s => W s * starRingEnd ℂ (W s)) volume 0 1 :=
      (hWc.mul (Complex.continuous_conj.comp hWc)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hi1 hi2, h1, h2]
  rw [intervalIntegral.integral_ofReal] at hint
  have := congrArg Complex.re hint
  simp only [Complex.ofReal_re, Complex.sub_re, Complex.re_sum] at this
  exact this

/-! ### Integral computations -/

lemma lint_min_exp {h : ℝ} (h0 : 0 < h) (h1 : h ≤ 1) :
    ∫⁻ σ, ENNReal.ofReal (min h (exp (-|σ|))) ≤ ENNReal.ofReal (2 * h * (Real.log h⁻¹ + 1)) := by
  set M := Real.log h⁻¹ with hM
  have hM0 : 0 ≤ M := Real.log_nonneg ((one_le_inv₀ h0).mpr h1)
  have heM : exp (-M) = h := by rw [hM, Real.log_inv, neg_neg, Real.exp_log h0]
  have hpt : ∀ σ, ENNReal.ofReal (min h (exp (-|σ|))) ≤
      (Icc (-M) M).indicator (fun _ => ENNReal.ofReal h) σ +
      ((Ioi M).indicator (fun σ => ENNReal.ofReal (exp (-σ))) σ +
       (Iio (-M)).indicator (fun σ => ENNReal.ofReal (exp σ)) σ) := by
    intro σ
    by_cases hσ : σ ∈ Icc (-M) M
    · rw [indicator_of_mem hσ]
      exact le_add_right (ENNReal.ofReal_le_ofReal (min_le_left _ _))
    · rw [indicator_of_notMem hσ, zero_add]
      simp only [mem_Icc, not_and_or, not_le] at hσ
      rcases hσ with hσ | hσ
      · have h2 : σ ∈ Iio (-M) := hσ
        rw [indicator_of_mem h2, indicator_of_notMem (by simp only [mem_Ioi, not_lt]; linarith),
          zero_add]
        apply ENNReal.ofReal_le_ofReal
        rw [abs_of_neg (by linarith), neg_neg]; exact min_le_right _ _
      · have h2 : σ ∈ Ioi M := hσ
        rw [indicator_of_mem h2, indicator_of_notMem (by simp only [mem_Iio, not_lt]; linarith),
          add_zero]
        apply ENNReal.ofReal_le_ofReal
        rw [abs_of_pos (by linarith)]; exact min_le_right _ _
  refine (lintegral_mono hpt).trans ?_
  rw [lintegral_add_left (measurable_const.indicator measurableSet_Icc),
    lintegral_add_left ((Measurable.ennreal_ofReal (by fun_prop)).indicator measurableSet_Ioi)]
  rw [lintegral_indicator measurableSet_Icc, lintegral_indicator measurableSet_Ioi,
    lintegral_indicator measurableSet_Iio, setLIntegral_const, Real.volume_Icc]
  have hI1 : ∫⁻ σ in Ioi M, ENNReal.ofReal (exp (-σ)) = ENNReal.ofReal h := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi M)
      (ae_of_all _ (fun _ => (exp_pos _).le)), integral_exp_neg_Ioi, heM]
  have hI2 : ∫⁻ σ in Iio (-M), ENNReal.ofReal (exp σ) = ENNReal.ofReal h := by
    rw [setLIntegral_congr Iio_ae_eq_Iic, ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_exp_Iic (-M)) (ae_of_all _ (fun _ => (exp_pos _).le)), integral_exp_Iic, heM]
  rw [hI1, hI2, ← ENNReal.ofReal_mul h0.le, ← ENNReal.ofReal_add h0.le h0.le,
    ← ENNReal.ofReal_add (by nlinarith) (by linarith)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith

lemma lint_min_inv_sq {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ x, ENNReal.ofReal (min c (1 / (2 * x ^ 2))) ≤ ENNReal.ofReal (π * √(2 * c)) := by
  rcases hc.eq_or_lt with rfl | hc'
  · have : ∀ x : ℝ, min 0 (1 / (2 * x ^ 2)) = 0 := fun x => min_eq_left (by positivity)
    simp [this]
  set k := √(2 * c) with hk
  have hk0 : 0 < k := Real.sqrt_pos.mpr (by linarith)
  have hk2 : k ^ 2 = 2 * c := Real.sq_sqrt (by linarith)
  have hpt : ∀ x, min c (1 / (2 * x ^ 2)) ≤ 2 * c * (1 + (k * x) ^ 2)⁻¹ := by
    intro x
    rw [mul_pow, hk2]
    rcases eq_or_ne x 0 with rfl | hx
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, div_zero,
        add_zero, inv_one, mul_one]
      exact (min_le_right _ _).trans (by linarith)
    have hx2 : 0 < x ^ 2 := by positivity
    by_cases h : 2 * c * x ^ 2 ≤ 1
    · refine (min_le_left _ _).trans ?_
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; nlinarith
    · push_neg at h
      refine (min_le_right _ _).trans ?_
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have hcomp := lintegral_comp_mul_left' (fun y => ENNReal.ofReal ((1 + y ^ 2)⁻¹)) hk0
  calc ∫⁻ x, ENNReal.ofReal (min c (1 / (2 * x ^ 2)))
      ≤ ∫⁻ x, ENNReal.ofReal (2 * c * (1 + (k * x) ^ 2)⁻¹) :=
        lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hpt x))
    _ = ENNReal.ofReal (2 * c) * ∫⁻ x, ENNReal.ofReal ((1 + (k * x) ^ 2)⁻¹) := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]; congr 1; ext x
        rw [ENNReal.ofReal_mul (by linarith)]
    _ = ENNReal.ofReal (2 * c) * (ENNReal.ofReal k⁻¹ * ENNReal.ofReal π) := by
        rw [hcomp, ← ofReal_integral_eq_lintegral_ofReal integrable_inv_one_add_sq
          (ae_of_all _ (fun _ => by positivity)), integral_univ_inv_one_add_sq]
    _ = ENNReal.ofReal (π * √(2 * c)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← hk, ← hk2]; field_simp

/-! ### Facts about the bump -/

variable {ρ : ℝ → ℝ}

lemma rho_cont (hρ : IsBump ρ) : Continuous ρ := hρ.smooth.continuous

lemma rho_zero_pos (hρ : IsBump ρ) : 0 < ρ 0 := by
  by_contra h
  push_neg at h
  have h0 : ∀ x, ρ x = 0 := fun x => le_antisymm ((hρ.le_at_zero x).trans h) (hρ.nonneg x)
  have h1 := hρ.integral_eq
  simp [h0] at h1

lemma psi_nonneg (hρ : IsBump ρ) (u : ℝ) : 0 ≤ psiF ρ u :=
  div_nonneg (hρ.nonneg u) (rho_zero_pos hρ).le

lemma psi_le_one (hρ : IsBump ρ) (u : ℝ) : psiF ρ u ≤ 1 :=
  (div_le_one (rho_zero_pos hρ)).mpr (hρ.le_at_zero u)

lemma psi_cont (hρ : IsBump ρ) : Continuous (psiF ρ) := (rho_cont hρ).div_const _

lemma psi_lip (hρ : IsBump ρ) : ∃ L : ℝ, 0 ≤ L ∧ ∀ u, 1 - psiF ρ u ≤ L * |u| := by
  have hcs : HasCompactSupport ρ := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (-1:ℝ)) (b := 1)) (fun x hx => ?_)
    apply hρ.supp
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs hρ.smooth (by simp)
  have h0 := rho_zero_pos hρ
  refine ⟨K / ρ 0, by positivity, fun u => ?_⟩
  have := hK.dist_le_mul u 0
  rw [Real.dist_eq, Real.dist_eq, sub_zero] at this
  unfold psiF
  have e : 1 - ρ u / ρ 0 = (ρ 0 - ρ u) / ρ 0 := by field_simp
  rw [e, div_le_iff₀ h0]
  have e2 : (K:ℝ) / ρ 0 * |u| * ρ 0 = K * |u| := by field_simp
  rw [e2]
  have := le_abs_self (ρ 0 - ρ u)
  rw [abs_sub_comm] at this
  linarith

lemma rhoH_cont (hρ : IsBump ρ) (h : ℝ) : Continuous (rhoH ρ h) := by
  unfold rhoH; exact ((rho_cont hρ).comp (continuous_id.div_const h)).div_const h

lemma rhoH_nonneg (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) (y : ℝ) : 0 ≤ rhoH ρ h y :=
  div_nonneg (hρ.nonneg _) hh.le

lemma rhoH_eq_zero (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) {y : ℝ} (hy : h ≤ |y|) :
    rhoH ρ h y = 0 := by
  unfold rhoH; rw [hρ.supp (y/h) ?_, zero_div]
  rw [abs_div, abs_of_pos hh, le_div_iff₀ hh, one_mul]; exact hy

lemma rhoH_integral (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : ∫ y, rhoH ρ h y = 1 := by
  unfold rhoH
  rw [integral_div, Measure.integral_comp_div (fun y => ρ y) h, hρ.integral_eq, abs_of_pos hh,
    smul_eq_mul, mul_one, div_self hh.ne']

lemma rhoH_integrable (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) : Integrable (rhoH ρ h) := by
  by_contra hni
  have := integral_undef hni
  rw [rhoH_integral hρ hh] at this; norm_num at this

lemma rhoH_lintegral (hρ : IsBump ρ) {h : ℝ} (hh : 0 < h) :
    ∫⁻ y, ENNReal.ofReal (rhoH ρ h y) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (rhoH_integrable hρ hh)
    (ae_of_all _ (rhoH_nonneg hρ hh)), rhoH_integral hρ hh, ENNReal.ofReal_one]

lemma hT_pos {T : ℝ} (hT0 : 0 < T) : 0 < hT T := by unfold hT; positivity

/-! ### Facts about the Fejér kernel -/

lemma fejer_per_int (hF : FejerStatement) (J : ℕ) (t : ℝ) (n : ℤ) :
    fejer J (t + n) = fejer J t := by
  have hp : Function.Periodic (fejer J) 1 := hF.2.2.1 J
  simpa using hp.int_mul n t

lemma fejer_int_shift (hF : FejerStatement) (J : ℕ) (c : ℝ) :
    ∫ s in (0:ℝ)..1, fejer J (s - c) = 1 := by
  rw [intervalIntegral.integral_comp_sub_right (fun s => fejer J s) c]
  have hp : Function.Periodic (fejer J) 1 := hF.2.2.1 J
  rw [show (1:ℝ) - c = (0 - c) + 1 by ring, hp.intervalIntegral_add_eq (0 - c) 0, zero_add]
  exact hF.2.2.2.2.1 J

lemma fejer_lint_shift (hF : FejerStatement) (J : ℕ) (c : ℝ) :
    ∫⁻ s in Ioc 0 1, ENNReal.ofReal (fejer J (s - c)) = 1 := by
  have hc : Continuous (fun s => fejer J (s - c)) :=
    (hF.1 J).comp (continuous_id.sub continuous_const)
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ (fun s => hF.2.1 J _)), ← intervalIntegral.integral_of_le zero_le_one,
    fejer_int_shift hF J c, ENNReal.ofReal_one]

lemma fejer_lint_half (hF : FejerStatement) (J : ℕ) :
    ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((hF.1 J).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ (fun s => hF.2.1 J _)), ← intervalIntegral.integral_of_le (by norm_num)]
  have hp : Function.Periodic (fejer J) 1 := hF.2.2.1 J
  rw [show (∫ t in (-(1/2):ℝ)..(1/2), fejer J t) = ∫ t in (-(1/2):ℝ)..(-(1/2) + 1), fejer J t by
    norm_num, hp.intervalIntegral_add_eq (-(1/2)) 0, zero_add, hF.2.2.2.2.1 J, ENNReal.ofReal_one]

lemma fejer_moment_lint (hF : FejerStatement) : ∃ C : ℝ, 0 < C ∧ ∀ J : ℕ, 1 ≤ J →
    ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r * √|r|) ≤
      ENNReal.ofReal (C / √J) := by
  obtain ⟨C, hC, hmom⟩ := hF.2.2.2.2.2.2
  refine ⟨C, hC, fun J hJ => ?_⟩
  have hc : Continuous (fun r => fejer J r * √|r|) := (hF.1 J).mul (continuous_abs.sqrt)
  rw [← ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ (fun r => mul_nonneg (hF.2.1 J r) (Real.sqrt_nonneg _))),
    ← intervalIntegral.integral_of_le (by norm_num)]
  exact ENNReal.ofReal_le_ofReal (hmom J hJ)

lemma fejer_abs_le (J : ℕ) (t : ℝ) : |fejer J t| ≤ (Finset.Icc (-(J:ℤ)) J).card := by
  unfold fejer
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum (fun k _ => ?_)
  rw [abs_mul, Nat.cast_one]
  have h1 := Real.abs_cos_le_one (2 * π * k * t)
  have h2 : |fejerCoeff J k| ≤ 1 := by
    rw [abs_of_nonneg (fejerCoeff_nonneg J k)]; exact fejerCoeff_le_one J k
  nlinarith [abs_nonneg (fejerCoeff J k), abs_nonneg (Real.cos (2 * π * k * t))]

/-! ### Facts about the annulus slice -/

lemma A_meas (hA : AnnulusStatement) : Measurable (Function.uncurry annB) := hA.1
lemma A_int_sigma (hA : AnnulusStatement) : ∀ x, x ≠ 0 → Integrable (fun σ => annB σ x) :=
  hA.2.2.2.1
lemma A_ell_le (hA : AnnulusStatement) : ∀ x, x ≠ 0 → ellF x ≤ 1 / (2 * x ^ 2) :=
  hA.2.2.2.2.2.2.1
lemma A_slice (hA : AnnulusStatement) :
    ∀ σ, Integrable (annB σ) ∧ ∫ x, annB σ x ≤ 2 * Real.exp (-|σ|) :=
  hA.2.2.2.2.2.2.2.2.2.1
lemma A_E1 (hA : AnnulusStatement) :
    ∀ x δ, x ≠ 0 → ∫ σ, |annB (σ - δ) x - annB σ x| ≤ 2 * min |δ| (ellF x) :=
  hA.2.2.2.2.2.2.2.2.2.2.1
lemma A_E2 (hA : AnnulusStatement) :
    ∀ σ u, ∫ x, |annB σ (x - u) - annB σ x| ≤ min (4 * |u|) (4 * Real.exp (-|σ|)) :=
  hA.2.2.2.2.2.2.2.2.2.2.2.1
lemma A_summ (hA : AnnulusStatement) :
    ∀ T σ x, 1 ≤ T → x ≠ 0 → Summable (fun j : ℤ => annB (σ + j * T) x) :=
  hA.2.2.2.2.2.2.2.2.2.2.2.2.1

lemma measurable_annB_comp (hA : AnnulusStatement) {α : Type*} [MeasurableSpace α]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p => annB (f p) (g p)) := by
  have h := (A_meas hA).comp (hf.prodMk hg)
  simpa only [Function.comp_def, Function.uncurry_apply_pair] using h

lemma measurable_annB_diff (hA : AnnulusStatement) {α : Type*} [MeasurableSpace α]
    {f g h k : α → ℝ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hk : Measurable k) :
    Measurable (fun p => ENNReal.ofReal |annB (f p) (g p) - annB (h p) (k p)|) :=
  (continuous_abs.measurable.comp ((measurable_annB_comp hA hf hg).sub
    (measurable_annB_comp hA hh hk))).ennreal_ofReal

lemma smB_measurable (hρ : IsBump ρ) (hA : AnnulusStatement) (T : ℝ) :
    Measurable (fun p : ℝ × ℝ => smB ρ T p.1 p.2) := by
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => rhoH ρ (hT T) q.2 * annB q.1.1 (q.1.2 - q.2)) :=
    ((rhoH_cont hρ _).measurable.comp measurable_snd).mul
      (measurable_annB_comp hA (measurable_fst.comp measurable_fst)
        ((measurable_snd.comp measurable_fst).sub measurable_snd))
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

lemma smB_comp (hρ : IsBump ρ) (hA : AnnulusStatement) (T : ℝ) {α : Type*} [MeasurableSpace α]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p => smB ρ T (f p) (g p)) := by
  have h := (smB_measurable hρ hA T).comp (hf.prodMk hg)
  simpa only [Function.comp_def] using h

lemma smB_diff_meas (hρ : IsBump ρ) (hA : AnnulusStatement) (T : ℝ) {α : Type*}
    [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun p => ENNReal.ofReal |smB ρ T (f p) (g p) - annB (f p) (g p)|) :=
  (continuous_abs.measurable.comp ((smB_comp hρ hA T hf hg).sub
    (measurable_annB_comp hA hf hg))).ennreal_ofReal

lemma smB_sub_le (hρ : IsBump ρ) (hA : AnnulusStatement) {T : ℝ} (hT0 : 0 < T) (σ x : ℝ) :
    ENNReal.ofReal |smB ρ T σ x - annB σ x| ≤
      ∫⁻ y, ENNReal.ofReal (rhoH ρ (hT T) y) * ENNReal.ofReal |annB σ (x - y) - annB σ x| := by
  have hh := hT_pos hT0
  have hint1 : Integrable (fun y => rhoH ρ (hT T) y * annB σ (x - y)) := by
    refine (rhoH_integrable hρ hh).mul_bdd (c := 1) ?_ (ae_of_all _ (fun y => ?_))
    · exact (measurable_annB_comp hA measurable_const
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (annB_nonneg _ _)]; exact annB_le_one _ _
  have hint2 : Integrable (fun y => rhoH ρ (hT T) y * annB σ x) :=
    (rhoH_integrable hρ hh).mul_const _
  have heq : smB ρ T σ x - annB σ x =
      ∫ y, rhoH ρ (hT T) y * (annB σ (x - y) - annB σ x) := by
    simp_rw [mul_sub]
    rw [integral_sub hint1 hint2, integral_mul_const, rhoH_integral hρ hh, one_mul]
    rfl
  rw [heq, ← Real.eNorm_eq_ofReal_abs]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
  refine lintegral_congr (fun y => ?_)
  rw [Real.eNorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (rhoH_nonneg hρ hh y),
    ENNReal.ofReal_mul (rhoH_nonneg hρ hh y)]

lemma E2_lint (hA : AnnulusStatement) (σ u : ℝ) :
    ∫⁻ x, ENNReal.ofReal |annB σ (x - u) - annB σ x| ≤
      ENNReal.ofReal (min (4 * |u|) (4 * Real.exp (-|σ|))) := by
  have hint : Integrable (fun x => |annB σ (x - u) - annB σ x|) :=
    (((A_slice hA σ).1.comp_sub_right u).sub (A_slice hA σ).1).abs
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun _ => abs_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (A_E2 hA σ u)

lemma E1_lint (hA : AnnulusStatement) {x : ℝ} (hx : x ≠ 0) (δ : ℝ) :
    ∫⁻ σ, ENNReal.ofReal |annB (σ - δ) x - annB σ x| ≤ ENNReal.ofReal (2 * min |δ| (ellF x)) := by
  have hint : Integrable (fun σ => |annB (σ - δ) x - annB σ x|) :=
    (((A_int_sigma hA x hx).comp_sub_right δ).sub (A_int_sigma hA x hx)).abs
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (fun _ => abs_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (A_E1 hA x δ hx)

lemma slice_lint (hA : AnnulusStatement) (σ : ℝ) :
    ∫⁻ x, ENNReal.ofReal (annB σ x) ≤ ENNReal.ofReal (2 * Real.exp (-|σ|)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (A_slice hA σ).1 (ae_of_all _ (annB_nonneg σ))]
  exact ENNReal.ofReal_le_ofReal (A_slice hA σ).2

lemma smooth_err (hρ : IsBump ρ) (hA : AnnulusStatement) {T : ℝ} (hT0 : 0 < T) (σ : ℝ) :
    ∫⁻ x, ENNReal.ofReal |smB ρ T σ x - annB σ x| ≤
      ENNReal.ofReal (4 * min (hT T) (Real.exp (-|σ|))) := by
  have hh := hT_pos hT0
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (rhoH ρ (hT T) p.2) *
      ENNReal.ofReal |annB σ (p.1 - p.2) - annB σ p.1|) :=
    ((rhoH_cont hρ _).measurable.comp measurable_snd).ennreal_ofReal.mul
      (measurable_annB_diff hA measurable_const (by fun_prop) measurable_const measurable_fst)
  calc ∫⁻ x, ENNReal.ofReal |smB ρ T σ x - annB σ x|
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (rhoH ρ (hT T) y) *
          ENNReal.ofReal |annB σ (x - y) - annB σ x| :=
        lintegral_mono (fun x => smB_sub_le hρ hA hT0 σ x)
    _ = ∫⁻ y, ∫⁻ x, ENNReal.ofReal (rhoH ρ (hT T) y) *
          ENNReal.ofReal |annB σ (x - y) - annB σ x| :=
        lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ y, ENNReal.ofReal (rhoH ρ (hT T) y) *
          ∫⁻ x, ENNReal.ofReal |annB σ (x - y) - annB σ x| := by
        refine lintegral_congr (fun y => ?_); rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ y, ENNReal.ofReal (rhoH ρ (hT T) y) *
          ENNReal.ofReal (4 * min (hT T) (Real.exp (-|σ|))) := by
        refine lintegral_mono (fun y => ?_)
        by_cases hy : |y| < hT T
        · gcongr
          refine (E2_lint hA σ y).trans (ENNReal.ofReal_le_ofReal ?_)
          rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 4)]
          exact min_le_min (by linarith) le_rfl
        · push_neg at hy; rw [rhoH_eq_zero hρ hh hy]; simp
    _ = ENNReal.ofReal (4 * min (hT T) (Real.exp (-|σ|))) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, rhoH_lintegral hρ hh, one_mul]

/-! ### The three error functions -/

/-- Physical smoothing error. -/
noncomputable def G1 (ρ : ℝ → ℝ) (T : ℝ) (J : ℕ) (s x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal T⁻¹ * ∫⁻ σ, ENNReal.ofReal (fejer J (s - σ / T)) *
    ENNReal.ofReal |smB ρ T σ x - annB σ x|

/-- Label smoothing error. -/
noncomputable def G2 (T : ℝ) (J : ℕ) (s x : ℝ) : ℝ≥0∞ :=
  ∑' j : ℤ, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
    ENNReal.ofReal |annB (T * s + j * T - T * r) x - annB (T * s + j * T) x|

/-- Taper/normalization error. -/
noncomputable def G3 (ρ : ℝ → ℝ) (T : ℝ) (s x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |psiF ρ (x / T ^ 2) / (1 + aT ρ T) - 1| *
    ∑' j : ℤ, ENNReal.ofReal (annB (T * s + j * T) x)

lemma G1_meas (hρ : IsBump ρ) (hA : AnnulusStatement) (hF : FejerStatement) (T : ℝ) (J : ℕ) :
    Measurable (fun p : ℝ × ℝ => G1 ρ T J p.1 p.2) := by
  unfold G1
  refine measurable_const.mul ?_
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (fejer J (q.1.1 - q.2 / T)) *
      ENNReal.ofReal |smB ρ T q.2 q.1.2 - annB q.2 q.1.2|) := by
    refine ((hF.1 J).measurable.comp ((measurable_fst.comp measurable_fst).sub
      (measurable_snd.div_const T))).ennreal_ofReal.mul ?_
    exact (continuous_abs.measurable.comp (((smB_measurable hρ hA T).comp
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))).sub
      (measurable_annB_comp hA measurable_snd (measurable_snd.comp measurable_fst)))).ennreal_ofReal
  exact hm.lintegral_prod_right'

lemma G2_meas (hA : AnnulusStatement) (hF : FejerStatement) (T : ℝ) (J : ℕ) :
    Measurable (fun p : ℝ × ℝ => G2 T J p.1 p.2) := by
  unfold G2
  refine Measurable.tsum (fun j => ?_)
  have hm : Measurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal (fejer J q.2) *
      ENNReal.ofReal |annB (T * q.1.1 + j * T - T * q.2) q.1.2 - annB (T * q.1.1 + j * T) q.1.2|) :=
    ((hF.1 J).measurable.comp measurable_snd).ennreal_ofReal.mul
      (measurable_annB_diff hA (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
  exact hm.lintegral_prod_right'

lemma G3_meas (hρ : IsBump ρ) (hA : AnnulusStatement) (T : ℝ) :
    Measurable (fun p : ℝ × ℝ => G3 ρ T p.1 p.2) := by
  unfold G3
  refine Measurable.mul ?_ (Measurable.tsum (fun j => ?_))
  · exact (continuous_abs.comp ((((psi_cont hρ).comp (continuous_snd.div_const _)).div_const
      _).sub continuous_const)).measurable.ennreal_ofReal
  · exact (measurable_annB_comp hA (by fun_prop) measurable_snd).ennreal_ofReal

/-! ### Pointwise bounds -/

lemma fejer_annB_integrable (hA : AnnulusStatement) (hF : FejerStatement) {T : ℝ} (J : ℕ)
    {x : ℝ} (hx : x ≠ 0) (s : ℝ) : Integrable (fun σ => fejer J (s - σ / T) * annB σ x) := by
  refine (A_int_sigma hA x hx).bdd_mul (c := (Finset.Icc (-(J:ℤ)) J).card) ?_
    (ae_of_all _ (fun σ => ?_))
  · exact ((hF.1 J).comp (continuous_const.sub (continuous_id.div_const T))).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact fejer_abs_le J _

lemma SA_bound (hρ : IsBump ρ) (hA : AnnulusStatement) (hF : FejerStatement)
    (hW : WrepStatement) {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ) {x : ℝ} (hx : x ≠ 0) (s : ℝ) :
    ENNReal.ofReal (T⁻¹ * |(∫ σ, fejer J (s - σ / T) * smB ρ T σ x) -
      ∫ σ, fejer J (s - σ / T) * annB σ x|) ≤ G1 ρ T J s x := by
  have hT0 : 0 < T := by linarith
  have hint1 := (hW ρ hρ T hT1 J s x).1
  have hint2 := fejer_annB_integrable hA hF (T := T) J hx s
  rw [← integral_sub hint1 hint2, ENNReal.ofReal_mul (by positivity)]
  unfold G1
  gcongr
  rw [← Real.eNorm_eq_ofReal_abs]
  refine (eNorm_integral_le_lintegral_eNorm _).trans (le_of_eq ?_)
  refine lintegral_congr (fun σ => ?_)
  rw [Real.eNorm_eq_ofReal_abs, ← mul_sub, abs_mul, abs_of_nonneg (hF.2.1 J _),
    ENNReal.ofReal_mul (hF.2.1 J _)]

lemma AP_bound (hA : AnnulusStatement) (hF : FejerStatement) {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ)
    {x : ℝ} (hx : x ≠ 0) (s : ℝ) :
    ENNReal.ofReal |T⁻¹ * (∫ σ, fejer J (s - σ / T) * annB σ x) - perB T (T * s) x| ≤
      G2 T J s x := by
  have hT0 : 0 < T := by linarith
  have hsum := A_summ hA T (T * s) x hT1 hx
  have hφint := fejer_annB_integrable hA hF (T := T) J hx s
  have hφnn : ∀ σ, 0 ≤ fejer J (s - σ / T) * annB σ x :=
    fun σ => mul_nonneg (hF.2.1 J _) (annB_nonneg _ _)
  set F : ℝ → ℝ≥0∞ := fun σ => ENNReal.ofReal (fejer J (s - σ / T) * annB σ x) with hFdef
  have hcv : ENNReal.ofReal T⁻¹ * ∫⁻ σ, F σ = ∫⁻ r, F (T * (s - r)) := by
    rw [← lintegral_comp_mul_left' F hT0]
    exact (lintegral_sub_left_eq_self (fun u => F (T * u)) s).symm
  have hA_eq : ENNReal.ofReal (T⁻¹ * ∫ σ, fejer J (s - σ / T) * annB σ x) =
      ∑' j : ℤ, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
        ENNReal.ofReal (annB (T * s + j * T - T * r) x) := by
    rw [ENNReal.ofReal_mul (by positivity), ofReal_integral_eq_lintegral_ofReal hφint
      (ae_of_all _ hφnn), hcv, lintegral_unfold' _ (-(1/2))]
    have hI : Ioc (-(1/2):ℝ) (-(1/2) + 1) = Ioc (-(1/2)) (1/2) := by norm_num
    rw [hI]
    refine tsum_congr (fun j => ?_)
    refine lintegral_congr (fun r => ?_)
    simp only [hFdef]
    have e1 : s - T * (s - (r - j)) / T = r - j := by
      rw [mul_div_cancel_left₀ _ hT0.ne']; ring
    have e2 : T * (s - (r - j)) = T * s + j * T - T * r := by ring
    have e3 : fejer J (r - j) = fejer J r := by
      have := fejer_per_int hF J (r - j) j
      rw [sub_add_cancel] at this; exact this.symm
    rw [e1, e2, e3, ENNReal.ofReal_mul (hF.2.1 J r)]
  have hP_eq : ENNReal.ofReal (perB T (T * s) x) =
      ∑' j : ℤ, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
        ENNReal.ofReal (annB (T * s + j * T) x) := by
    unfold perB
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => annB_nonneg _ _) hsum]
    refine tsum_congr (fun j => ?_)
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, fejer_lint_half hF J, one_mul]
  have hIA0 : 0 ≤ T⁻¹ * ∫ σ, fejer J (s - σ / T) * annB σ x :=
    mul_nonneg (by positivity) (integral_nonneg hφnn)
  have hP0 : 0 ≤ perB T (T * s) x := tsum_nonneg (fun j => annB_nonneg _ _)
  have hfm : Measurable (fun r => ENNReal.ofReal (fejer J r)) := (hF.1 J).measurable.ennreal_ofReal
  have key : ∀ u v : ℝ, ENNReal.ofReal u ≤ ENNReal.ofReal v + ENNReal.ofReal |u - v| := by
    intro u v
    exact (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (u - v)])).trans
      ENNReal.ofReal_add_le
  have hαm : ∀ j : ℤ, Measurable (fun r => ENNReal.ofReal (fejer J r) *
      ENNReal.ofReal (annB (T * s + j * T - T * r) x)) :=
    fun j => hfm.mul (measurable_annB_comp hA (by fun_prop) measurable_const).ennreal_ofReal
  have hβm : ∀ j : ℤ, Measurable (fun r => ENNReal.ofReal (fejer J r) *
      ENNReal.ofReal (annB (T * s + j * T) x)) := fun j => hfm.mul measurable_const
  apply ofReal_abs_sub_le hIA0 hP0
  · rw [hA_eq, hP_eq]; unfold G2; rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum (fun j => ?_)
    refine le_trans (lintegral_mono (fun r => ?_)) (le_of_eq (lintegral_add_left (hβm j) _))
    rw [← mul_add]; gcongr; exact key _ _
  · rw [hA_eq, hP_eq]; unfold G2; rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum (fun j => ?_)
    refine le_trans (lintegral_mono (fun r => ?_)) (le_of_eq (lintegral_add_left (hαm j) _))
    rw [← mul_add]; gcongr
    rw [abs_sub_comm]; exact key _ _

lemma kappa_bound {ψ a B : ℝ} (hψ0 : 0 ≤ ψ) (hψ1 : ψ ≤ 1) (ha : 0 ≤ a) (hB : 1 - ψ ≤ B) :
    |ψ / (1 + a) - 1| ≤ min 1 B + a := by
  have h1a : 0 < 1 + a := by linarith
  have hk1 : ψ / (1 + a) ≤ 1 := (div_le_one h1a).mpr (by linarith)
  rw [abs_of_nonpos (by linarith)]
  have : ψ - a ≤ ψ / (1 + a) := by rw [le_div_iff₀ h1a]; nlinarith
  have hmin : 1 - ψ ≤ min 1 B := le_min (by linarith) hB
  linarith

lemma real_core {W P IS IA κ T : ℝ} (hT0 : 0 < T) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hP0 : 0 ≤ P)
    (hW : W = κ * (T⁻¹ * IS)) :
    |W - P| ≤ T⁻¹ * |IS - IA| + |T⁻¹ * IA - P| + |κ - 1| * P := by
  rw [hW]
  have e : κ * (T⁻¹ * IS) - P = κ * (T⁻¹ * (IS - IA)) + κ * (T⁻¹ * IA - P) + (κ - 1) * P := by
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
  · rw [abs_mul, abs_mul, abs_of_nonneg hκ0, abs_of_pos (inv_pos.mpr hT0)]
    exact mul_le_of_le_one_left (by positivity) hκ1
  · rw [abs_mul, abs_of_nonneg hκ0]; exact mul_le_of_le_one_left (abs_nonneg _) hκ1
  · rw [abs_mul, abs_of_nonneg hP0]

lemma ennreal_core {a b c d : ℝ} {G1 G2 G3 : ℝ≥0∞} (h : a ≤ b + c + d)
    (h1 : ENNReal.ofReal b ≤ G1) (h2 : ENNReal.ofReal c ≤ G2) (h3 : ENNReal.ofReal d = G3) :
    ENNReal.ofReal a ≤ G1 + G2 + G3 :=
  (ENNReal.ofReal_le_ofReal h).trans (ENNReal.ofReal_add_le.trans
    (add_le_add (ENNReal.ofReal_add_le.trans (add_le_add h1 h2)) h3.le))

lemma pointwise (hρ : IsBump ρ) (hA : AnnulusStatement) (hF : FejerStatement)
    (hW : WrepStatement) (hWb : WboundStatement) {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ) {x : ℝ}
    (hx : x ≠ 0) (s : ℝ) :
    ENNReal.ofReal ((Wsum ρ T J s x).re * (1 - (Wsum ρ T J s x).re)) ≤
      G1 ρ T J s x + G2 T J s x + G3 ρ T s x := by
  have hT0 : 0 < T := by linarith
  obtain ⟨-, hrep⟩ := hW ρ hρ T hT1 J s x
  obtain ⟨-, hW0, hW1⟩ := hWb ρ hρ T hT1 J s x
  have ha : 0 ≤ aT ρ T := by unfold aT; have := rho_zero_pos hρ; positivity
  have hκ0 : 0 ≤ psiF ρ (x / T ^ 2) / (1 + aT ρ T) := div_nonneg (psi_nonneg hρ _) (by linarith)
  have hκ1 : psiF ρ (x / T ^ 2) / (1 + aT ρ T) ≤ 1 :=
    (div_le_one (by linarith)).mpr ((psi_le_one hρ _).trans (by linarith))
  have hWeq : (Wsum ρ T J s x).re = psiF ρ (x / T ^ 2) / (1 + aT ρ T) *
      (T⁻¹ * ∫ σ, fejer J (s - σ / T) * smB ρ T σ x) := by
    rw [hrep, Complex.ofReal_re]; simp only [div_eq_mul_inv, mul_inv]; ring
  have hsum := A_summ hA T (T * s) x hT1 hx
  obtain ⟨n, hn⟩ := perB_nat hsum
  have hP0 : 0 ≤ perB T (T * s) x := by rw [hn]; exact Nat.cast_nonneg n
  have hstep1 : (Wsum ρ T J s x).re * (1 - (Wsum ρ T J s x).re) ≤
      |(Wsum ρ T J s x).re - perB T (T * s) x| := by
    rw [hn]; exact mul_one_sub_le_abs_sub_nat hW0 hW1 n
  have hstep2 := real_core (IA := ∫ σ, fejer J (s - σ / T) * annB σ x) hT0 hκ0 hκ1 hP0 hWeq
  have hPe : ENNReal.ofReal (perB T (T * s) x) =
      ∑' j : ℤ, ENNReal.ofReal (annB (T * s + j * T) x) :=
    ENNReal.ofReal_tsum_of_nonneg (fun j => annB_nonneg _ _) hsum
  have h3 : ENNReal.ofReal (|psiF ρ (x / T ^ 2) / (1 + aT ρ T) - 1| * perB T (T * s) x) =
      G3 ρ T s x := by
    unfold G3
    exact (ENNReal.ofReal_mul (abs_nonneg _)).trans
      (congrArg (ENNReal.ofReal |psiF ρ (x / T ^ 2) / (1 + aT ρ T) - 1| * ·) hPe)
  exact ennreal_core (hstep1.trans hstep2) (SA_bound hρ hA hF hW hT1 J hx s)
    (AP_bound hA hF hT1 J hx s) h3

/-! ### Integrated bounds -/

lemma G1_integral (hρ : IsBump ρ) (hA : AnnulusStatement) (hF : FejerStatement) {T : ℝ}
    (hT1 : 1 ≤ T) (J : ℕ) :
    ∫⁻ x, ∫⁻ s in Ioc 0 1, G1 ρ T J s x ≤
      ENNReal.ofReal (T⁻¹ * (4 * (2 * hT T * (Real.log (hT T)⁻¹ + 1)))) := by
  have hT0 : 0 < T := by linarith
  have hh0 := hT_pos hT0
  have hh1 : hT T ≤ 1 := by unfold hT; exact inv_le_one_of_one_le₀ (by nlinarith)
  have step1 : ∀ x, ∫⁻ s in Ioc 0 1, G1 ρ T J s x =
      ENNReal.ofReal T⁻¹ * ∫⁻ σ, ENNReal.ofReal |smB ρ T σ x - annB σ x| := by
    intro x
    have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (fejer J (p.1 - p.2 / T)) *
        ENNReal.ofReal |smB ρ T p.2 x - annB p.2 x|) :=
      ((hF.1 J).measurable.comp (measurable_fst.sub (measurable_snd.div_const T))).ennreal_ofReal.mul
        (smB_diff_meas hρ hA T measurable_snd measurable_const)
    unfold G1
    refine (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).trans
      (congrArg (ENNReal.ofReal T⁻¹ * ·) ?_)
    refine (lintegral_lintegral_swap (f := fun s σ => ENNReal.ofReal (fejer J (s - σ / T)) *
        ENNReal.ofReal |smB ρ T σ x - annB σ x|) hm.aemeasurable).trans
      (lintegral_congr (fun σ => ?_))
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, fejer_lint_shift hF J (σ / T), one_mul]
  have hD' : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal |smB ρ T p.2 p.1 - annB p.2 p.1|) :=
    smB_diff_meas hρ hA T measurable_snd measurable_fst
  simp_rw [step1]
  calc ∫⁻ x, ENNReal.ofReal T⁻¹ * ∫⁻ σ, ENNReal.ofReal |smB ρ T σ x - annB σ x|
      = ENNReal.ofReal T⁻¹ * ∫⁻ x, ∫⁻ σ, ENNReal.ofReal |smB ρ T σ x - annB σ x| :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal T⁻¹ * ∫⁻ σ, ∫⁻ x, ENNReal.ofReal |smB ρ T σ x - annB σ x| :=
        congrArg (ENNReal.ofReal T⁻¹ * ·) (lintegral_lintegral_swap
          (f := fun x σ => ENNReal.ofReal |smB ρ T σ x - annB σ x|) hD'.aemeasurable)
    _ ≤ ENNReal.ofReal T⁻¹ * ∫⁻ σ, ENNReal.ofReal (4 * min (hT T) (Real.exp (-|σ|))) := by
        gcongr with σ; exact smooth_err hρ hA hT0 σ
    _ ≤ ENNReal.ofReal T⁻¹ * ENNReal.ofReal (4 * (2 * hT T * (Real.log (hT T)⁻¹ + 1))) := by
        gcongr
        have : ∀ σ, ENNReal.ofReal (4 * min (hT T) (Real.exp (-|σ|))) =
            ENNReal.ofReal 4 * ENNReal.ofReal (min (hT T) (Real.exp (-|σ|))) :=
          fun σ => ENNReal.ofReal_mul (by norm_num)
        simp_rw [this]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (by norm_num)]
        gcongr; exact lint_min_exp hh0 hh1
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

lemma G2_inner (hA : AnnulusStatement) (hF : FejerStatement) {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ)
    {x : ℝ} (hx : x ≠ 0) :
    ∫⁻ s in Ioc 0 1, G2 T J s x ≤ ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
      (ENNReal.ofReal T⁻¹ * ENNReal.ofReal (2 * min (T * |r|) (1 / (2 * x ^ 2)))) := by
  have hT0 : 0 < T := by linarith
  have hmeas : ∀ j : ℤ, Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (fejer J p.2) *
      ENNReal.ofReal |annB (T * p.1 + j * T - T * p.2) x - annB (T * p.1 + j * T) x|) :=
    fun j => ((hF.1 J).measurable.comp measurable_snd).ennreal_ofReal.mul
      (measurable_annB_diff hA (by fun_prop) measurable_const (by fun_prop) measurable_const)
  have hmeas2 : ∀ j : ℤ, Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal |annB (T * p.1 + j * T - T * p.2) x - annB (T * p.1 + j * T) x|) :=
    fun j => measurable_annB_diff hA (by fun_prop) measurable_const (by fun_prop) measurable_const
  unfold G2
  rw [lintegral_tsum (fun j => ((hmeas j).lintegral_prod_right').aemeasurable)]
  calc ∑' j : ℤ, ∫⁻ s in Ioc 0 1, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
        ENNReal.ofReal |annB (T * s + j * T - T * r) x - annB (T * s + j * T) x|
      = ∑' j : ℤ, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ∫⁻ s in Ioc 0 1, ENNReal.ofReal (fejer J r) *
        ENNReal.ofReal |annB (T * s + j * T - T * r) x - annB (T * s + j * T) x| := by
        exact tsum_congr (fun j => lintegral_lintegral_swap (hmeas j).aemeasurable)
    _ = ∑' j : ℤ, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) * ∫⁻ s in Ioc 0 1,
        ENNReal.ofReal |annB (T * s + j * T - T * r) x - annB (T * s + j * T) x| := by
        exact tsum_congr (fun j => lintegral_congr (fun r =>
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top))
    _ = ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ∑' j : ℤ, ENNReal.ofReal (fejer J r) * ∫⁻ s in Ioc 0 1,
        ENNReal.ofReal |annB (T * s + j * T - T * r) x - annB (T * s + j * T) x| := by
        rw [lintegral_tsum]
        intro j
        exact (((hF.1 J).measurable.ennreal_ofReal).mul
          ((hmeas2 j).lintegral_prod_left')).aemeasurable
    _ = ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) * (ENNReal.ofReal T⁻¹ *
        ∫⁻ σ, ENNReal.ofReal |annB (σ - T * r) x - annB σ x|) := by
        refine lintegral_congr (fun r => ?_)
        rw [ENNReal.tsum_mul_left,
          lintegral_unfold_T (fun σ => ENNReal.ofReal |annB (σ - T * r) x - annB σ x|) hT0]
    _ ≤ ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
        (ENNReal.ofReal T⁻¹ * ENNReal.ofReal (2 * min (T * |r|) (1 / (2 * x ^ 2)))) := by
        refine lintegral_mono (fun r => ?_)
        gcongr
        refine (E1_lint hA hx (T * r)).trans (ENNReal.ofReal_le_ofReal ?_)
        rw [abs_mul, abs_of_pos hT0]
        gcongr
        exact A_ell_le hA x hx

lemma G2_integral (hA : AnnulusStatement) (hF : FejerStatement) {T : ℝ} (hT1 : 1 ≤ T) (J : ℕ)
    {CF : ℝ} (hmom : ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r * √|r|) ≤
      ENNReal.ofReal (CF / √J)) (hCF : 0 ≤ CF) :
    ∫⁻ x, ∫⁻ s in Ioc 0 1, G2 T J s x ≤
      ENNReal.ofReal (T⁻¹ * (2 * π * √(2 * T)) * (CF / √J)) := by
  have hT0 : 0 < T := by linarith
  have hK : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (fejer J p.2) *
      (ENNReal.ofReal T⁻¹ * ENNReal.ofReal (2 * min (T * |p.2|) (1 / (2 * p.1 ^ 2))))) :=
    ((hF.1 J).measurable.comp measurable_snd).ennreal_ofReal.mul
      (measurable_const.mul (Measurable.ennreal_ofReal (by fun_prop)))
  calc ∫⁻ x, ∫⁻ s in Ioc 0 1, G2 T J s x
      ≤ ∫⁻ x, ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r) *
        (ENNReal.ofReal T⁻¹ * ENNReal.ofReal (2 * min (T * |r|) (1 / (2 * x ^ 2)))) :=
        lintegral_mono_ae ((Measure.ae_ne volume 0).mono fun x hx => G2_inner hA hF hT1 J hx)
    _ = ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ∫⁻ x, ENNReal.ofReal (fejer J r) *
        (ENNReal.ofReal T⁻¹ * ENNReal.ofReal (2 * min (T * |r|) (1 / (2 * x ^ 2)))) :=
        lintegral_lintegral_swap hK.aemeasurable
    _ ≤ ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (T⁻¹ * (2 * π * √(2 * T))) *
        ENNReal.ofReal (fejer J r * √|r|) := by
        refine lintegral_mono (fun r => ?_)
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have hfr := hF.2.1 J r
        calc ENNReal.ofReal (fejer J r) * (ENNReal.ofReal T⁻¹ *
              ∫⁻ x, ENNReal.ofReal (2 * min (T * |r|) (1 / (2 * x ^ 2))))
            ≤ ENNReal.ofReal (fejer J r) * (ENNReal.ofReal T⁻¹ *
              ENNReal.ofReal (2 * (π * √(2 * (T * |r|))))) := by
              gcongr
              have : ∀ x : ℝ, ENNReal.ofReal (2 * min (T * |r|) (1 / (2 * x ^ 2))) =
                  ENNReal.ofReal 2 * ENNReal.ofReal (min (T * |r|) (1 / (2 * x ^ 2))) :=
                fun x => ENNReal.ofReal_mul (by norm_num)
              simp_rw [this]
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ENNReal.ofReal_mul (by norm_num)]
              gcongr
              exact lint_min_inv_sq (by positivity)
          _ = ENNReal.ofReal (T⁻¹ * (2 * π * √(2 * T))) * ENNReal.ofReal (fejer J r * √|r|) := by
              rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hfr,
                ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              rw [show 2 * (T * |r|) = (2 * T) * |r| by ring, Real.sqrt_mul (by positivity)]
              ring
    _ = ENNReal.ofReal (T⁻¹ * (2 * π * √(2 * T))) *
        ∫⁻ r in Ioc (-(1/2):ℝ) (1/2), ENNReal.ofReal (fejer J r * √|r|) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (T⁻¹ * (2 * π * √(2 * T))) * ENNReal.ofReal (CF / √J) := by gcongr
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

lemma step4_ineq {L a T σ : ℝ} (hL : 0 ≤ L) (ha : 0 ≤ a) (hT : 0 < T) :
    (min 1 (L * exp σ / T ^ 2) + a) * (2 * exp (-|σ|)) ≤
      2 * max L 1 * min (T ^ 2)⁻¹ (exp (-|σ|)) + 2 * a * min 1 (exp (-|σ|)) := by
  have he : exp (-|σ|) ≤ 1 := exp_le_one_iff.mpr (by linarith [abs_nonneg σ])
  rw [min_eq_right he]
  have key : min 1 (L * exp σ / T ^ 2) * exp (-|σ|) ≤ max L 1 * min (T ^ 2)⁻¹ (exp (-|σ|)) := by
    rw [mul_min_of_nonneg _ _ (by positivity : (0:ℝ) ≤ max L 1)]
    apply le_min
    · calc min 1 (L * exp σ / T ^ 2) * exp (-|σ|) ≤ (L * exp σ / T ^ 2) * exp (-|σ|) := by
            gcongr; exact min_le_right _ _
        _ = L * (exp σ * exp (-|σ|)) / T ^ 2 := by ring
        _ ≤ L * 1 / T ^ 2 := by
            gcongr; rw [← exp_add]; exact exp_le_one_iff.mpr (by linarith [le_abs_self σ])
        _ ≤ max L 1 * (T ^ 2)⁻¹ := by
            rw [mul_one, div_eq_mul_inv]; gcongr; exact le_max_left _ _
    · calc min 1 (L * exp σ / T ^ 2) * exp (-|σ|) ≤ 1 * exp (-|σ|) := by
            gcongr; exact min_le_left _ _
        _ ≤ max L 1 * exp (-|σ|) := by gcongr; exact le_max_right _ _
  nlinarith [key, exp_pos (-|σ|)]

lemma G3_integral (hρ : IsBump ρ) (hA : AnnulusStatement) {T : ℝ} (hT1 : 1 ≤ T) {L : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ u, 1 - psiF ρ u ≤ L * |u|) :
    ∫⁻ x, ∫⁻ s in Ioc 0 1, G3 ρ T s x ≤
      ENNReal.ofReal (T⁻¹ * (2 * max L 1 * (2 * (T ^ 2)⁻¹ * (Real.log ((T ^ 2)⁻¹)⁻¹ + 1)) +
        2 * aT ρ T * (2 * 1 * (Real.log (1:ℝ)⁻¹ + 1)))) := by
  have hT0 : 0 < T := by linarith
  have ha : 0 ≤ aT ρ T := by unfold aT; have := rho_zero_pos hρ; positivity
  set c : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal |psiF ρ (x / T ^ 2) / (1 + aT ρ T) - 1| with hc
  have hcm : Measurable c := (continuous_abs.comp ((((psi_cont hρ).comp
    (continuous_id.div_const _)).div_const _).sub continuous_const)).measurable.ennreal_ofReal
  have step1 : ∀ x, ∫⁻ s in Ioc 0 1, G3 ρ T s x =
      ENNReal.ofReal T⁻¹ * ∫⁻ σ, c x * ENNReal.ofReal (annB σ x) := by
    intro x
    unfold G3
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_tsum (fun j => ((measurable_annB_comp hA (by fun_prop)
        measurable_const).ennreal_ofReal).aemeasurable),
      lintegral_unfold_T (fun σ => ENNReal.ofReal (annB σ x)) hT0,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    ring
  have step3 : ∀ σ, ∫⁻ x, c x * ENNReal.ofReal (annB σ x) ≤
      ENNReal.ofReal (min 1 (L * exp σ / T ^ 2) + aT ρ T) *
        ENNReal.ofReal (2 * exp (-|σ|)) := by
    intro σ
    calc ∫⁻ x, c x * ENNReal.ofReal (annB σ x)
        ≤ ∫⁻ x, ENNReal.ofReal (min 1 (L * exp σ / T ^ 2) + aT ρ T) *
            ENNReal.ofReal (annB σ x) := by
          refine lintegral_mono (fun x => ?_)
          rcases annB_eq_zero_or_one σ x with h0 | h1
          · rw [h0]; simp
          · gcongr
            have hx : |x| ≤ exp σ := annB_support (by rw [h1]; norm_num)
            refine ENNReal.ofReal_le_ofReal
              (kappa_bound (psi_nonneg hρ _) (psi_le_one hρ _) ha ((hL _).trans ?_))
            rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < T ^ 2), mul_div_assoc']
            gcongr
      _ = ENNReal.ofReal (min 1 (L * exp σ / T ^ 2) + aT ρ T) *
            ∫⁻ x, ENNReal.ofReal (annB σ x) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr; exact slice_lint hA σ
  have hm2 : Measurable (fun p : ℝ × ℝ => c p.1 * ENNReal.ofReal (annB p.2 p.1)) :=
    (hcm.comp measurable_fst).mul
      (measurable_annB_comp hA measurable_snd measurable_fst).ennreal_ofReal
  simp_rw [step1]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_lintegral_swap hm2.aemeasurable]
  have hmexp : Measurable (fun σ : ℝ => ENNReal.ofReal (min (T ^ 2)⁻¹ (exp (-|σ|)))) :=
    Measurable.ennreal_ofReal (by fun_prop)
  calc ENNReal.ofReal T⁻¹ * ∫⁻ σ, ∫⁻ x, c x * ENNReal.ofReal (annB σ x)
      ≤ ENNReal.ofReal T⁻¹ * ∫⁻ σ, (ENNReal.ofReal (2 * max L 1) *
          ENNReal.ofReal (min (T ^ 2)⁻¹ (exp (-|σ|))) +
          ENNReal.ofReal (2 * aT ρ T) * ENNReal.ofReal (min 1 (exp (-|σ|)))) := by
        gcongr with σ
        refine (step3 σ).trans ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have := step4_ineq (σ := σ) hL0 ha hT0
        linarith
    _ = ENNReal.ofReal T⁻¹ * (ENNReal.ofReal (2 * max L 1) *
          (∫⁻ σ, ENNReal.ofReal (min (T ^ 2)⁻¹ (exp (-|σ|)))) +
          ENNReal.ofReal (2 * aT ρ T) * ∫⁻ σ, ENNReal.ofReal (min 1 (exp (-|σ|)))) := by
        rw [lintegral_add_left (hmexp.const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal T⁻¹ * (ENNReal.ofReal (2 * max L 1) *
          ENNReal.ofReal (2 * (T ^ 2)⁻¹ * (Real.log ((T ^ 2)⁻¹)⁻¹ + 1)) +
          ENNReal.ofReal (2 * aT ρ T) * ENNReal.ofReal (2 * 1 * (Real.log (1:ℝ)⁻¹ + 1))) := by
        have i1 := lint_min_exp (h := (T ^ 2)⁻¹) (by positivity) (inv_le_one_of_one_le₀ (by nlinarith))
        have i2 := lint_min_exp (h := (1:ℝ)) one_pos le_rfl
        gcongr
    _ = _ := by
        have hl : 0 ≤ Real.log ((T ^ 2)⁻¹)⁻¹ := by
          rw [inv_inv]; exact Real.log_nonneg (by nlinarith)
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by simp; positivity),
          ← ENNReal.ofReal_mul (by positivity)]

/-! ### Assembly -/

lemma meas_slice {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (fun p : ℝ × ℝ => f p.1 p.2)) (x : ℝ) :
    Measurable (fun s => f s x) := hf.comp (measurable_id.prodMk measurable_const)

lemma meas_lint_slice {f : ℝ → ℝ → ℝ≥0∞} (hf : Measurable (fun p : ℝ × ℝ => f p.1 p.2))
    (μ : Measure ℝ) [SFinite μ] : Measurable (fun x => ∫⁻ s, f s x ∂μ) :=
  hf.lintegral_prod_left'

lemma lint_add3 {μ : Measure ℝ} {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ s, (f s + g s + h s) ∂μ = (∫⁻ s, f s ∂μ) + (∫⁻ s, g s ∂μ) + ∫⁻ s, h s ∂μ := by
  have hfg : Measurable (fun s => f s + g s) := hf.add hg
  rw [lintegral_add_left hfg, lintegral_add_left hf]

lemma final_arith {ρ : ℝ → ℝ} {T CF L : ℝ} {J : ℕ} (hT3 : 3 ≤ T) (hJ : T ^ 8 ≤ J)
    (hCF : 0 < CF) (hρ0 : 0 < ρ 0) :
    T⁻¹ * (4 * (2 * hT T * (Real.log (hT T)⁻¹ + 1))) +
      T⁻¹ * (2 * π * √(2 * T)) * (CF / √J) +
      T⁻¹ * (2 * max L 1 * (2 * (T ^ 2)⁻¹ * (Real.log ((T ^ 2)⁻¹)⁻¹ + 1)) +
        2 * aT ρ T * (2 * 1 * (Real.log (1:ℝ)⁻¹ + 1))) ≤
    (24 + 4 * π * CF + 12 * max L 1 + 768 * ρ 0) * Real.log T / T ^ 3 := by
  have hT0 : 0 < T := by linarith
  have hlogT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  have hl2 : Real.log ((T ^ 2)⁻¹)⁻¹ = 2 * Real.log T := by
    rw [inv_inv, Real.log_pow]; push_cast; ring
  have hM : 1 ≤ max L 1 := le_max_right _ _
  have hT3' : 0 < T ^ 3 := by positivity
  have hBa : T⁻¹ * (4 * (2 * hT T * (Real.log (hT T)⁻¹ + 1))) ≤ 24 * Real.log T / T ^ 3 := by
    unfold hT
    rw [hl2]
    have e : T⁻¹ * (4 * (2 * (T ^ 2)⁻¹ * (2 * Real.log T + 1))) =
        8 * (2 * Real.log T + 1) / T ^ 3 := by ring
    rw [e]
    exact (div_le_div_iff_of_pos_right hT3').mpr (by linarith)
  have hBb : T⁻¹ * (2 * π * √(2 * T)) * (CF / √J) ≤ 4 * π * CF * Real.log T / T ^ 3 := by
    have hsq1 : √(2 * T) ≤ 2 * T := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
    have hsq2 : T ^ 4 ≤ √J := by
      have h : √((T ^ 4) ^ 2) = T ^ 4 := Real.sqrt_sq (by positivity)
      calc T ^ 4 = √((T ^ 4) ^ 2) := h.symm
        _ ≤ √J := Real.sqrt_le_sqrt (by rw [← pow_mul]; exact hJ)
    have hT4 : 0 < T ^ 4 := by positivity
    calc T⁻¹ * (2 * π * √(2 * T)) * (CF / √J)
        ≤ T⁻¹ * (2 * π * (2 * T)) * (CF / T ^ 4) := by gcongr
      _ = 4 * π * CF / T ^ 4 := by field_simp; ring
      _ ≤ 4 * π * CF * Real.log T / T ^ 3 := by
        rw [div_le_div_iff₀ hT4 hT3']
        have h1 : T ^ 3 ≤ Real.log T * T ^ 4 := by
          have : T ^ 3 ≤ T ^ 4 := pow_le_pow_right₀ (by linarith) (by norm_num)
          nlinarith
        have hk : 0 ≤ 4 * π * CF := by positivity
        have := mul_le_mul_of_nonneg_left h1 hk
        linarith
  have hBc : T⁻¹ * (2 * max L 1 * (2 * (T ^ 2)⁻¹ * (Real.log ((T ^ 2)⁻¹)⁻¹ + 1)) +
        2 * aT ρ T * (2 * 1 * (Real.log (1:ℝ)⁻¹ + 1))) ≤
      12 * max L 1 * Real.log T / T ^ 3 + 768 * ρ 0 * Real.log T / T ^ 3 := by
    rw [hl2, show Real.log (1:ℝ)⁻¹ = 0 by simp]
    have e : T⁻¹ * (2 * max L 1 * (2 * (T ^ 2)⁻¹ * (2 * Real.log T + 1)) +
        2 * aT ρ T * (2 * 1 * (0 + 1))) =
        4 * max L 1 * (2 * Real.log T + 1) / T ^ 3 + 4 * aT ρ T / T := by ring
    rw [e]
    have h1 : 4 * max L 1 * (2 * Real.log T + 1) / T ^ 3 ≤ 12 * max L 1 * Real.log T / T ^ 3 := by
      refine (div_le_div_iff_of_pos_right hT3').mpr ?_
      nlinarith
    have h2 : 4 * aT ρ T / T ≤ 768 * ρ 0 * Real.log T / T ^ 3 := by
      unfold aT
      rw [div_le_div_iff₀ hT0 hT3']
      have hexp : T ^ 4 ≤ 24 * Real.exp T := by
        have := Real.pow_div_factorial_le_exp T hT0.le 4
        norm_num [Nat.factorial] at this
        linarith
      have hu : T ^ 4 * Real.exp (-T) ≤ 24 := by
        have := mul_le_mul_of_nonneg_right hexp (Real.exp_pos (-T)).le
        rwa [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at this
      have ha := mul_le_mul_of_nonneg_left hu (by positivity : (0:ℝ) ≤ 32 * ρ 0 * T)
      have hb := mul_le_mul_of_nonneg_left hlogT (by positivity : (0:ℝ) ≤ 768 * ρ 0 * T)
      nlinarith
    linarith
  have e : (24 + 4 * π * CF + 12 * max L 1 + 768 * ρ 0) * Real.log T / T ^ 3 =
      24 * Real.log T / T ^ 3 + 4 * π * CF * Real.log T / T ^ 3 +
      (12 * max L 1 * Real.log T / T ^ 3 + 768 * ρ 0 * Real.log T / T ^ 3) := by ring
  rw [e]
  linarith

lemma Wsum_cont (ρ : ℝ → ℝ) (T : ℝ) (J : ℕ) (x : ℝ) : Continuous (fun s => Wsum ρ T J s x) := by
  unfold Wsum
  exact continuous_finsetSum _ (fun l _ => continuous_const.mul
    (continuous_ee.comp (continuous_const.mul continuous_id)))

end ChowlaOpus.VarAux

namespace ChowlaOpus

open VarAux in
theorem varStatement_holds (hA : AnnulusStatement) (hF : FejerStatement)
    (hW : WrepStatement) (hWb : WboundStatement) : VarStatement := by
  intro ρ hρ
  obtain ⟨L, hL0, hL⟩ := psi_lip hρ
  obtain ⟨CF, hCF, hmom⟩ := fejer_moment_lint hF
  have hρ0 := rho_zero_pos hρ
  refine ⟨24 + 4 * π * CF + 12 * max L 1 + 768 * ρ 0, 3, by positivity, ?_⟩
  intro T hT3 J hJ
  have hT1 : 1 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hJ1 : 1 ≤ J := by
    have : (1:ℝ) ≤ J := le_trans (one_le_pow₀ hT1) hJ
    exact_mod_cast this
  set Fx := fun x => (bL ρ T J 0 x).re -
    ∑ l ∈ Finset.Icc (-(J:ℤ)) J, ‖bL ρ T J l x‖ ^ 2 with hFx
  have hFeq : ∀ x, Fx x =
      ∫ s in (0:ℝ)..1, (Wsum ρ T J s x).re * (1 - (Wsum ρ T J s x).re) := fun x =>
    (parseval J (fun l => bL ρ T J l x) (fun s => (hWb ρ hρ T hT1 J s x).1)).symm
  have hF0 : ∀ x, 0 ≤ Fx x := by
    intro x; rw [hFeq x]
    refine intervalIntegral.integral_nonneg zero_le_one (fun s _ => ?_)
    obtain ⟨-, h0, h1⟩ := hWb ρ hρ T hT1 J s x
    exact mul_nonneg h0 (by linarith)
  set Ba := T⁻¹ * (4 * (2 * hT T * (Real.log (hT T)⁻¹ + 1))) with hBa
  set Bb := T⁻¹ * (2 * π * √(2 * T)) * (CF / √J) with hBb
  set Bc := T⁻¹ * (2 * max L 1 * (2 * (T ^ 2)⁻¹ * (Real.log ((T ^ 2)⁻¹)⁻¹ + 1)) +
        2 * aT ρ T * (2 * 1 * (Real.log (1:ℝ)⁻¹ + 1))) with hBc
  have hlogT : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hT0]
    linarith [Real.exp_one_lt_d9]
  have hl2 : Real.log (hT T)⁻¹ = 2 * Real.log T := by
    unfold hT; rw [inv_inv, Real.log_pow]; push_cast; ring
  have hlog0 : 0 ≤ Real.log T := by linarith
  have hBa0 : 0 ≤ Ba := by rw [hBa, hl2]; have := hT_pos hT0; positivity
  have hBb0 : 0 ≤ Bb := by positivity
  have ha : 0 ≤ aT ρ T := by unfold aT; positivity
  have hBc0 : 0 ≤ Bc := by
    rw [hBc]
    have : Real.log ((T ^ 2)⁻¹)⁻¹ = 2 * Real.log T := hl2
    rw [this]; simp only [inv_one, Real.log_one, zero_add]; positivity
  have hlint : ∫⁻ x, ENNReal.ofReal (Fx x) ≤ ENNReal.ofReal (Ba + Bb + Bc) := by
    have hm1 := G1_meas hρ hA hF T J
    have hm2 := G2_meas hA hF T J
    have hm3 := G3_meas hρ hA T
    calc ∫⁻ x, ENNReal.ofReal (Fx x)
        ≤ ∫⁻ x, ∫⁻ s in Ioc 0 1, (G1 ρ T J s x + G2 T J s x + G3 ρ T s x) := by
          refine lintegral_mono_ae ((Measure.ae_ne volume 0).mono (fun x hx => ?_))
          have hc : Continuous (fun s => (Wsum ρ T J s x).re * (1 - (Wsum ρ T J s x).re)) :=
            (Complex.continuous_re.comp (Wsum_cont ρ T J x)).mul
              (continuous_const.sub (Complex.continuous_re.comp (Wsum_cont ρ T J x)))
          rw [hFeq x, intervalIntegral.integral_of_le zero_le_one,
            ofReal_integral_eq_lintegral_ofReal (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
              (ae_of_all _ (fun s => ?_))]
          · exact lintegral_mono (fun s => pointwise hρ hA hF hW hWb hT1 J hx s)
          · obtain ⟨-, h0, h1⟩ := hWb ρ hρ T hT1 J s x
            exact mul_nonneg h0 (by linarith)
      _ = ∫⁻ x, ((∫⁻ s in Ioc 0 1, G1 ρ T J s x) + (∫⁻ s in Ioc 0 1, G2 T J s x) +
            ∫⁻ s in Ioc 0 1, G3 ρ T s x) :=
          lintegral_congr (fun x => lint_add3 (meas_slice hm1 x) (meas_slice hm2 x))
      _ = (∫⁻ x, ∫⁻ s in Ioc 0 1, G1 ρ T J s x) + (∫⁻ x, ∫⁻ s in Ioc 0 1, G2 T J s x) +
            ∫⁻ x, ∫⁻ s in Ioc 0 1, G3 ρ T s x :=
          lint_add3 (meas_lint_slice hm1 _) (meas_lint_slice hm2 _)
      _ ≤ ENNReal.ofReal Ba + ENNReal.ofReal Bb + ENNReal.ofReal Bc :=
          add_le_add (add_le_add (G1_integral hρ hA hF hT1 J)
            (G2_integral hA hF hT1 J (hmom J hJ1) hCF.le)) (G3_integral hρ hA hT1 hL0 hL)
      _ = ENNReal.ofReal (Ba + Bb + Bc) := by
          rw [ENNReal.ofReal_add (by positivity) hBc0, ENNReal.ofReal_add hBa0 hBb0]
  have hbound : Ba + Bb + Bc ≤ (24 + 4 * π * CF + 12 * max L 1 + 768 * ρ 0) *
      Real.log T / T ^ 3 := final_arith hT3 hJ hCF hρ0
  by_cases hi : Integrable Fx
  · have h1 := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hF0)
    rw [← h1] at hlint
    have h2 : ∫ x, Fx x ≤ Ba + Bb + Bc :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hlint
    exact h2.trans hbound
  · rw [integral_undef hi]
    have : 0 < Real.log T := by linarith
    positivity

end ChowlaOpus
