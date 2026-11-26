module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

namespace AnnulusAux

open Set Filter Topology

lemma item2 (σ x : ℝ) : 0 ≤ annB σ x ∧ annB σ x ≤ 1 := by
  unfold annB; split_ifs <;> norm_num

/-- `L x = log (1 + x⁻²)`, twice the label mean. -/
noncomputable def L (x : ℝ) : ℝ := Real.log (1 + (x ^ 2)⁻¹)

lemma annB_meas (σ : ℝ) : Measurable (annB σ) := by
  unfold annB
  refine Measurable.ite ?_ measurable_const measurable_const
  rw [Set.ofPred_and]
  exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) (by fun_prop))

lemma int_ind_one {s : Set ℝ} (hs : MeasurableSet s) (h : volume s ≠ ⊤) :
    Integrable (s.indicator (1 : ℝ → ℝ)) :=
  (integrable_indicator_iff hs).2 (integrableOn_const h)

/-- For `x ≠ 0`, `σ ↦ annB σ x` is the indicator of `[log |x|, log (1 + x²) / 2]`. -/
lemma annB_sigma {x : ℝ} (hx : x ≠ 0) (σ : ℝ) :
    annB σ x = (Icc (Real.log |x|) (Real.log (1 + x ^ 2) / 2)).indicator 1 σ := by
  have hax : 0 < |x| := abs_pos.2 hx
  have h1 : |x| ≤ Real.exp σ ↔ Real.log |x| ≤ σ := (Real.log_le_iff_le_exp hax).symm
  have h2 : Real.exp σ ^ 2 ≤ 1 + x ^ 2 ↔ σ ≤ Real.log (1 + x ^ 2) / 2 := by
    rw [← Real.exp_nat_mul, le_div_iff₀ (by norm_num : (0:ℝ) < 2),
      Real.le_log_iff_exp_le (by positivity)]
    norm_num [mul_comm]
  unfold annB
  by_cases h : |x| ≤ Real.exp σ ∧ Real.exp σ ^ 2 ≤ 1 + x ^ 2
  · rw [ite_eq_left h, indicator_of_mem]
    · rfl
    · exact ⟨h1.1 h.1, h2.1 h.2⟩
  · rw [ite_eq_right h, indicator_of_notMem]
    rintro ⟨h3, h4⟩
    exact h ⟨h1.2 h3, h2.2 h4⟩

lemma annB_zero (σ : ℝ) : annB σ 0 = (Iic 0).indicator 1 σ := by
  unfold annB
  have : Real.exp σ ^ 2 ≤ 1 + 0 ^ 2 ↔ σ ≤ 0 := by
    rw [← Real.exp_nat_mul]; simp only [Nat.cast_ofNat, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero, Real.exp_le_one_iff]
    constructor <;> intro <;> linarith
  by_cases h : σ ≤ 0
  · rw [ite_eq_left ⟨by simp [(Real.exp_pos σ).le], this.2 h⟩, indicator_of_mem (by exact h)]
    rfl
  · rw [ite_eq_right (fun h' => h (this.1 h'.2)), indicator_of_notMem (by exact h)]

lemma ellF_zero : ellF 0 = 0 := by
  unfold ellF
  apply integral_undef
  simp_rw [annB_zero]
  rw [integrable_indicator_iff measurableSet_Iic]
  intro h
  have := (integrableOn_const_iff (C := (1:ℝ)) (s := Iic (0:ℝ)) (μ := volume)).1 h
  simp [Real.volume_Iic] at this

lemma L_eq {x : ℝ} (hx : x ≠ 0) :
    L x = Real.log (1 + x ^ 2) - 2 * Real.log |x| := by
  unfold L
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  rw [show 1 + (x ^ 2)⁻¹ = (1 + x ^ 2) / x ^ 2 by field_simp; ring,
    Real.log_div (by positivity) hx2, Real.log_pow, Real.log_abs]
  push_cast; ring

lemma ellF_eq (x : ℝ) : ellF x = L x / 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ellF_zero, L]
  unfold ellF
  simp_rw [annB_sigma hx]
  have hle : Real.log |x| ≤ Real.log (1 + x ^ 2) / 2 := by
    have h2 : Real.log (|x| ^ 2) = 2 * Real.log |x| := by rw [Real.log_pow]; norm_num
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2), mul_comm, ← h2, sq_abs]
    exact Real.log_le_log (by positivity) (by linarith)
  rw [integral_indicator_one measurableSet_Icc, Real.volume_real_Icc_of_le hle, L_eq hx]
  ring

lemma item4 (x : ℝ) (hx : x ≠ 0) : Integrable (fun σ => annB σ x) := by
  simp_rw [annB_sigma hx]
  exact int_ind_one measurableSet_Icc measure_Icc_lt_top.ne

lemma item5 (x : ℝ) (_hx : x ≠ 0) : ellF x = Real.log (1 + (x ^ 2)⁻¹) / 2 := ellF_eq x

lemma item6 (x : ℝ) : 0 ≤ ellF x := integral_nonneg (fun σ => (item2 σ x).1)

lemma item7 (x : ℝ) (hx : x ≠ 0) : ellF x ≤ 1 / (2 * x ^ 2) := by
  rw [ellF_eq, L]
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + (x ^ 2)⁻¹ by positivity)
  rw [one_div, mul_inv, div_eq_mul_inv]
  nlinarith [show (0:ℝ) ≤ (x ^ 2)⁻¹ by positivity]

/-- The `x`-slice of the annulus: `[-r, r] \ (-s, s)` with `r = e^σ`, `s = √(r² - 1)`. -/
lemma annB_x (σ x : ℝ) : annB σ x =
    (Icc (-Real.exp σ) (Real.exp σ)).indicator 1 x -
      (Ioo (-Real.sqrt (Real.exp σ ^ 2 - 1)) (Real.sqrt (Real.exp σ ^ 2 - 1))).indicator 1 x := by
  set r := Real.exp σ with hr
  set s := Real.sqrt (r ^ 2 - 1) with hs
  have hsr : s < r := (Real.sqrt_lt' (Real.exp_pos σ)).2 (by linarith)
  have key : r ^ 2 ≤ 1 + x ^ 2 ↔ s ≤ |x| := by
    rw [hs, Real.sqrt_le_left (abs_nonneg x), sq_abs]; constructor <;> intro <;> linarith
  unfold annB
  rw [← hr]
  by_cases h1 : |x| ≤ r
  · rw [indicator_of_mem (show x ∈ Icc (-r) r from abs_le.1 h1)]
    by_cases h2 : r ^ 2 ≤ 1 + x ^ 2
    · rw [ite_eq_left ⟨h1, h2⟩, indicator_of_notMem]
      · simp
      · intro h; have := abs_lt.2 h; linarith [key.1 h2]
    · rw [ite_eq_right (fun h => h2 h.2), indicator_of_mem]
      · simp
      · exact abs_lt.1 (lt_of_not_ge (fun h => h2 (key.2 h)))
  · rw [ite_eq_right (fun h => h1 h.1), indicator_of_notMem (fun h => h1 (abs_le.2 h)),
      indicator_of_notMem]
    · simp
    · intro h; have := abs_lt.2 h; linarith

lemma annB_integrable (σ : ℝ) : Integrable (annB σ) := by
  have : annB σ = fun x => (Icc (-Real.exp σ) (Real.exp σ)).indicator 1 x -
      (Ioo (-Real.sqrt (Real.exp σ ^ 2 - 1)) (Real.sqrt (Real.exp σ ^ 2 - 1))).indicator 1 x :=
    funext (annB_x σ)
  rw [this]
  exact (int_ind_one measurableSet_Icc measure_Icc_lt_top.ne).sub
    (int_ind_one measurableSet_Ioo measure_Ioo_lt_top.ne)

lemma item10 (σ : ℝ) : Integrable (annB σ) ∧ ∫ x, annB σ x ≤ 2 * Real.exp (-|σ|) := by
  refine ⟨annB_integrable σ, ?_⟩
  simp_rw [annB_x σ]
  set r := Real.exp σ with hr
  set s := Real.sqrt (r ^ 2 - 1) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hr0 : 0 < r := Real.exp_pos σ
  rw [integral_sub (int_ind_one measurableSet_Icc measure_Icc_lt_top.ne)
      (int_ind_one measurableSet_Ioo measure_Ioo_lt_top.ne),
    integral_indicator_one measurableSet_Icc, integral_indicator_one measurableSet_Ioo,
    Real.volume_real_Icc_of_le (by linarith), Real.volume_real_Ioo_of_le (by linarith)]
  rcases le_or_gt σ 0 with hσ | hσ
  · rw [abs_of_nonpos hσ, neg_neg, ← hr]; linarith
  · rw [abs_of_pos hσ, Real.exp_neg, ← hr]
    have hr1 : 1 < r := by rw [hr]; exact Real.one_lt_exp_iff.2 hσ
    have hss : s ^ 2 = r ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
    have hsr : s ≤ r := by nlinarith
    rw [show r - -r - (s - -s) = 2 * (r - s) by ring]
    have : r - s ≤ 1 / r :=
      (le_div_iff₀ hr0).2 (by nlinarith [mul_nonneg hs0 (sub_nonneg.2 hsr)])
    rw [one_div] at this
    linarith

/-- Pointwise bound for translating an interval indicator. -/
lemma shift_pt (I : Set ℝ) (a b δ : ℝ) (hδ : 0 ≤ δ) (h1 : Ioo a b ⊆ I) (h2 : I ⊆ Icc a b)
    (t : ℝ) : |I.indicator (1 : ℝ → ℝ) (t - δ) - I.indicator 1 t| ≤
      (Icc a (a + δ)).indicator (1 : ℝ → ℝ) t + (Icc b (b + δ)).indicator 1 t := by
  have hA : 0 ≤ (Icc a (a + δ)).indicator (1 : ℝ → ℝ) t :=
    indicator_nonneg (fun _ _ => zero_le_one) _
  have hB : 0 ≤ (Icc b (b + δ)).indicator (1 : ℝ → ℝ) t :=
    indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases ht1 : t - δ ∈ I <;> by_cases ht2 : t ∈ I
  · rw [indicator_of_mem ht1, indicator_of_mem ht2]
    simp only [Pi.one_apply, sub_self, abs_zero]; linarith
  · rw [indicator_of_mem ht1, indicator_of_notMem ht2]
    simp only [Pi.one_apply, sub_zero, abs_one]
    have h4 := h2 ht1
    have h3 : ¬ (a < t ∧ t < b) := fun h => ht2 (h1 h)
    by_cases htb : b ≤ t
    · rw [indicator_of_mem (show t ∈ Icc b (b + δ) from ⟨htb, by linarith [h4.2]⟩)]
      simp only [Pi.one_apply]; linarith
    · have : t ≤ a := by
        by_contra h; exact h3 ⟨lt_of_not_ge h, lt_of_not_ge htb⟩
      rw [indicator_of_mem (show t ∈ Icc a (a + δ) from ⟨by linarith [h4.1], by linarith⟩)]
      simp only [Pi.one_apply]; linarith
  · rw [indicator_of_notMem ht1, indicator_of_mem ht2]
    simp only [Pi.one_apply, zero_sub, abs_neg, abs_one]
    have h4 := h2 ht2
    have h3 : ¬ (a < t - δ ∧ t - δ < b) := fun h => ht1 (h1 h)
    by_cases hta : t - δ ≤ a
    · rw [indicator_of_mem (show t ∈ Icc a (a + δ) from ⟨h4.1, by linarith⟩)]
      simp only [Pi.one_apply]; linarith
    · have : b ≤ t - δ := by
        by_contra h; exact h3 ⟨lt_of_not_ge hta, lt_of_not_ge h⟩
      rw [indicator_of_mem (show t ∈ Icc b (b + δ) from ⟨by linarith, by linarith [h4.2]⟩)]
      simp only [Pi.one_apply]; linarith
  · rw [indicator_of_notMem ht1, indicator_of_notMem ht2]
    simp only [sub_self, abs_zero]; linarith

lemma shift_int (I : Set ℝ) (a b δ : ℝ) (hI : MeasurableSet I) (h1 : Ioo a b ⊆ I)
    (h2 : I ⊆ Icc a b) :
    ∫ t, |I.indicator (1 : ℝ → ℝ) (t - δ) - I.indicator 1 t| ≤ 2 * |δ| := by
  have hg : Integrable (I.indicator (1 : ℝ → ℝ)) :=
    int_ind_one hI (ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono h2))
  have key : ∀ δ : ℝ, 0 ≤ δ →
      ∫ t, |I.indicator (1 : ℝ → ℝ) (t - δ) - I.indicator 1 t| ≤ 2 * δ := by
    intro δ hδ
    calc ∫ t, |I.indicator (1 : ℝ → ℝ) (t - δ) - I.indicator 1 t|
        ≤ ∫ t, ((Icc a (a + δ)).indicator (1 : ℝ → ℝ) t + (Icc b (b + δ)).indicator 1 t) :=
          integral_mono ((hg.comp_sub_right δ).sub hg).abs
            ((int_ind_one measurableSet_Icc measure_Icc_lt_top.ne).add
              (int_ind_one measurableSet_Icc measure_Icc_lt_top.ne))
            (fun t => shift_pt I a b δ hδ h1 h2 t)
      _ = 2 * δ := by
          rw [integral_add (int_ind_one measurableSet_Icc measure_Icc_lt_top.ne)
              (int_ind_one measurableSet_Icc measure_Icc_lt_top.ne),
            integral_indicator_one measurableSet_Icc, integral_indicator_one measurableSet_Icc,
            Real.volume_real_Icc_of_le (by linarith), Real.volume_real_Icc_of_le (by linarith)]
          ring
  rcases le_total 0 δ with hδ | hδ
  · rw [abs_of_nonneg hδ]; exact key δ hδ
  · rw [abs_of_nonpos hδ]
    have : ∫ t, |I.indicator (1 : ℝ → ℝ) (t - δ) - I.indicator 1 t| =
        ∫ t, |I.indicator (1 : ℝ → ℝ) (t - -δ) - I.indicator 1 t| := by
      rw [← integral_add_right_eq_self
        (fun t => |I.indicator (1 : ℝ → ℝ) (t - δ) - I.indicator 1 t|) δ]
      congr 1; ext t
      simp only [add_sub_cancel_right, sub_neg_eq_add]
      rw [abs_sub_comm]
    rw [this]; exact key (-δ) (by linarith)

lemma abs_sub_le_add_of_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) : |p - q| ≤ p + q :=
  abs_le.2 ⟨by linarith, by linarith⟩

lemma item11 (x δ : ℝ) (hx : x ≠ 0) :
    ∫ σ, |annB (σ - δ) x - annB σ x| ≤ 2 * min |δ| (ellF x) := by
  have hint := item4 x hx
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
  apply le_min
  · simp_rw [annB_sigma hx]
    exact shift_int _ _ _ δ measurableSet_Icc Ioo_subset_Icc_self subset_rfl
  · calc ∫ σ, |annB (σ - δ) x - annB σ x|
        ≤ ∫ σ, (annB (σ - δ) x + annB σ x) :=
          integral_mono ((hint.comp_sub_right δ).sub hint).abs
            ((hint.comp_sub_right δ).add hint)
            (fun σ => abs_sub_le_add_of_nonneg (item2 _ _).1 (item2 _ _).1)
      _ = 2 * ellF x := by
          rw [integral_add (hint.comp_sub_right δ) hint,
            integral_sub_right_eq_self (fun σ => annB σ x) δ]
          unfold ellF; ring

lemma item12 (σ u : ℝ) :
    ∫ x, |annB σ (x - u) - annB σ x| ≤ min (4 * |u|) (4 * Real.exp (-|σ|)) := by
  obtain ⟨hint, hle⟩ := item10 σ
  apply le_min
  · set r := Real.exp σ with hr
    set s := Real.sqrt (r ^ 2 - 1) with hs
    have hg1 : Integrable ((Icc (-r) r).indicator (1 : ℝ → ℝ)) :=
      int_ind_one measurableSet_Icc measure_Icc_lt_top.ne
    have hg2 : Integrable ((Ioo (-s) s).indicator (1 : ℝ → ℝ)) :=
      int_ind_one measurableSet_Ioo measure_Ioo_lt_top.ne
    have hi1 : Integrable (fun x =>
        |(Icc (-r) r).indicator (1 : ℝ → ℝ) (x - u) - (Icc (-r) r).indicator 1 x|) :=
      ((hg1.comp_sub_right u).sub hg1).abs
    have hi2 : Integrable (fun x =>
        |(Ioo (-s) s).indicator (1 : ℝ → ℝ) (x - u) - (Ioo (-s) s).indicator 1 x|) :=
      ((hg2.comp_sub_right u).sub hg2).abs
    calc ∫ x, |annB σ (x - u) - annB σ x|
        ≤ ∫ x, (|(Icc (-r) r).indicator (1 : ℝ → ℝ) (x - u) - (Icc (-r) r).indicator 1 x| +
            |(Ioo (-s) s).indicator (1 : ℝ → ℝ) (x - u) - (Ioo (-s) s).indicator 1 x|) := by
          refine integral_mono ((hint.comp_sub_right u).sub hint).abs
            (hi1.add hi2)
            (fun x => ?_)
          simp only
          rw [annB_x σ (x - u), annB_x σ x, ← hr, ← hs]
          refine le_trans (le_of_eq ?_) (abs_sub _ _)
          ring_nf
      _ = (∫ x, |(Icc (-r) r).indicator (1 : ℝ → ℝ) (x - u) - (Icc (-r) r).indicator 1 x|) +
            ∫ x, |(Ioo (-s) s).indicator (1 : ℝ → ℝ) (x - u) - (Ioo (-s) s).indicator 1 x| :=
          integral_add hi1 hi2
      _ ≤ 2 * |u| + 2 * |u| :=
          add_le_add (shift_int _ _ _ u measurableSet_Icc Ioo_subset_Icc_self subset_rfl)
            (shift_int _ _ _ u measurableSet_Ioo subset_rfl Ioo_subset_Icc_self)
      _ = 4 * |u| := by ring
  · calc ∫ x, |annB σ (x - u) - annB σ x|
        ≤ ∫ x, (annB σ (x - u) + annB σ x) :=
          integral_mono ((hint.comp_sub_right u).sub hint).abs
            ((hint.comp_sub_right u).add hint)
            (fun x => abs_sub_le_add_of_nonneg (item2 _ _).1 (item2 _ _).1)
      _ = 2 * ∫ x, annB σ x := by
          rw [integral_add (hint.comp_sub_right u) hint,
            integral_sub_right_eq_self (fun x => annB σ x) u]
          ring
      _ ≤ 4 * Real.exp (-|σ|) := by linarith

/-- Integers `j` with `σ + j T` in the label interval of `x`. -/
lemma annB_shift_eq_zero {x : ℝ} (hx : x ≠ 0) {T : ℝ} (hT : 0 < T) (σ : ℝ) (j : ℤ)
    (hj : j ∉ Finset.Icc ⌈(Real.log |x| - σ) / T⌉ ⌊(Real.log (1 + x ^ 2) / 2 - σ) / T⌋) :
    annB (σ + j * T) x = 0 := by
  rw [annB_sigma hx, indicator_of_notMem]
  rintro ⟨h1, h2⟩
  apply hj
  rw [Finset.mem_Icc]
  constructor
  · exact Int.ceil_le.2 (by rw [div_le_iff₀ hT]; linarith)
  · exact Int.le_floor.2 (by rw [le_div_iff₀ hT]; linarith)

lemma item13 (T σ x : ℝ) (hT : 1 ≤ T) (hx : x ≠ 0) :
    Summable (fun j : ℤ => annB (σ + j * T) x) :=
  summable_of_ne_finset_zero (fun j hj => annB_shift_eq_zero hx (by linarith) σ j hj)


lemma L_nonneg (x : ℝ) : 0 ≤ L x :=
  Real.log_nonneg (by have : 0 ≤ (x ^ 2)⁻¹ := by positivity
                      linarith)

lemma L_abs (x : ℝ) : L |x| = L x := by simp [L, sq_abs]

/-- Antiderivative of `L` on `(0, ∞)`. -/
noncomputable def F (x : ℝ) : ℝ := x * L x + 2 * Real.arctan x

lemma mulL_eq (x : ℝ) : x * L x = x * Real.log (1 + x ^ 2) - 2 * (x * Real.log x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [L_eq hx, Real.log_abs]; ring

lemma F_cont : Continuous F := by
  have : F = fun x => x * Real.log (1 + x ^ 2) - 2 * (x * Real.log x) + 2 * Real.arctan x :=
    funext (fun x => by unfold F; rw [mulL_eq])
  rw [this]
  have h1 : Continuous (fun x : ℝ => Real.log (1 + x ^ 2)) :=
    Continuous.log (by fun_prop) (fun x => by positivity)
  exact ((continuous_id.mul h1).sub (continuous_const.mul Real.continuous_mul_log)).add
    (continuous_const.mul Real.continuous_arctan)

lemma F_deriv {x : ℝ} (hx : 0 < x) : HasDerivAt F (L x) x := by
  have hx2 : x ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun y : ℝ => (y ^ 2)⁻¹) (-(2 * x) / (x ^ 2) ^ 2) x := h1.inv hx2
  have h3 : HasDerivAt (fun y : ℝ => 1 + (y ^ 2)⁻¹) (-(2 * x) / (x ^ 2) ^ 2) x :=
    h2.const_add 1
  have h4 : HasDerivAt (fun y : ℝ => Real.log (1 + (y ^ 2)⁻¹))
      ((-(2 * x) / (x ^ 2) ^ 2) / (1 + (x ^ 2)⁻¹)) x := h3.log (by positivity)
  have h5 : HasDerivAt (fun y : ℝ => y * Real.log (1 + (y ^ 2)⁻¹))
      (1 * Real.log (1 + (x ^ 2)⁻¹) + x * ((-(2 * x) / (x ^ 2) ^ 2) / (1 + (x ^ 2)⁻¹))) x :=
    (hasDerivAt_id' x).mul h4
  have h6 : HasDerivAt (fun y => 2 * Real.arctan y) (2 * (1 / (1 + x ^ 2))) x :=
    (Real.hasDerivAt_arctan x).const_mul 2
  have h7 := h5.add h6
  unfold F L
  convert h7 using 1
  field_simp
  ring

lemma F_zero : F 0 = 0 := by simp [F, L]

lemma F_tendsto : Tendsto F atTop (𝓝 Real.pi) := by
  have h1 : Tendsto (fun x => x * L x) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_inv_atTop_zero
    · filter_upwards [eventually_gt_atTop 0] with x hx
      exact mul_nonneg hx.le (L_nonneg x)
    · filter_upwards [eventually_gt_atTop 0] with x hx
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + (x ^ 2)⁻¹ by positivity)
      unfold L
      calc x * Real.log (1 + (x ^ 2)⁻¹) ≤ x * (x ^ 2)⁻¹ := by gcongr; linarith
        _ = x⁻¹ := by field_simp
  have h2 : Tendsto (fun x => 2 * Real.arctan x) atTop (𝓝 Real.pi) := by
    have := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).const_mul 2
    convert this using 2; ring
  have := h1.add h2
  rw [zero_add] at this
  exact this

lemma L_integrableOn : IntegrableOn L (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg F_cont.continuousWithinAt (fun _ hx => F_deriv hx)
    (fun x _ => L_nonneg x) F_tendsto

lemma L_integral : ∫ x in Ioi (0:ℝ), L x = Real.pi := by
  have := integral_Ioi_of_hasDerivAt_of_nonneg (g := F) (a := 0) F_cont.continuousWithinAt
    (fun _ hx => F_deriv hx) (fun x _ => L_nonneg x) F_tendsto
  rw [this, F_zero, sub_zero]

lemma integrable_comp_abs' {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (fun x => f |x|) := by
  have hf' : IntegrableOn (fun x => f |x|) (Ioi 0) :=
    hf.congr_fun (fun x hx => by show f x = f |x|; rw [abs_of_pos (mem_Ioi.1 hx)])
      measurableSet_Ioi
  have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf'
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0:ℝ))]
  exact int_Iic.union hf'

lemma ellF_eq_abs : ellF = fun x => L |x| / 2 := funext fun x => by rw [ellF_eq, L_abs]

lemma item8 : Integrable ellF := by
  rw [ellF_eq_abs]; exact (integrable_comp_abs' L_integrableOn).div_const 2

lemma item9 : ∫ x, ellF x = Real.pi := by
  rw [ellF_eq_abs, integral_div, integral_comp_abs (f := L), L_integral]; ring

/-! ### The periodization -/

/-- Threshold `δ_T = (e^{2T} - 1)^{-1/2}`: `ℓ(x) ≥ T ⇒ |x| ≤ δ_T`. -/
noncomputable def dT (T : ℝ) : ℝ := Real.sqrt ((Real.exp (2 * T) - 1)⁻¹)

lemma perB_meas (T σ : ℝ) : Measurable (perB T σ) := by
  unfold perB
  exact Measurable.tsum (fun j => annB_meas _)

lemma ellF_eq_sub {x : ℝ} (hx : x ≠ 0) :
    ellF x = Real.log (1 + x ^ 2) / 2 - Real.log |x| := by
  rw [ellF_eq, L_eq hx]; ring

lemma mem_dT {T x : ℝ} (hT : 0 < T) (hx : x ≠ 0) (h : T ≤ ellF x) :
    x ∈ Icc (-dT T) (dT T) := by
  rw [ellF_eq, L] at h
  have h1 : Real.exp (2 * T) ≤ 1 + (x ^ 2)⁻¹ :=
    (Real.le_log_iff_exp_le (by positivity)).1 (by linarith)
  have hE : 0 < Real.exp (2 * T) - 1 := by
    have := Real.add_one_le_exp (2 * T); linarith
  have h2 : x ^ 2 ≤ (Real.exp (2 * T) - 1)⁻¹ :=
    (le_inv_comm₀ hE (by positivity)).1 (by linarith)
  exact abs_le.1 (Real.abs_le_sqrt h2)

lemma perB_bound {T σ x : ℝ} (hT : 0 < T) (hx : x ≠ 0) :
    max (perB T σ x - 1) 0 ≤ (Icc (-dT T) (dT T)).indicator (fun y => ellF y / T) x := by
  set a := Real.log |x|
  set b := Real.log (1 + x ^ 2) / 2
  set m := ⌈(a - σ) / T⌉ with hm
  set M := ⌊(b - σ) / T⌋ with hM
  have hsum : perB T σ x = ∑ j ∈ Finset.Icc m M, annB (σ + j * T) x :=
    tsum_eq_sum (fun j hj => annB_shift_eq_zero hx hT σ j hj)
  have hle : perB T σ x ≤ ((Finset.Icc m M).card : ℝ) := by
    rw [hsum]
    refine (Finset.sum_le_card_nsmul _ _ 1 (fun j _ => (item2 _ _).2)).trans ?_
    simp
  have hMm : (M : ℝ) - m ≤ ellF x / T := by
    have h1 : (M : ℝ) ≤ (b - σ) / T := Int.floor_le _
    have h2 : (a - σ) / T ≤ m := Int.le_ceil _
    rw [ellF_eq_sub hx]
    have : (b - σ) / T - (a - σ) / T = (b - a) / T := by ring
    linarith
  have hpos : 0 ≤ (Icc (-dT T) (dT T)).indicator (fun y => ellF y / T) x :=
    indicator_nonneg (fun y _ => div_nonneg (item6 y) hT.le) _
  rcases le_or_gt M m with hk | hk
  · have : (Finset.Icc m M).card ≤ 1 := by rw [Int.card_Icc]; omega
    have : ((Finset.Icc m M).card : ℝ) ≤ 1 := by exact_mod_cast this
    rw [max_eq_right (by linarith)]; exact hpos
  · have hcard : ((Finset.Icc m M).card : ℝ) = M + 1 - m := by
      have := Int.card_Icc_of_le m M (show m ≤ M + 1 by omega)
      have h' : (((Finset.Icc m M).card : ℤ) : ℝ) = ((M + 1 - m : ℤ) : ℝ) := by rw [this]
      push_cast at h'; exact h'
    have h1 : 1 ≤ ellF x / T := by
      have : (1 : ℝ) ≤ M - m := by exact_mod_cast (by omega : (1 : ℤ) ≤ M - m)
      linarith
    have hxδ : x ∈ Icc (-dT T) (dT T) :=
      mem_dT hT hx (by rwa [le_div_iff₀ hT, one_mul] at h1)
    rw [indicator_of_mem hxδ]
    exact max_le (by linarith) (div_nonneg (item6 x) hT.le)

lemma bound_integral {T : ℝ} (hT : 0 < T) :
    ∫ x, (Icc (-dT T) (dT T)).indicator (fun y => ellF y / T) x = F (dT T) / T := by
  have hδ0 : 0 ≤ dT T := Real.sqrt_nonneg _
  have : (fun x => (Icc (-dT T) (dT T)).indicator (fun y => ellF y / T) x) =
      fun x => (Iic (dT T)).indicator (fun y => L y / (2 * T)) |x| := by
    funext x
    by_cases hx : |x| ≤ dT T
    · rw [indicator_of_mem (abs_le.1 hx : x ∈ Icc (-dT T) (dT T)),
        indicator_of_mem (show |x| ∈ Iic (dT T) from hx), ellF_eq, L_abs]
      field_simp
    · rw [indicator_of_notMem (fun h => hx (abs_le.2 h)),
        indicator_of_notMem (show |x| ∉ Iic (dT T) from hx)]
  rw [this, integral_comp_abs, setIntegral_indicator measurableSet_Iic, Ioi_inter_Iic,
    ← intervalIntegral.integral_of_le hδ0, intervalIntegral.integral_div,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδ0 F_cont.continuousOn
      (fun x hx => F_deriv hx.1)
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hδ0).2
        (L_integrableOn.mono_set Ioc_subset_Ioi_self)), F_zero]
  field_simp
  ring

lemma F_dT_le {T : ℝ} (hT : 0 < T) : F (dT T) ≤ 2 * T * dT T + 2 * dT T := by
  have hδ0 : 0 ≤ dT T := Real.sqrt_nonneg _
  have hE : 0 < Real.exp (2 * T) - 1 := by
    have := Real.add_one_le_exp (2 * T); linarith
  have hL : L (dT T) = 2 * T := by
    unfold L dT
    rw [Real.sq_sqrt (inv_nonneg.2 hE.le), inv_inv, add_sub_cancel, Real.log_exp]
  unfold F
  rw [hL]
  have := Real.arctan_le_self hδ0
  nlinarith

lemma dT_le {T : ℝ} (hT : 1 ≤ T) : 4 * dT T ≤ 5 * Real.exp (-T) := by
  have hu : 2 ≤ Real.exp T := by have := Real.add_one_le_exp T; linarith
  have hE : Real.exp (2 * T) = Real.exp T ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h1 : dT T ≤ 5 / 4 * Real.exp (-T) := by
    unfold dT
    rw [Real.sqrt_le_left (by positivity), hE, Real.exp_neg]
    rw [show (5 / 4 * (Real.exp T)⁻¹) ^ 2 = 25 / (16 * Real.exp T ^ 2) by field_simp; ring,
      inv_eq_one_div, div_le_div_iff₀ (by nlinarith) (by positivity)]
    nlinarith
  linarith

lemma item14 (T σ : ℝ) (hT : 1 ≤ T) : Integrable (fun x => max (perB T σ x - 1) 0) ∧
    ∫ x, max (perB T σ x - 1) 0 ≤ 5 * Real.exp (-T) := by
  have hT0 : 0 < T := by linarith
  have hg : Integrable ((Icc (-dT T) (dT T)).indicator (fun y => ellF y / T)) :=
    (item8.div_const T).indicator measurableSet_Icc
  have hmeas : Measurable (fun x => max (perB T σ x - 1) 0) :=
    ((perB_meas T σ).sub_const 1).max measurable_const
  have hae : ∀ᵐ x ∂volume, max (perB T σ x - 1) 0 ≤
      (Icc (-dT T) (dT T)).indicator (fun y => ellF y / T) x := by
    filter_upwards [Measure.ae_ne volume 0] with x hx
    exact perB_bound hT0 hx
  refine ⟨hg.mono' hmeas.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [hae] with x hx
    rwa [Real.norm_of_nonneg (le_max_right _ _)]
  · calc ∫ x, max (perB T σ x - 1) 0
        ≤ ∫ x, (Icc (-dT T) (dT T)).indicator (fun y => ellF y / T) x :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => le_max_right _ _)) hg hae
      _ = F (dT T) / T := bound_integral hT0
      _ ≤ (2 * T * dT T + 2 * dT T) / T := by gcongr; exact F_dT_le hT0
      _ ≤ 4 * dT T := by
          rw [div_le_iff₀ hT0]
          have : 0 ≤ dT T := Real.sqrt_nonneg _
          nlinarith
      _ ≤ 5 * Real.exp (-T) := dT_le hT


/-! ### Measurability, symmetry and the label transform `β_ξ` -/

lemma item1 : Measurable (Function.uncurry annB) := by
  unfold Function.uncurry annB
  refine Measurable.ite ?_ measurable_const measurable_const
  rw [Set.ofPred_and]
  exact (measurableSet_le (by fun_prop) (by fun_prop)).inter
    (measurableSet_le (by fun_prop) (by fun_prop))

lemma item3 (σ x : ℝ) : annB σ (-x) = annB σ x := by
  simp [annB]

lemma ee_continuous : Continuous ee := by
  unfold ee; fun_prop

lemma annB_meas_swap : Measurable (fun p : ℝ × ℝ => annB p.2 p.1) := by
  have := item1.comp measurable_swap
  simp only [Function.comp_def, Function.uncurry_def, Prod.fst_swap, Prod.snd_swap] at this
  exact this

lemma item15 (ξ : ℝ) : Measurable (betaF ξ) := by
  have h2 : Measurable (fun p : ℝ × ℝ => ee (-(ξ * p.2))) :=
    (ee_continuous.comp (by fun_prop)).measurable
  have h : Measurable (fun p : ℝ × ℝ => ((annB p.2 p.1 : ℝ) : ℂ) * ee (-(ξ * p.2))) :=
    (Complex.measurable_ofReal.comp annB_meas_swap).mul h2
  have := h.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  exact this.measurable

lemma item16 (ξ x : ℝ) : ‖betaF ξ x‖ ≤ ellF x := by
  unfold betaF ellF
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1; ext σ
  rw [norm_mul, norm_ee, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (item2 σ x).1]

lemma item17 (x : ℝ) : betaF 0 x = ellF x := by
  unfold betaF ellF
  simp only [zero_mul, neg_zero, ee_zero, mul_one]
  exact integral_ofReal

lemma item18 (ξ x : ℝ) : betaF (-ξ) x = starRingEnd ℂ (betaF ξ x) := by
  unfold betaF
  rw [← integral_conj]
  congr 1; ext σ
  rw [map_mul, Complex.conj_ofReal, ← ee_neg]
  congr 2; ring

lemma item19 (ξ x : ℝ) : betaF ξ (-x) = betaF ξ x := by
  unfold betaF
  simp_rw [item3]

end AnnulusAux

open AnnulusAux in
theorem annulusStatement_holds : AnnulusStatement :=
  ⟨item1, item2, item3, item4, item5, item6, item7, item8, item9, item10, item11, item12,
    item13, item14, item15, item16, item17, item18, item19⟩

end ChowlaOpus
