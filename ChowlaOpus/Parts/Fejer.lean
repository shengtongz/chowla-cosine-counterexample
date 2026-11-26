module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.FejerAux

lemma fejer_complex (R : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * ee (k * t) = fejer R t := by
  apply Complex.ext
  · rw [Complex.re_sum, Complex.ofReal_re]
    unfold fejer
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_ofReal_mul, ee_re]
    ring_nf
  · rw [Complex.im_sum, Complex.ofReal_im]
    refine Finset.sum_involution (fun k _ => -k) ?_ ?_ ?_ ?_
    · intro k _
      simp only [Complex.im_ofReal_mul, ee_im, fejerCoeff_neg, Int.cast_neg]
      rw [show 2 * π * (-(k : ℝ) * t) = -(2 * π * (k * t)) by ring, Real.sin_neg]
      ring
    · intro k _ hk h
      apply hk
      have : k = 0 := by omega
      subst this
      simp [ee_im]
    · intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      omega
    · intro k _
      simp

lemma fiber_card (R : ℕ) (k : ℤ) (hk : k ∈ Finset.Icc (-(R : ℤ)) R) :
    ((Finset.range (R + 1) ×ˢ Finset.range (R + 1)).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = k)).card = R + 1 - k.natAbs := by
  rw [Finset.mem_Icc] at hk
  have himg : (Finset.range (R + 1) ×ˢ Finset.range (R + 1)).filter
      (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2 = k) =
      (Finset.range (R + 1 - k.natAbs)).image (fun i => (i + k.toNat, i + (-k).toNat)) := by
    ext ⟨j, j'⟩
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_image,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨hj, hj'⟩, h⟩
      refine ⟨j - k.toNat, ?_, ?_, ?_⟩ <;> omega
    · rintro ⟨i, hi, rfl, rfl⟩
      omega
  rw [himg, Finset.card_image_of_injective, Finset.card_range]
  intro i i' h
  simp only [Prod.mk.injEq] at h
  omega

lemma sum_sub_eq (R : ℕ) (g : ℤ → ℂ) :
    ∑ p ∈ Finset.range (R + 1) ×ˢ Finset.range (R + 1), g ((p.1 : ℤ) - p.2) =
      ∑ k ∈ Finset.Icc (-(R : ℤ)) R, ((R + 1 - k.natAbs : ℕ) : ℂ) * g k := by
  rw [← Finset.sum_fiberwise_of_maps_to' (t := Finset.Icc (-(R : ℤ)) R)
    (g := fun p : ℕ × ℕ => (p.1 : ℤ) - p.2)]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_const, fiber_card R k hk, nsmul_eq_mul]
  · rintro ⟨j, j'⟩ h
    simp only [Finset.mem_product, Finset.mem_range] at h
    simp only [Finset.mem_Icc]
    omega

/-- The Dirichlet-type sum `∑_{j=0}^{R} e(j t)`. -/
noncomputable def dir (R : ℕ) (t : ℝ) : ℂ := ∑ j ∈ Finset.range (R + 1), ee (j * t)

lemma natCast_mul_fejerCoeff (R : ℕ) (k : ℤ) (hk : k ∈ Finset.Icc (-(R : ℤ)) R) :
    ((R : ℝ) + 1) * fejerCoeff R k = ((R + 1 - k.natAbs : ℕ) : ℝ) := by
  rw [Finset.mem_Icc] at hk
  have habs : |(k : ℝ)| ≤ R := by
    rw [← Int.cast_abs]; exact_mod_cast abs_le.mpr hk
  have hpos : (0 : ℝ) < R + 1 := by positivity
  have h1 : 0 ≤ 1 - |(k : ℝ)| / ((R : ℝ) + 1) := by
    rw [sub_nonneg, div_le_one hpos]; linarith
  unfold fejerCoeff
  rw [max_eq_right h1, Nat.cast_sub (by omega), Nat.cast_natAbs, Int.cast_abs]
  field_simp
  push_cast
  ring

lemma dir_mul_conj (R : ℕ) (t : ℝ) :
    dir R t * starRingEnd ℂ (dir R t) =
      ((R : ℂ) + 1) * ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * ee (k * t) := by
  unfold dir
  rw [map_sum, Finset.sum_mul_sum, ← Finset.sum_product']
  have : ∀ p : ℕ × ℕ, ee (p.1 * t) * starRingEnd ℂ (ee (p.2 * t)) =
      (fun k : ℤ => ee (k * t)) ((p.1 : ℤ) - p.2) := by
    intro p
    rw [← ee_neg, ← ee_add]
    congr 1
    push_cast; ring
  rw [Finset.sum_congr rfl (fun p _ => this p), sum_sub_eq R (fun k : ℤ => ee (k * t)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← mul_assoc]
  congr 1
  exact_mod_cast (natCast_mul_fejerCoeff R k hk).symm

lemma fejer_eq_normSq (R : ℕ) (t : ℝ) : ((R : ℝ) + 1) * fejer R t = ‖dir R t‖ ^ 2 := by
  have h := dir_mul_conj R t
  rw [fejer_complex R t, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h.symm

lemma fejer_nonneg (R : ℕ) (t : ℝ) : 0 ≤ fejer R t := by
  have h := fejer_eq_normSq R t
  have hpos : (0 : ℝ) < R + 1 := by positivity
  have : 0 ≤ ((R : ℝ) + 1) * fejer R t := by rw [h]; positivity
  nlinarith

lemma norm_dir_le (R : ℕ) (t : ℝ) : ‖dir R t‖ ≤ R + 1 := by
  unfold dir
  refine (norm_sum_le _ _).trans ?_
  simp [norm_ee]

lemma fejer_le (R : ℕ) (t : ℝ) : fejer R t ≤ R + 1 := by
  have h := fejer_eq_normSq R t
  have hpos : (0 : ℝ) < R + 1 := by positivity
  have h1 := norm_dir_le R t
  have h2 : ‖dir R t‖ ^ 2 ≤ ((R : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith

lemma dir_eq_geom (R : ℕ) (t : ℝ) : dir R t = ∑ j ∈ Finset.range (R + 1), ee t ^ j := by
  unfold dir
  refine Finset.sum_congr rfl fun j _ => ?_
  have := ee_mul_intCast t (j : ℤ)
  rw [zpow_natCast] at this
  rw [← this]
  congr 1
  push_cast; ring

lemma norm_ee_sub_one_sq (t : ℝ) : ‖ee t - 1‖ ^ 2 = 4 * Real.sin (π * t) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ee_re, ee_im,
    Complex.one_re, Complex.one_im]
  have hc : Real.cos (2 * π * t) = 2 * Real.cos (π * t) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have hs : Real.sin (2 * π * t) = 2 * Real.sin (π * t) * Real.cos (π * t) := by
    rw [← Real.sin_two_mul]; ring_nf
  rw [hc, hs]
  linear_combination (4 * (Real.cos (π * t) ^ 2 - 1)) * Real.sin_sq_add_cos_sq (π * t)

lemma sixteen_sq_le (t : ℝ) (ht : |t| ≤ 1 / 2) : 16 * t ^ 2 ≤ ‖ee t - 1‖ ^ 2 := by
  rw [norm_ee_sub_one_sq]
  have h1 : 2 / π * (π * |t|) ≤ Real.sin (π * |t|) :=
    Real.mul_le_sin (by positivity) (by nlinarith [Real.pi_pos])
  have h2 : 2 / π * (π * |t|) = 2 * |t| := by field_simp
  rw [h2] at h1
  have h3 : Real.sin (π * |t|) ^ 2 = Real.sin (π * t) ^ 2 := by
    rcases abs_choice t with h | h <;> rw [h]
    rw [mul_neg, Real.sin_neg, neg_sq]
  have h4 : (2 * |t|) ^ 2 ≤ Real.sin (π * |t|) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  rw [← h3]
  have : (2 * |t|) ^ 2 = 4 * t ^ 2 := by rw [mul_pow, sq_abs]; ring
  linarith

lemma fejer_le_inv (R : ℕ) (t : ℝ) (ht0 : t ≠ 0) (ht : |t| ≤ 1 / 2) :
    fejer R t ≤ 1 / (4 * ((R : ℝ) + 1) * t ^ 2) := by
  have h := fejer_eq_normSq R t
  have hpos : (0 : ℝ) < R + 1 := by positivity
  have hgeom : dir R t * (ee t - 1) = ee t ^ (R + 1) - 1 := by
    rw [dir_eq_geom, geom_sum_mul]
  have hnum : ‖ee t ^ (R + 1) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_ee]; norm_num
  have hprod : ‖dir R t‖ ^ 2 * ‖ee t - 1‖ ^ 2 ≤ 4 := by
    rw [← mul_pow, ← norm_mul, hgeom]
    have := pow_le_pow_left₀ (norm_nonneg _) hnum 2
    linarith
  have h16 := sixteen_sq_le t ht
  have ht2 : 0 < t ^ 2 := by positivity
  have hD : ‖dir R t‖ ^ 2 * (16 * t ^ 2) ≤ 4 :=
    (mul_le_mul_of_nonneg_left h16 (by positivity)).trans hprod
  rw [le_div_iff₀ (by positivity)]
  nlinarith

lemma fejer_continuous (R : ℕ) : Continuous (fejer R) := by
  unfold fejer
  fun_prop

lemma fejer_even (R : ℕ) (t : ℝ) : fejer R (-t) = fejer R t := by
  simp only [fejer]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show 2 * π * (k : ℝ) * (-t) = -(2 * π * k * t) by ring, Real.cos_neg]

lemma moment_half (R : ℕ) (hR : 1 ≤ R) :
    ∫ t in (0 : ℝ)..(1 / 2), fejer R t * √|t| ≤ 3 / (2 * √((R : ℝ) + 1)) := by
  set N : ℝ := (R : ℝ) + 1 with hN
  have hN2 : 2 ≤ N := by
    have : (1 : ℝ) ≤ R := by exact_mod_cast hR
    linarith
  have hNpos : 0 < N := by linarith
  set δ : ℝ := 1 / N with hδ
  have hδpos : 0 < δ := by positivity
  have hδle : δ ≤ 1 / 2 := by
    rw [hδ, div_le_div_iff₀ hNpos (by norm_num)]; linarith
  have hδN : δ * N = 1 := by rw [hδ]; field_simp
  have hsN : 0 < √N := Real.sqrt_pos.mpr hNpos
  have hsq : √N * √N = N := Real.mul_self_sqrt hNpos.le
  have hsδ : √δ = 1 / √N := by
    rw [hδ, Real.sqrt_div' _ hNpos.le, Real.sqrt_one]
  have hcont : Continuous (fun t => fejer R t * √|t|) := by
    have := fejer_continuous R
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := δ)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have h1 : ∫ t in (0 : ℝ)..δ, fejer R t * √|t| ≤ √δ := by
    calc ∫ t in (0 : ℝ)..δ, fejer R t * √|t| ≤ ∫ t in (0 : ℝ)..δ, N * √δ := by
          refine intervalIntegral.integral_mono_on hδpos.le (hcont.intervalIntegrable _ _)
            intervalIntegrable_const ?_
          intro t ht
          have hs : √|t| ≤ √δ := Real.sqrt_le_sqrt (by rw [abs_of_nonneg ht.1]; exact ht.2)
          exact mul_le_mul (fejer_le R t) hs (Real.sqrt_nonneg _) hNpos.le
      _ = √δ := by
          rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, ← mul_assoc, hδN, one_mul]
  have h0 : (0 : ℝ) ∉ Set.uIcc δ (1 / 2) := by
    rw [Set.uIcc_of_le hδle]
    intro h
    exact absurd h.1 (not_le.mpr hδpos)
  have h2 : ∫ t in δ..(1 / 2), fejer R t * √|t| ≤
      ∫ t in δ..(1 / 2), (1 / (4 * N)) * t ^ (-(3 / 2 : ℝ)) := by
    refine intervalIntegral.integral_mono_on hδle (hcont.intervalIntegrable _ _)
      ((intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul _) ?_
    intro t ht
    have htpos : 0 < t := hδpos.trans_le ht.1
    have hb := fejer_le_inv R t htpos.ne' (by rw [abs_of_pos htpos]; exact ht.2)
    rw [abs_of_pos htpos]
    have hrw : t ^ (-(3 / 2 : ℝ)) = √t / t ^ 2 := by
      rw [show (-(3 / 2 : ℝ)) = 1 / 2 - 2 by norm_num, Real.rpow_sub htpos, Real.sqrt_eq_rpow,
        Real.rpow_two]
    rw [hrw]
    calc fejer R t * √t ≤ 1 / (4 * N * t ^ 2) * √t :=
          mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _)
      _ = 1 / (4 * N) * (√t / t ^ 2) := by field_simp
  have h3 : ∫ t in δ..(1 / 2), (1 / (4 * N)) * t ^ (-(3 / 2 : ℝ)) ≤ 1 / (2 * √N) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
    have e1 : (-(3 / 2 : ℝ)) + 1 = -(1 / 2) := by norm_num
    have e2 : δ ^ (-(1 / 2 : ℝ)) = √N := by
      rw [Real.rpow_neg hδpos.le, ← Real.sqrt_eq_rpow, hsδ, one_div, inv_inv]
    have e3 : 0 < (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
    rw [e1, e2]
    calc 1 / (4 * N) * (((1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)) - √N) / -(1 / 2))
        = 1 / (4 * N) * (2 * (√N - (1 / 2 : ℝ) ^ (-(1 / 2 : ℝ)))) := by ring
      _ ≤ 1 / (4 * N) * (2 * √N) := by gcongr; linarith
      _ = 1 / (2 * √N) := by
          have h4N : 4 * N = (2 * √N) * (2 * √N) := by linear_combination (-4) * hsq
          rw [h4N]
          field_simp
  have h4 : √δ + 1 / (2 * √N) = 3 / (2 * √N) := by rw [hsδ]; field_simp; ring
  linarith

lemma moment (R : ℕ) (hR : 1 ≤ R) :
    ∫ t in (-(1 / 2) : ℝ)..(1 / 2), fejer R t * √|t| ≤ 3 / √R := by
  have hcont : Continuous (fun t => fejer R t * √|t|) := by
    have := fejer_continuous R
    fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hneg : ∫ t in (-(1 / 2) : ℝ)..0, fejer R t * √|t| =
      ∫ t in (0 : ℝ)..(1 / 2), fejer R t * √|t| := by
    have := intervalIntegral.integral_comp_neg (a := -(1 / 2 : ℝ)) (b := 0)
      (fun t => fejer R t * √|t|)
    simp only [fejer_even, abs_neg, neg_zero, neg_neg] at this
    exact this
  rw [hneg]
  have h := moment_half R hR
  have hR' : (0 : ℝ) < R := by exact_mod_cast hR
  have hsR : 0 < √(R : ℝ) := Real.sqrt_pos.mpr hR'
  have hle : √(R : ℝ) ≤ √((R : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  calc _ ≤ 3 / (2 * √((R : ℝ) + 1)) + 3 / (2 * √((R : ℝ) + 1)) := by linarith
    _ = 3 / √((R : ℝ) + 1) := by field_simp; ring
    _ ≤ 3 / √R := by gcongr

lemma fejer_periodic (R : ℕ) (t : ℝ) : fejer R (t + 1) = fejer R t := by
  simp only [fejer]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : 2 * π * (k : ℝ) * (t + 1) = 2 * π * k * t + (k : ℤ) * (2 * π) := by ring
  rw [this, Real.cos_add_int_mul_two_pi]

lemma integral_cos_int (k : ℤ) :
    ∫ t in (0 : ℝ)..1, Real.cos (2 * π * k * t) = if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hc : (2 * π * k : ℝ) ≠ 0 := by
      have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
    have : 2 * π * (k : ℝ) * 1 = ((2 * k : ℤ) : ℝ) * π := by push_cast; ring
    rw [this, Real.sin_int_mul_pi]
    simp

lemma fejer_integral (R : ℕ) : ∫ t in (0 : ℝ)..1, fejer R t = 1 := by
  unfold fejer
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_cos_int]
    simp [fejerCoeff_zero]
  · intro k _
    exact (by fun_prop : Continuous fun t => fejerCoeff R k * Real.cos (2 * π * k * t)
      ).intervalIntegrable _ _

end ChowlaOpus.FejerAux

namespace ChowlaOpus

open FejerAux in
theorem fejerStatement_holds : FejerStatement :=
  ⟨fejer_continuous, fejer_nonneg, fejer_periodic, fejer_even, fejer_integral, fejer_complex,
    ⟨3, by norm_num, moment⟩⟩

end ChowlaOpus
