module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.W9Aux

lemma exists_ee_eq {u : ℂ} (hu : ‖u‖ = 1) : ∃ z : ℝ, ee z = u := by
  refine ⟨Complex.arg u / (2 * Real.pi), ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I u
  rw [hu] at h
  simp only [Complex.ofReal_one, one_mul] at h
  rw [ee]
  convert h using 2
  push_cast
  field_simp

lemma norm_chi_eq_one {p : ℕ} (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ) (k : ℤ)
    (hk : ¬ (p : ℤ) ∣ k) : ‖χ (k : ZMod (p ^ 2))‖ = 1 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
  have hcop : IsCoprime ((p ^ 2 : ℕ) : ℤ) k := by
    push_cast
    exact ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hk).pow_left
  have hu : IsUnit (k : ZMod (p ^ 2)) := (ZMod.isUnit_intCast_iff_isCoprime k (p ^ 2)).mpr hcop
  obtain ⟨u, hu⟩ := hu
  rw [← hu, ← MulChar.coe_equivToUnitHom]
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

lemma hasCompactSupport_of_supp {f : ℝ → ℂ} {R : ℝ} (h : ∀ x, R < |x| → f x = 0) :
    HasCompactSupport f := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) (fun x hx => h x ?_)
  by_contra hc
  push Not at hc
  exact hx ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

lemma summable_b : Summable (fun n : ℕ => 1 / (1 + ((n : ℝ) + 1) ^ 2)) := by
  have h2 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    push_cast at this
    exact this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h2
  apply one_div_le_one_div_of_le (by positivity)
  linarith

lemma tsum_b_le : ∑' n : ℕ, 1 / (1 + ((n : ℝ) + 1) ^ 2) ≤ π ^ 2 / 6 - 1 / 2 := by
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 2) (π ^ 2 / 6 - 1) := by
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 2).mpr hasSum_zeta_two
    convert this using 1
    · ext n; push_cast; ring
    · simp [Finset.sum_range_succ]
  rw [summable_b.tsum_eq_zero_add]
  have hle : ∑' n : ℕ, 1 / (1 + (((n + 1 : ℕ) : ℝ) + 1) ^ 2) ≤ π ^ 2 / 6 - 1 := by
    refine (Summable.tsum_le_tsum (fun n => ?_)
      ((summable_nat_add_iff 1).mpr summable_b) hz.summable).trans hz.tsum_eq.le
    push_cast
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have h0 : (1 : ℝ) / (1 + (((0 : ℕ) : ℝ) + 1) ^ 2) = 1 / 2 := by norm_num
  rw [h0]
  linarith

lemma aux_G (f : ℝ) (hf0 : 0 ≤ f) (hf1 : f ≤ 1) :
    Summable (fun j : ℤ => 1 / (1 + ((j : ℝ) - f) ^ 2)) ∧
      ∑' j : ℤ, 1 / (1 + ((j : ℝ) - f) ^ 2) ≤ 5 := by
  have hb := summable_b
  have hb1 : Summable (fun n : ℕ => 1 / (1 + (n : ℝ) ^ 2)) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (1 + (n : ℝ) ^ 2)) 1).mp
      (by push_cast; exact hb)
  have hN1 : Summable (fun n : ℕ => 1 / (1 + ((((n + 1 : ℕ) : ℤ) : ℝ) - f) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hb1
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have hN : Summable (fun n : ℕ => 1 / (1 + ((((n : ℕ) : ℤ) : ℝ) - f) ^ 2)) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (1 + ((((n : ℕ) : ℤ) : ℝ) - f) ^ 2)) 1).mp hN1
  have hNeg : Summable (fun n : ℕ => 1 / (1 + (((-((n : ℤ) + 1) : ℤ) : ℝ) - f) ^ 2)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hb
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  refine ⟨Summable.of_nat_of_neg_add_one (f := fun j : ℤ => 1 / (1 + ((j : ℝ) - f) ^ 2)) hN hNeg, ?_⟩
  rw [tsum_of_nat_of_neg_add_one (f := fun j : ℤ => 1 / (1 + ((j : ℝ) - f) ^ 2)) hN hNeg,
    hN.tsum_eq_zero_add]
  have h0 : (1 : ℝ) / (1 + ((((0 : ℕ) : ℤ) : ℝ) - f) ^ 2) ≤ 1 := by
    apply div_le_one_of_le₀ _ (by positivity)
    nlinarith
  have h1 : ∑' n : ℕ, 1 / (1 + ((((n + 1 : ℕ) : ℤ) : ℝ) - f) ^ 2) ≤
      ∑' n : ℕ, 1 / (1 + (n : ℝ) ^ 2) := by
    refine Summable.tsum_le_tsum (fun n => ?_) hN1 hb1
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h1' : ∑' n : ℕ, 1 / (1 + (n : ℝ) ^ 2) = 1 + ∑' n : ℕ, 1 / (1 + ((n : ℝ) + 1) ^ 2) := by
    rw [hb1.tsum_eq_zero_add]
    push_cast
    norm_num
  have h2 : ∑' n : ℕ, 1 / (1 + (((-((n : ℤ) + 1) : ℤ) : ℝ) - f) ^ 2) ≤
      ∑' n : ℕ, 1 / (1 + ((n : ℝ) + 1) ^ 2) := by
    refine Summable.tsum_le_tsum (fun n => ?_) hNeg hb
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have h3 := tsum_b_le
  have hpi : π ^ 2 < 12 := by
    have := Real.pi_lt_d2
    have := Real.pi_pos
    nlinarith
  linarith

lemma sum_inv_one_add_sq (y : ℝ) :
    Summable (fun k : ℤ => 1 / (1 + ((k : ℝ) - y) ^ 2)) ∧
      ∑' k : ℤ, 1 / (1 + ((k : ℝ) - y) ^ 2) ≤ 5 := by
  obtain ⟨h1, h2⟩ := aux_G (y - ⌊y⌋) (Int.fract_nonneg y) (Int.fract_lt_one y).le
  have key : (fun k : ℤ => 1 / (1 + ((k : ℝ) - y) ^ 2)) =
      (fun j : ℤ => 1 / (1 + ((j : ℝ) - (y - ⌊y⌋)) ^ 2)) ∘ (Equiv.subRight ⌊y⌋) := by
    ext k
    simp only [Function.comp_apply, Equiv.subRight_apply, Int.cast_sub]
    ring_nf
  rw [key]
  refine ⟨(Equiv.summable_iff _).mpr h1, ?_⟩
  rw [Function.comp_def, Equiv.tsum_eq (Equiv.subRight ⌊y⌋)
    (fun j : ℤ => 1 / (1 + ((j : ℝ) - (y - ⌊y⌋)) ^ 2))]
  exact h2

/-- Lower bound for the real part of a single row of the dual sum. -/
lemma row_re_ge (hR : RowSumStatement) (hM : MultStatement) {k : ℕ} {T K : ℝ}
    {S : Finset (Fin (k + 1) → ℤ)} {cf : (Fin (k + 1) → ℤ) → ℝ → ℂ}
    (hcf : IsProfile T S cf K (T ^ 2)) (L : Fin (k + 1) → ℤ) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hLp : ∀ v ∈ S, 2 * |∑ i, L i * v i| < p)
    (hLinj : ∀ v ∈ S, ∀ w ∈ S, ∑ i, L i * v i = ∑ i, L i * w i → v = w)
    {χ : MulChar (ZMod (p ^ 2)) ℂ} (hχ : KernelChar p χ) {η : ℝ} (hη0 : 0 ≤ η)
    (hphase : ∀ v ∈ S, v ≠ 0 →
      ‖gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T)‖ ≤ η)
    (y : ℝ) (kk : ℤ) :
    -((p : ℝ) * (𝓕 (cf 0) y).re + (p : ℝ) * η * S.card * K * (1 / (1 + y ^ 2))) ≤
      (∑ v ∈ S, 𝓕 (cf v) y * rowSum p χ (∑ i, L i * v i) kk).re := by
  obtain ⟨hRa, hRb, hRc, -, -⟩ := hR p hp hp2 χ hχ
  have hK : 0 ≤ K := by
    have h1 := hcf.decay 0 0
    have h2 : 0 ≤ ‖𝓕 (cf 0) 0‖ := norm_nonneg _
    norm_num at h1
    linarith
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hF0 := hcf.fourier_b0 y
  have herr : 0 ≤ (p : ℝ) * η * S.card * K * (1 / (1 + y ^ 2)) := by positivity
  have hn0 : (∑ i, L i * (0 : Fin (k + 1) → ℤ) i) = 0 := by simp
  have hndvd : ∀ v ∈ S, v ≠ 0 → ¬ (p : ℤ) ∣ ∑ i, L i * v i := by
    intro v hv hv0 hdvd
    have hlt : |∑ i, L i * v i| < (p : ℤ) := by
      have := hLp v hv
      have := abs_nonneg (∑ i, L i * v i)
      linarith
    have h0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    exact hv0 (hLinj v hv 0 hcf.zero_mem (by rw [h0, hn0]))
  rw [← Finset.add_sum_erase S _ hcf.zero_mem, hn0]
  by_cases hk : (p : ℤ) ∣ kk
  · have hrest : ∑ v ∈ S.erase 0, 𝓕 (cf v) y * rowSum p χ (∑ i, L i * v i) kk = 0 := by
      apply Finset.sum_eq_zero
      intro v hv
      obtain ⟨hv0, hvS⟩ := Finset.mem_erase.mp hv
      rw [hRb _ kk (hndvd v hvS hv0) hk, mul_zero]
    rw [hrest, add_zero, hRc kk, ite_eq_left hk]
    obtain ⟨r, hr, hrge⟩ : ∃ r : ℝ, ((if (p : ℤ) ^ 2 ∣ kk then ((p : ℂ) ^ 2) else 0) - (p : ℂ)) =
        (r : ℂ) ∧ -(p : ℝ) ≤ r := by
      split_ifs
      · exact ⟨(p : ℝ) ^ 2 - p, by push_cast; ring, by nlinarith⟩
      · exact ⟨-(p : ℝ), by push_cast; ring, le_refl _⟩
    rw [hr, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    nlinarith [hF0.2]
  · have hR0 : rowSum p χ 0 kk = 0 := by
      rw [hRc kk, ite_eq_right hk,
        ite_eq_right (fun h => hk (dvd_trans (dvd_pow_self _ two_ne_zero) h))]
      simp
    rw [hR0, mul_zero, zero_add]
    have hχk := norm_chi_eq_one hp χ kk hk
    obtain ⟨z, hz⟩ := exists_ee_eq hχk
    obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (χ (kk : ZMod (p ^ 2)))⁻¹ := ⟨_, rfl⟩
    have hcz : c = ee (-z) := by
      rw [hc, ← hz]
      exact inv_eq_of_mul_eq_one_right (by rw [← ee_add, add_neg_cancel, ee_zero])
    have hcn : ‖c‖ = 1 := by rw [hc, norm_inv, hχk, inv_one]
    have hee : ∀ v : Fin (k + 1) → ℤ,
        ee (∑ i, (v i : ℝ) * (-z * L i)) = c ^ (∑ i, L i * v i) := by
      intro v
      rw [hcz, ← ee_mul_intCast]
      congr 1
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hpos := hcf.pos (fun i => -z * L i) y
    obtain ⟨Sp, hSp⟩ : ∃ s : ℂ, s = trigEval S
        (fun v => mult (2 * Real.pi * v 0 / T) * 𝓕 (cf v) y) (fun i => -z * L i) := ⟨_, rfl⟩
    rw [← hSp] at hpos
    have hSpeq : Sp = 𝓕 (cf 0) y + ∑ v ∈ S.erase 0,
        mult (2 * Real.pi * v 0 / T) * 𝓕 (cf v) y * c ^ (∑ i, L i * v i) := by
      rw [hSp, trigEval, ← Finset.add_sum_erase S _ hcf.zero_mem]
      congr 1
      · simp [hM.2.1, ee_zero]
      · apply Finset.sum_congr rfl
        intro v _
        rw [hee]
    obtain ⟨E, hE⟩ : ∃ e : ℂ, e = ∑ v ∈ S.erase 0, 𝓕 (cf v) y * c ^ (∑ i, L i * v i) *
        (gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T)) := ⟨_, rfl⟩
    have hrow : ∑ v ∈ S.erase 0, 𝓕 (cf v) y * rowSum p χ (∑ i, L i * v i) kk =
        (p : ℂ) * Sp - (p : ℂ) * 𝓕 (cf 0) y + (p : ℂ) * E := by
      rw [hSpeq, hE, mul_add, add_sub_cancel_left, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro v hv
      obtain ⟨hv0, hvS⟩ := Finset.mem_erase.mp hv
      rw [hRa _ kk (hndvd v hvS hv0) hk, ← hc]
      ring
    have hEnorm : ‖E‖ ≤ S.card * K * (1 / (1 + y ^ 2)) * η := by
      rw [hE]
      calc ‖∑ v ∈ S.erase 0, 𝓕 (cf v) y * c ^ (∑ i, L i * v i) *
            (gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T))‖
          ≤ ∑ v ∈ S.erase 0, ‖𝓕 (cf v) y * c ^ (∑ i, L i * v i) *
            (gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T))‖ :=
            norm_sum_le _ _
        _ ≤ ∑ v ∈ S.erase 0, K / (1 + y ^ 2) * η := by
            apply Finset.sum_le_sum
            intro v hv
            obtain ⟨hv0, hvS⟩ := Finset.mem_erase.mp hv
            rw [norm_mul, norm_mul, norm_zpow, hcn, one_zpow, mul_one]
            exact mul_le_mul (hcf.decay v y) (hphase v hvS hv0) (norm_nonneg _)
              (by positivity)
        _ = (S.erase 0).card * (K / (1 + y ^ 2) * η) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ S.card * (K / (1 + y ^ 2) * η) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact_mod_cast Finset.card_erase_le
        _ = S.card * K * (1 / (1 + y ^ 2)) * η := by ring
    rw [hrow]
    have hEre : -‖E‖ ≤ E.re := by
      have := Complex.abs_re_le_norm E
      linarith [neg_abs_le E.re]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero]
    have h1 : 0 ≤ (p : ℝ) * Sp.re := mul_nonneg hp0 hpos.2
    have h2 : (p : ℝ) * (-(S.card * K * (1 / (1 + y ^ 2)) * η)) ≤ p * E.re :=
      mul_le_mul_of_nonneg_left (by linarith) hp0
    nlinarith

/-- The real part of the Poisson sum is twice the cosine sum of the weights. -/
lemma lhs_eq {k : ℕ} {T K : ℝ} {S : Finset (Fin (k + 1) → ℤ)}
    {cf : (Fin (k + 1) → ℤ) → ℝ → ℂ}
    (hcf : IsProfile T S cf K (T ^ 2)) (L : Fin (k + 1) → ℤ) {p : ℕ} (hp : p.Prime)
    {χ : MulChar (ZMod (p ^ 2)) ℂ} (hχ : KernelChar p χ) {N : ℕ}
    (hN : (p : ℝ) ^ 2 * T ^ 2 ≤ N) (t : ℝ) {X : ℂ}
    (hX : HasSum (fun d : ℤ => ∑ v ∈ S, (if (p : ℤ) ∣ d then 0 else
          cf v ((d : ℝ) / (p : ℝ) ^ 2) * (χ (d : ZMod (p ^ 2))) ^ (∑ i, L i * v i)) *
            ee (d * t)) X) :
    X.re = 2 * ∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d * Real.cos (2 * Real.pi * d * t) := by
  obtain ⟨B, hB⟩ : ∃ B : ℤ → ℂ, B = fun d => if (p : ℤ) ∣ d then 0 else
      ∑ v ∈ S, cf v ((d : ℝ) / (p : ℝ) ^ 2) * (χ (d : ZMod (p ^ 2))) ^ (∑ i, L i * v i) :=
    ⟨_, rfl⟩
  have hX' : HasSum (fun d : ℤ => B d * ee (d * t)) X := by
    convert hX using 1
    ext d
    rw [hB]
    dsimp only
    split_ifs <;> simp [Finset.sum_mul]
  have hχneg : ∀ a : ZMod (p ^ 2), χ (-a) = χ a := fun a => by
    rw [← neg_one_mul, map_mul, hχ.1, one_mul]
  have hBneg : ∀ d, B (-d) = B d := by
    intro d
    rw [hB]
    dsimp only
    by_cases h : (p : ℤ) ∣ d
    · rw [ite_eq_left (dvd_neg.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (dvd_neg.mp h')), ite_eq_right h]
      apply Finset.sum_congr rfl
      intro v _
      simp only [Int.cast_neg, neg_div, hcf.even, hχneg]
  have hwgt : ∀ d : ℤ, wgt S cf L p χ d = (B d).re := by
    intro d
    rw [hB]
    simp only [wgt]
    split_ifs <;> simp
  have hPpos : (0 : ℝ) < (p : ℝ) ^ 2 := by
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact pow_pos this 2
  have hBzero : ∀ n : ℕ, N < n → B n = 0 := by
    intro n hn
    rw [hB]
    dsimp only
    split_ifs with h
    · rfl
    · apply Finset.sum_eq_zero
      intro v _
      rw [hcf.supp v _ ?_, zero_mul]
      have hnN : (N : ℝ) < n := by exact_mod_cast hn
      rw [Int.cast_natCast, abs_of_nonneg (by positivity), lt_div_iff₀ hPpos]
      nlinarith [sq_nonneg T]
  have h2 := hX'.nat_add_neg
  have hB0 : B 0 = 0 := by rw [hB]; simp
  have hfin : HasSum (fun n : ℕ => B n * ee (((n : ℤ) : ℝ) * t) +
      B (-(n : ℤ)) * ee (((-(n : ℤ) : ℤ) : ℝ) * t))
      (∑ n ∈ Finset.Icc 1 N, (B n * ee (((n : ℤ) : ℝ) * t) +
        B (-(n : ℤ)) * ee (((-(n : ℤ) : ℤ) : ℝ) * t))) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · have : n = 0 := by omega
      subst this
      simp [hB0]
    · rw [hBneg, hBzero n hn]
      simp
  have hXeq := h2.unique hfin
  rw [hB0, zero_mul, add_zero] at hXeq
  rw [hXeq, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [hBneg, hwgt]
  simp only [Complex.add_re, Complex.mul_re, ee_re, ee_im, Int.cast_neg, Int.cast_natCast]
  rw [show 2 * π * (n : ℝ) * t = 2 * π * ((n : ℝ) * t) by ring,
    show 2 * π * (-(n : ℝ) * t) = -(2 * π * ((n : ℝ) * t)) by ring, Real.cos_neg, Real.sin_neg]
  ring

/-- `Re ∑_j c_0(j) e(jx) ≤ ∑_j c_0(j)`. -/
lemma re_tsum_le {k : ℕ} {T K : ℝ} {S : Finset (Fin (k + 1) → ℤ)}
    {cf : (Fin (k + 1) → ℤ) → ℝ → ℂ}
    (hcf : IsProfile T S cf K (T ^ 2)) (x : ℝ)
    (hs : Summable (fun j : ℤ => cf 0 j * ee (-((j : ℝ) * x)))) :
    (∑' j : ℤ, cf 0 j * ee (-((j : ℝ) * x))).re ≤ ∑' j : ℤ, (cf 0 j).re := by
  have hfin : Summable (fun j : ℤ => (cf 0 j).re) := by
    apply summable_of_ne_finset_zero (s := Finset.Icc (-⌈T ^ 2⌉) ⌈T ^ 2⌉)
    intro j hj
    have hc := Int.le_ceil (T ^ 2)
    rw [hcf.supp 0 j ?_, Complex.zero_re]
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hj
    rcases hj with hj | hj
    · have : (j : ℝ) < -⌈T ^ 2⌉ := by exact_mod_cast hj
      exact lt_abs.mpr (Or.inr (by linarith))
    · have : (⌈T ^ 2⌉ : ℝ) < j := by exact_mod_cast hj
      exact lt_abs.mpr (Or.inl (by linarith))
  rw [Complex.re_tsum hs]
  refine Summable.tsum_le_tsum (fun j => ?_) (Complex.hasSum_re hs.hasSum).summable hfin
  rw [Complex.mul_re, (hcf.b0 j).1, zero_mul, sub_zero, ee_re]
  have := (hcf.b0 j).2
  have := Real.cos_le_one (2 * π * -((j : ℝ) * x))
  nlinarith

end ChowlaOpus.W9Aux

namespace ChowlaOpus

theorem w9Statement_holds (hR : RowSumStatement) (hP : PoissonStatement)
    (hPP : PlainPoissonStatement) (hM : MultStatement) : W9Statement := by
  intro k T K S cf hcf hT L p hp hp2 hLp hLinj χ hχ η hη0 hηK hphase N hN t
  have hK : 0 ≤ K := by
    have h1 := hcf.decay 0 0
    have h2 : 0 ≤ ‖𝓕 (cf 0) 0‖ := norm_nonneg _
    norm_num at h1
    linarith
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hcont : ∀ v, Continuous (cf v) := fun v => (hcf.smooth v).continuous
  have hcs : ∀ v, HasCompactSupport (cf v) :=
    fun v => W9Aux.hasCompactSupport_of_supp (hcf.supp v)
  have hPv := fun v => hP p hp χ (∑ i, L i * v i) (cf v) K (hcont v) (hcs v) (hcf.decay v) t
  have hLHS : HasSum (fun d : ℤ => ∑ v ∈ S, (if (p : ℤ) ∣ d then 0 else
      cf v ((d : ℝ) / (p : ℝ) ^ 2) * (χ (d : ZMod (p ^ 2))) ^ (∑ i, L i * v i)) * ee (d * t))
      (∑ v ∈ S, ∑' kk : ℤ, 𝓕 (cf v) (kk - (p : ℝ) ^ 2 * t) * rowSum p χ (∑ i, L i * v i) kk) :=
    hasSum_sum (fun v _ => (hPv v).2)
  have hRHS : HasSum (fun kk : ℤ => ∑ v ∈ S,
      𝓕 (cf v) (kk - (p : ℝ) ^ 2 * t) * rowSum p χ (∑ i, L i * v i) kk)
      (∑ v ∈ S, ∑' kk : ℤ, 𝓕 (cf v) (kk - (p : ℝ) ^ 2 * t) * rowSum p χ (∑ i, L i * v i) kk) :=
    hasSum_sum (fun v _ => (hPv v).1.hasSum)
  have hXre := W9Aux.lhs_eq hcf L hp hχ hN t hLHS
  obtain ⟨hs5, h5⟩ := W9Aux.sum_inv_one_add_sq ((p : ℝ) ^ 2 * t)
  obtain ⟨hPPs, hPPh⟩ := hPP (cf 0) K (hcont 0) (hcs 0) (hcf.decay 0) (-((p : ℝ) ^ 2 * t))
  have hF0 : HasSum (fun kk : ℤ => (𝓕 (cf 0) (kk - (p : ℝ) ^ 2 * t)).re)
      (∑' j : ℤ, cf 0 j * ee (-((j : ℝ) * -((p : ℝ) ^ 2 * t)))).re := by
    have := Complex.hasSum_re hPPh
    simpa only [← sub_eq_add_neg] using this
  have hZ := W9Aux.re_tsum_le hcf (-((p : ℝ) ^ 2 * t)) hPPs
  have hg := ((hF0.mul_left (p : ℝ)).add (hs5.hasSum.mul_left
    ((p : ℝ) * η * S.card * K))).neg
  have hle := hasSum_le (fun (kk : ℤ) => W9Aux.row_re_ge hR hM hcf L hp hp2 hLp hLinj hχ hη0 hphase
    ((kk : ℝ) - (p : ℝ) ^ 2 * t) kk) hg (Complex.hasSum_re hRHS)
  rw [hXre] at hle
  set C := ∑' j : ℤ, (cf 0 j).re
  set Z := (∑' j : ℤ, cf 0 j * ee (-((j : ℝ) * -((p : ℝ) ^ 2 * t)))).re
  set W := ∑' kk : ℤ, 1 / (1 + ((kk : ℝ) - (p : ℝ) ^ 2 * t) ^ 2)
  set F := ∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d * Real.cos (2 * Real.pi * d * t)
  have hc0 : 0 ≤ (p : ℝ) * η * S.card * K := by positivity
  have h1 : (p : ℝ) * Z ≤ p * C := mul_le_mul_of_nonneg_left hZ hp0
  have h2 : (p : ℝ) * η * S.card * K * W ≤ (p : ℝ) * η * S.card * K * 5 :=
    mul_le_mul_of_nonneg_left h5 hc0
  have h3 : (p : ℝ) * (η * (5 * K * S.card)) ≤ p * (1 / T) :=
    mul_le_mul_of_nonneg_left hηK hp0
  have h4 : (p : ℝ) * η * S.card * K * 5 = (p : ℝ) * (η * (5 * K * S.card)) := by ring
  have h6 : -((p : ℝ) / 2 * (C + 1 / T)) = -((p : ℝ) * C + p * (1 / T)) / 2 := by ring
  rw [h6]
  linarith

end ChowlaOpus
