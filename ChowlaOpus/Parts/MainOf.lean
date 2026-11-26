module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.MainOfAux

/-- The asymptotic conditions on `T` used in the assembly. -/
lemma exists_T₀ (C c K ε : ℝ) (hC : 0 < C) (hc : 0 < c) (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      C * Real.log T / T ^ 2 ≤ c ∧ 4 ≤ C * T * Real.log T ∧
      2 * K ^ 2 * Real.log T ^ 2 < ε ^ 2 * c * T := by
  have h1 : ∀ᶠ T in Filter.atTop,
      2 * K ^ 2 * (Real.log T ^ 2 / (1 * T + 0)) < ε ^ 2 * c := by
    have := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).const_mul (2 * K ^ 2)
    rw [mul_zero] at this
    exact this.eventually_lt_const (by positivity)
  have h2 : ∀ᶠ T in Filter.atTop, max (max (Real.exp 1) (4 / C)) (max (C / c) 1) ≤ T :=
    Filter.eventually_ge_atTop _
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 (h1.and h2)
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨hA, hB⟩ := hT₀ T hT
  have he : Real.exp 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have h4 : 4 / C ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hCc : C / c ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hT1 : 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  have hTpos : 0 < T := by linarith
  have hL1 : 1 ≤ Real.log T := (Real.le_log_iff_exp_le hTpos).2 he
  have hLT : Real.log T ≤ T := (Real.log_le_sub_one_of_pos hTpos).trans (by linarith)
  refine ⟨?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have h : C ≤ T * c := (div_le_iff₀ hc).1 hCc
    have h' : C * Real.log T ≤ C * T := mul_le_mul_of_nonneg_left hLT hC.le
    have h'' : C * T ≤ T * c * T := mul_le_mul_of_nonneg_right h hTpos.le
    linarith
  · have h : 4 ≤ T * C := (div_le_iff₀ hC).1 h4
    have h' : C * T * 1 ≤ C * T * Real.log T :=
      mul_le_mul_of_nonneg_left hL1 (by positivity)
    linarith
  · simp only [one_mul, add_zero] at hA
    rw [mul_div_assoc', div_lt_iff₀ hTpos] at hA
    linarith

end ChowlaOpus.MainOfAux

namespace ChowlaOpus

theorem cosine_counterexample_of (hW : WeightsStatement) (hR : RoundingStatement)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ A : Finset ℕ+, N ≤ A.card ∧ ∀ t : ℝ, -ε * Real.sqrt (A.card : ℝ) < cosineSum A t := by
  obtain ⟨C, c, hC, hc, hW⟩ := hW
  obtain ⟨CR, hCR, hR⟩ := hR
  set C₁ : ℝ := CR * Real.sqrt (6 * C) with hC₁
  have hC₁pos : 0 < C₁ := by positivity
  set K : ℝ := C + C₁ with hK
  have hKpos : 0 < K := by positivity
  obtain ⟨T₀, hT₀⟩ := MainOfAux.exists_T₀ C c K ε hC hc hε
  obtain ⟨T, hTT₀, hT3, hWT⟩ := hW T₀
  obtain ⟨hi, hii, hiii⟩ := hT₀ T hTT₀
  set L := Real.log T with hL
  have hTpos : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  obtain ⟨p, Nw, w, hp, hNw1, hNw, hw01, hlow, hmass, hvar⟩ :=
    hWT (⌈2 * C₁ * L / c + 2 * T * N / c⌉₊ + 1)
  have hpR : 2 * C₁ * L / c + 2 * T * N / c + 1 ≤ (p : ℝ) := by
    have h1 := Nat.le_ceil (2 * C₁ * L / c + 2 * T * N / c)
    have h2 : ((⌈2 * C₁ * L / c + 2 * T * N / c⌉₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hp
    push_cast at h2
    linarith
  have hA1 : 0 ≤ 2 * C₁ * L / c := by positivity
  have hA2 : 0 ≤ 2 * T * N / c := by positivity
  have hp1 : (1 : ℝ) ≤ p := by linarith
  have hppos : (0 : ℝ) < p := by linarith
  have hpC₁ : 2 * C₁ * L ≤ c * p := by
    have : 2 * C₁ * L / c ≤ p := by linarith
    rw [div_le_iff₀ hc] at this; linarith
  have hpN : 2 * T * N ≤ c * p := by
    have : 2 * T * N / c ≤ p := by linarith
    rw [div_le_iff₀ hc] at this; linarith
  set S : ℝ := C * p ^ 2 * L / T ^ 3 with hS
  have hSpos : 0 < S := by positivity
  have hsumw_le : ∑ d ∈ Finset.Icc 1 Nw, w d ≤ Nw := by
    calc ∑ d ∈ Finset.Icc 1 Nw, w d ≤ ∑ _d ∈ Finset.Icc 1 Nw, (1 : ℝ) :=
          Finset.sum_le_sum fun d _ => (hw01 d).2
      _ = Nw := by simp
  have hS_le_mass : S ≤ c * p ^ 2 / T := by
    have hi' : C * L ≤ c * T ^ 2 := (div_le_iff₀ (by positivity)).1 hi
    rw [hS, div_le_div_iff₀ (by positivity) hTpos]
    have : C * L * (p ^ 2 * T) ≤ c * T ^ 2 * (p ^ 2 * T) :=
      mul_le_mul_of_nonneg_right hi' (by positivity)
    linarith
  have hSN : S ≤ Nw := by linarith
  obtain ⟨a, ha01, hround⟩ := hR Nw w S hNw1 hw01 hSpos hSN hvar
  -- the rounding error
  have hlog : Real.log (2 * Nw / S) ≤ 6 * L := by
    have hNwpos : (1 : ℝ) ≤ Nw := by exact_mod_cast hNw1
    have hpos : 0 < 2 * (Nw : ℝ) / S := by positivity
    have hle : 2 * (Nw : ℝ) / S ≤ T ^ 6 := by
      rw [div_le_iff₀ hSpos]
      have h6 : T ^ 6 * S = C * T * L * (p ^ 2 * T ^ 2) := by
        rw [hS]; field_simp
      rw [h6]
      have h4 : 4 * (p ^ 2 * T ^ 2) ≤ C * T * L * (p ^ 2 * T ^ 2) :=
        mul_le_mul_of_nonneg_right hii (by positivity)
      linarith
    calc Real.log (2 * Nw / S) ≤ Real.log (T ^ 6) := Real.log_le_log hpos hle
      _ = 6 * L := by rw [Real.log_pow, ← hL]; norm_num
  have hX : S * Real.log (2 * Nw / S) ≤ (Real.sqrt (6 * C) * p * L / T) ^ 2 := by
    have h1 : S * Real.log (2 * Nw / S) ≤ S * (6 * L) := mul_le_mul_of_nonneg_left hlog hSpos.le
    have h2 : (Real.sqrt (6 * C) * p * L / T) ^ 2 = 6 * C * p ^ 2 * L ^ 2 / T ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    have h3 : S * (6 * L) = 6 * C * p ^ 2 * L ^ 2 / T ^ 3 := by
      rw [hS]; ring
    have h4 : 6 * C * p ^ 2 * L ^ 2 / T ^ 3 ≤ 6 * C * p ^ 2 * L ^ 2 / T ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_right₀ hT1 (by norm_num))
    linarith
  have herr : CR * Real.sqrt (S * Real.log (2 * Nw / S)) ≤ C₁ * p * L / T := by
    have h := Real.sqrt_le_sqrt hX
    rw [Real.sqrt_sq (by positivity)] at h
    calc CR * Real.sqrt (S * Real.log (2 * Nw / S))
        ≤ CR * (Real.sqrt (6 * C) * p * L / T) := mul_le_mul_of_nonneg_left h hCR.le
      _ = C₁ * p * L / T := by rw [hC₁]; ring
  have hdiff : ∀ t : ℝ,
      |(∑ d ∈ Finset.Icc 1 Nw, a d * Real.cos (2 * Real.pi * d * t)) -
        ∑ d ∈ Finset.Icc 1 Nw, w d * Real.cos (2 * Real.pi * d * t)| ≤ C₁ * p * L / T := by
    intro t
    rw [← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    exact (hround t).trans herr
  -- the set `A`
  set F := (Finset.Icc 1 Nw).filter (fun d => a d = 1) with hF
  set A : Finset ℕ+ := F.image Nat.toPNat' with hA
  have hFpos : ∀ d ∈ F, 0 < d := by
    intro d hd
    rw [hF, Finset.mem_filter, Finset.mem_Icc] at hd
    omega
  have hinj : Set.InjOn Nat.toPNat' (F : Set ℕ) := by
    intro x hx y hy hxy
    have hx1 := hFpos x hx
    have hy1 := hFpos y hy
    have h := congrArg (fun z : ℕ+ => (z : ℕ)) hxy
    simpa [Nat.toPNat'_coe, hx1, hy1] using h
  have hcos : ∀ t : ℝ,
      cosineSum A t = ∑ d ∈ Finset.Icc 1 Nw, a d * Real.cos (2 * Real.pi * d * t) := by
    intro t
    unfold cosineSum
    rw [hA, Finset.sum_image hinj, hF, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    have hd1 : 0 < d := by rw [Finset.mem_Icc] at hd; omega
    have hd' : ((Nat.toPNat' d : ℕ+) : ℕ) = d := by rw [Nat.toPNat'_coe]; simp [hd1]
    rw [hd']
    rcases ha01 d with h | h <;> simp [h]
  have hcard : (A.card : ℝ) = ∑ d ∈ Finset.Icc 1 Nw, a d := by
    have h := hcos 0
    simp only [mul_zero, Real.cos_zero, mul_one] at h
    rw [← h]
    simp [cosineSum]
  have hbig : C₁ * p * L / T ≤ c * p ^ 2 / (2 * T) := by
    rw [div_le_div_iff₀ hTpos (by positivity)]
    have : 2 * C₁ * L * (p * T) ≤ c * p * (p * T) :=
      mul_le_mul_of_nonneg_right hpC₁ (by positivity)
    linarith
  have hcardM : c * p ^ 2 / (2 * T) ≤ A.card := by
    have h0 := hdiff 0
    simp only [mul_zero, Real.cos_zero, mul_one] at h0
    have h1 := (abs_le.1 h0).1
    have h2 : c * p ^ 2 / T = 2 * (c * p ^ 2 / (2 * T)) := by field_simp
    rw [hcard]
    linarith
  have hMN : (N : ℝ) ≤ c * p ^ 2 / (2 * T) := by
    rw [le_div_iff₀ (by positivity)]
    have : 2 * T * N * 1 ≤ c * p * p := mul_le_mul hpN hp1 (by norm_num) (by positivity)
    linarith
  refine ⟨A, ?_, ?_⟩
  · exact_mod_cast hMN.trans hcardM
  · intro t
    rw [hcos t]
    have h1 := (abs_le.1 (hdiff t)).1
    have h2 := hlow t
    have hsq : K * p * L / T < ε * Real.sqrt (A.card : ℝ) := by
      have hx : 0 ≤ K * p * L / T / ε := by positivity
      have hlt : (K * p * L / T / ε) ^ 2 < (A.card : ℝ) := by
        refine lt_of_lt_of_le ?_ hcardM
        rw [div_pow, div_pow, mul_pow, mul_pow, div_div,
          div_lt_div_iff₀ (by positivity) (by positivity)]
        have hp2 : 0 < (p : ℝ) ^ 2 * T := by positivity
        have := mul_lt_mul_of_pos_left hiii hp2
        linarith
      have h := (Real.lt_sqrt hx).2 hlt
      rw [div_lt_iff₀ hε] at h
      linarith
    have hKsplit : K * p * L / T = C * p * L / T + C₁ * p * L / T := by rw [hK]; ring
    linarith

end ChowlaOpus
