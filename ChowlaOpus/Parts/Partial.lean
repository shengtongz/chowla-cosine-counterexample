module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

namespace PartialAux

open Finset

/-- Real sign attached to a boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

/-- Row sum of `a` against the sign vector `σ`. -/
noncomputable def rowS {v : ℕ} (a : Fin v → ℝ) (σ : Fin v → Bool) : ℝ := ∑ j, a j * sgn (σ j)

lemma sum_exp_rowS_le {v : ℕ} (a : Fin v → ℝ) (ha : ∀ j, |a j| ≤ 1) (t : ℝ) :
    ∑ σ : Fin v → Bool, Real.exp (t * rowS a σ) ≤ 2 ^ v * Real.exp (t ^ 2 * v / 2) := by
  have h1 : ∀ σ : Fin v → Bool,
      Real.exp (t * rowS a σ) = ∏ j, Real.exp (t * (a j * sgn (σ j))) := by
    intro σ
    rw [rowS, Finset.mul_sum, Real.exp_sum]
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun j (b : Bool) => Real.exp (t * (a j * sgn b)))]
  have h2 : ∀ j, ∑ b : Bool, Real.exp (t * (a j * sgn b)) ≤ 2 * Real.exp (t ^ 2 / 2) := by
    intro j
    have hc : ∑ b : Bool, Real.exp (t * (a j * sgn b)) = 2 * Real.cosh (t * a j) := by
      rw [Fintype.sum_bool]
      show Real.exp (t * (a j * 1)) + Real.exp (t * (a j * -1)) = _
      have e1 : t * (a j * 1) = t * a j := by ring
      have e2 : t * (a j * -1) = -(t * a j) := by ring
      rw [Real.cosh_eq, e1, e2]
      ring
    rw [hc]
    have hcosh := Real.cosh_le_exp_half_sq (t * a j)
    have hsq : (t * a j) ^ 2 / 2 ≤ t ^ 2 / 2 := by
      have haj : a j ^ 2 ≤ 1 := by
        have := abs_le.mp (ha j)
        nlinarith
      rw [mul_pow]
      nlinarith [sq_nonneg t]
    have := Real.exp_le_exp.mpr hsq
    linarith
  calc ∏ j, ∑ b : Bool, Real.exp (t * (a j * sgn b))
      ≤ ∏ _j : Fin v, (2 * Real.exp (t ^ 2 / 2)) :=
        Finset.prod_le_prod₀ (fun j _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
          (fun j _ => h2 j)
    _ = 2 ^ v * Real.exp (t ^ 2 * v / 2) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring

lemma sum_exp_abs_rowS_le {v : ℕ} (a : Fin v → ℝ) (ha : ∀ j, |a j| ≤ 1) (t : ℝ) :
    ∑ σ : Fin v → Bool, Real.exp (t * |rowS a σ|) ≤ 2 * 2 ^ v * Real.exp (t ^ 2 * v / 2) := by
  have h : ∀ σ, Real.exp (t * |rowS a σ|) ≤
      Real.exp (t * rowS a σ) + Real.exp ((-t) * rowS a σ) := by
    intro σ
    rcases abs_cases (rowS a σ) with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
      linarith [Real.exp_pos ((-t) * rowS a σ)]
    · rw [h1]
      have : t * -rowS a σ = -t * rowS a σ := by ring
      rw [this]
      linarith [Real.exp_pos (t * rowS a σ)]
  calc ∑ σ, Real.exp (t * |rowS a σ|)
      ≤ ∑ σ, (Real.exp (t * rowS a σ) + Real.exp ((-t) * rowS a σ)) :=
        Finset.sum_le_sum (fun σ _ => h σ)
    _ = ∑ σ, Real.exp (t * rowS a σ) + ∑ σ, Real.exp ((-t) * rowS a σ) :=
        Finset.sum_add_distrib
    _ ≤ 2 ^ v * Real.exp (t ^ 2 * v / 2) + 2 ^ v * Real.exp ((-t) ^ 2 * v / 2) :=
        add_le_add (sum_exp_rowS_le a ha t) (sum_exp_rowS_le a ha (-t))
    _ = 2 * 2 ^ v * Real.exp (t ^ 2 * v / 2) := by rw [neg_sq]; ring

lemma abs_round_le {Δ w X : ℝ} (hΔ : 0 < Δ) (hw : 0 < w) (h : w ≤ Δ ^ 2) :
    |((round (X / (2 * Δ)) : ℤ) : ℝ)| ≤ Real.exp (Δ / w * |X| - Δ ^ 2 / w) := by
  by_cases hX : |X| < Δ
  · have h0 : round (X / (2 * Δ)) = 0 := by
      rw [round_eq_zero_iff, Set.mem_Ico]
      have := abs_lt.mp hX
      constructor
      · rw [le_div_iff₀ (by positivity)]
        linarith
      · rw [div_lt_iff₀ (by positivity)]
        linarith
    rw [h0, Int.cast_zero, abs_zero]
    positivity
  · push Not at hX
    have h1 : |((round (X / (2 * Δ)) : ℤ) : ℝ)| ≤ |X| / Δ := by
      have h2 := abs_sub_round (X / (2 * Δ))
      have h3 : |((round (X / (2 * Δ)) : ℤ) : ℝ)| ≤
          |X / (2 * Δ)| + |X / (2 * Δ) - round (X / (2 * Δ))| := by
        calc |((round (X / (2 * Δ)) : ℤ) : ℝ)|
            = |X / (2 * Δ) - (X / (2 * Δ) - round (X / (2 * Δ)))| := by ring_nf
          _ ≤ _ := abs_sub _ _
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Δ)] at h3
      have h4 : 1 / 2 ≤ |X| / (2 * Δ) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      calc |((round (X / (2 * Δ)) : ℤ) : ℝ)| ≤ |X| / (2 * Δ) + 1 / 2 := by linarith
        _ ≤ |X| / (2 * Δ) + |X| / (2 * Δ) := by linarith
        _ = |X| / Δ := by field_simp; ring
    have hu : 1 ≤ |X| / Δ := by
      rw [le_div_iff₀ hΔ]
      linarith
    have hD : 1 ≤ Δ ^ 2 / w := by
      rw [le_div_iff₀ hw]
      linarith
    have heq : Δ / w * |X| - Δ ^ 2 / w = (Δ ^ 2 / w) * (|X| / Δ - 1) := by
      field_simp
    rw [heq]
    calc |((round (X / (2 * Δ)) : ℤ) : ℝ)| ≤ |X| / Δ := h1
      _ ≤ (|X| / Δ - 1) + 1 := by linarith
      _ ≤ Real.exp (|X| / Δ - 1) := Real.add_one_le_exp _
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

lemma sum_abs_round_le {v : ℕ} (hv : 0 < v) (a : Fin v → ℝ) (ha : ∀ j, |a j| ≤ 1) {Δ : ℝ}
    (hΔ : 0 < Δ) (h : (v : ℝ) ≤ Δ ^ 2) :
    ∑ σ : Fin v → Bool, |((round (rowS a σ / (2 * Δ)) : ℤ) : ℝ)| ≤
      2 * 2 ^ v * Real.exp (-(Δ ^ 2 / (2 * v))) := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have e : -(Δ ^ 2 / v) + (Δ / v) ^ 2 * v / 2 = -(Δ ^ 2 / (2 * v)) := by
    field_simp
    ring
  calc ∑ σ : Fin v → Bool, |((round (rowS a σ / (2 * Δ)) : ℤ) : ℝ)|
      ≤ ∑ σ : Fin v → Bool, Real.exp (Δ / v * |rowS a σ| - Δ ^ 2 / v) :=
        Finset.sum_le_sum (fun σ _ => abs_round_le hΔ hv' h)
    _ = Real.exp (-(Δ ^ 2 / v)) * ∑ σ : Fin v → Bool, Real.exp (Δ / v * |rowS a σ|) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (-(Δ ^ 2 / v)) * (2 * 2 ^ v * Real.exp ((Δ / v) ^ 2 * v / 2)) :=
        mul_le_mul_of_nonneg_left (sum_exp_abs_rowS_le a ha _) (Real.exp_pos _).le
    _ = 2 * 2 ^ v * Real.exp (-(Δ ^ 2 / v) + (Δ / v) ^ 2 * v / 2) := by
        rw [Real.exp_add]
        ring
    _ = 2 * 2 ^ v * Real.exp (-(Δ ^ 2 / (2 * v))) := by rw [e]

lemma sum_exp_neg_abs_le {β : ℝ} (hβ : 0 < β) (T : Finset ℤ) :
    ∑ k ∈ T, Real.exp (-(β * |(k : ℝ)|)) ≤ (1 + Real.exp (-β)) / (1 - Real.exp (-β)) := by
  set r := Real.exp (-β) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith
  have hf : ∀ k : ℤ, Real.exp (-(β * |(k : ℝ)|)) = r ^ k.natAbs := by
    intro k
    rw [hr, ← Real.exp_nat_mul, Nat.cast_natAbs, Int.cast_abs]
    congr 1
    ring
  have hS : HasSum (fun k : ℤ => r ^ k.natAbs) ((1 - r)⁻¹ + r * (1 - r)⁻¹) := by
    apply HasSum.of_nat_of_neg_add_one
    · simpa using hasSum_geometric_of_lt_one hr0 hr1
    · have := (hasSum_geometric_of_lt_one hr0 hr1).mul_left r
      convert this using 1
      ext n
      have : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega
      rw [this, pow_succ]
      ring
  have hle := sum_le_hasSum T (fun k _ => by positivity) hS
  simp_rw [hf]
  calc ∑ k ∈ T, r ^ k.natAbs ≤ (1 - r)⁻¹ + r * (1 - r)⁻¹ := hle
    _ = (1 + r) / (1 - r) := by
        have : 1 - r ≠ 0 := by linarith
        field_simp

lemma weighted_pigeonhole {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω] (M : ℕ)
    (b : Ω → Fin M → ℤ) {β : ℝ} (hβ : 0 < β) :
    ∃ p₀, (Fintype.card Ω : ℝ) *
        Real.exp (-(β / Fintype.card Ω * ∑ p, ∑ i, |(b p i : ℝ)|)) ≤
      (univ.filter (fun p => b p = b p₀)).card *
        ((1 + Real.exp (-β)) / (1 - Real.exp (-β))) ^ M := by
  set N := Fintype.card Ω with hNdef
  have hN : (0 : ℝ) < N := by exact_mod_cast Fintype.card_pos
  set q := (1 + Real.exp (-β)) / (1 - Real.exp (-β)) with hq
  set W : (Fin M → ℤ) → ℝ := fun c => Real.exp (-(β * ∑ i, |(c i : ℝ)|)) with hW
  have hW0 : ∀ c, 0 ≤ W c := fun c => (Real.exp_pos _).le
  -- Jensen
  have hJ : (N : ℝ) * Real.exp (-(β / N * ∑ p, ∑ i, |(b p i : ℝ)|)) ≤ ∑ p, W (b p) := by
    have hw1 : ∑ _p : Ω, (1 / N : ℝ) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, ← hNdef, nsmul_eq_mul]
      field_simp
    have hjen := (convexOn_exp).map_sum_le (t := univ) (w := fun _ => (1 / N : ℝ))
      (p := fun p => -(β * ∑ i, |(b p i : ℝ)|))
      (fun _ _ => by positivity) hw1 (fun _ _ => Set.mem_univ _)
    simp only [smul_eq_mul] at hjen
    rw [← Finset.mul_sum, ← Finset.mul_sum] at hjen
    have e : 1 / (N : ℝ) * ∑ p, -(β * ∑ i, |(b p i : ℝ)|) =
        -(β / N * ∑ p, ∑ i, |(b p i : ℝ)|) := by
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      ring
    rw [e] at hjen
    calc (N : ℝ) * Real.exp (-(β / N * ∑ p, ∑ i, |(b p i : ℝ)|))
        ≤ (N : ℝ) * (1 / N * ∑ p, W (b p)) := mul_le_mul_of_nonneg_left hjen hN.le
      _ = ∑ p, W (b p) := by field_simp
  -- fibres
  set I := univ.image b with hI
  have hIne : I.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  obtain ⟨c₀, hc₀I, hc₀max⟩ :=
    I.exists_max_image (fun c => (univ.filter (fun p => b p = c)).card) hIne
  obtain ⟨p₀, -, hp₀⟩ := Finset.mem_image.mp hc₀I
  refine ⟨p₀, ?_⟩
  rw [hp₀]
  have hfib : ∑ p, W (b p) = ∑ c ∈ I, ((univ.filter (fun p => b p = c)).card : ℝ) * W c := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := I) (g := b)
      (fun p _ => Finset.mem_image_of_mem b (Finset.mem_univ p))]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_congr rfl (fun p hp => by rw [(Finset.mem_filter.mp hp).2])]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hbox : ∑ c ∈ I, W c ≤ q ^ M := by
    set T : Fin M → Finset ℤ := fun i => I.image (fun c => c i) with hT
    set P : Finset (Fin M → ℤ) := Fintype.piFinset T with hP
    have hsub : I ⊆ P := by
      intro c hc
      rw [hP, Fintype.mem_piFinset]
      intro i
      exact Finset.mem_image_of_mem _ hc
    have hWp : ∀ c : Fin M → ℤ, W c = ∏ i : Fin M, Real.exp (-(β * |((c i : ℤ) : ℝ)|)) := by
      intro c
      simp only [hW]
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    calc ∑ c ∈ I, W c ≤ ∑ c ∈ P, W c :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun c _ _ => hW0 c)
      _ = ∑ c ∈ P, ∏ i : Fin M, Real.exp (-(β * |((c i : ℤ) : ℝ)|)) :=
          Finset.sum_congr rfl (fun c _ => hWp c)
      _ = ∏ i : Fin M, ∑ k ∈ T i, Real.exp (-(β * |((k : ℤ) : ℝ)|)) :=
          (Finset.prod_univ_sum T (fun _ k => Real.exp (-(β * |((k : ℤ) : ℝ)|)))).symm
      _ ≤ ∏ _i : Fin M, q :=
          Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le))
            (fun i _ => sum_exp_neg_abs_le hβ _)
      _ = q ^ M := by simp
  calc (N : ℝ) * Real.exp (-(β / N * ∑ p, ∑ i, |(b p i : ℝ)|)) ≤ ∑ p, W (b p) := hJ
    _ = ∑ c ∈ I, ((univ.filter (fun p => b p = c)).card : ℝ) * W c := hfib
    _ ≤ ∑ c ∈ I, ((univ.filter (fun p => b p = c₀)).card : ℝ) * W c :=
        Finset.sum_le_sum (fun c hc => mul_le_mul_of_nonneg_right
          (by exact_mod_cast hc₀max c hc) (hW0 c))
    _ = ((univ.filter (fun p => b p = c₀)).card : ℝ) * ∑ c ∈ I, W c := by
        rw [Finset.mul_sum]
    _ ≤ ((univ.filter (fun p => b p = c₀)).card : ℝ) * q ^ M :=
        mul_le_mul_of_nonneg_left hbox (by positivity)

lemma hamming_ball_card_le {v : ℕ} (σ : Fin v → Bool) :
    ((univ.filter (fun τ : Fin v → Bool =>
        10 * (univ.filter (fun j => σ j ≠ τ j)).card < v)).card : ℝ) ≤
      ((1 + (4 / 5 : ℝ) ^ 10) / (4 / 5)) ^ v := by
  set s : ℝ := (4 / 5 : ℝ) ^ 10 with hs
  set B := univ.filter (fun τ : Fin v → Bool =>
    10 * (univ.filter (fun j => σ j ≠ τ j)).card < v) with hB
  have hprod : ∀ τ : Fin v → Bool, s ^ (univ.filter (fun j => σ j ≠ τ j)).card =
      ∏ j, (if σ j ≠ τ j then s else 1) := by
    intro τ
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  have hsum : ∑ τ : Fin v → Bool, s ^ (univ.filter (fun j => σ j ≠ τ j)).card =
      (1 + s) ^ v := by
    simp_rw [hprod]
    rw [← Fintype.prod_sum (fun j (c : Bool) => if σ j ≠ c then s else 1)]
    have : ∀ j, ∑ c : Bool, (if σ j ≠ c then s else 1) = 1 + s := by
      intro j
      rw [Fintype.sum_bool]
      cases σ j <;> simp [add_comm]
    rw [Finset.prod_congr rfl (fun j _ => this j), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hlow : ∀ τ ∈ B, (4 / 5 : ℝ) ^ v ≤ s ^ (univ.filter (fun j => σ j ≠ τ j)).card := by
    intro τ hτ
    have h := (Finset.mem_filter.mp hτ).2
    rw [hs, ← pow_mul]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hmain : (B.card : ℝ) * (4 / 5) ^ v ≤ (1 + s) ^ v := by
    calc (B.card : ℝ) * (4 / 5) ^ v = ∑ τ ∈ B, (4 / 5 : ℝ) ^ v := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ τ ∈ B, s ^ (univ.filter (fun j => σ j ≠ τ j)).card := Finset.sum_le_sum hlow
      _ ≤ ∑ τ : Fin v → Bool, s ^ (univ.filter (fun j => σ j ≠ τ j)).card :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun _ _ _ => by positivity)
      _ = (1 + s) ^ v := hsum
  rw [div_pow, le_div_iff₀ (by positivity)]
  exact hmain

lemma key_ineq {v M : ℝ} (hv : 0 < v) (hvM : v ≤ M) :
    Real.log ((40 * M + v) / v) * (2 * M * Real.exp (-(50 * Real.log (2 * M / v)))) ≤
      v / 20 := by
  have hM : 0 < M := by linarith
  set y := 2 * M / v with hy
  have hy2 : 2 ≤ y := by
    rw [hy, le_div_iff₀ hv]
    linarith
  have hy0 : 0 < y := by linarith
  have hMy : M = y * v / 2 := by
    rw [hy]
    field_simp
  have hlog : Real.log ((40 * M + v) / v) ≤ 20 * y := by
    have := Real.log_le_sub_one_of_pos (show 0 < (40 * M + v) / v by positivity)
    have e : (40 * M + v) / v - 1 = 20 * y := by
      rw [hy]
      field_simp
      ring
    linarith
  have hexp : Real.exp (-(50 * Real.log y)) = 1 / y ^ 50 := by
    rw [Real.exp_neg, show (50 : ℝ) * Real.log y = Real.log (y ^ 50) by
      rw [Real.log_pow]; norm_num, Real.exp_log (by positivity), one_div]
  rw [hexp]
  have hpow : 400 * y ^ 2 ≤ y ^ 50 := by
    have h0 : (2 : ℝ) ^ 48 ≤ y ^ 48 := pow_le_pow_left₀ (by norm_num) hy2 48
    have h1 : (2 : ℝ) ^ 48 * y ^ 2 ≤ y ^ 48 * y ^ 2 :=
      mul_le_mul_of_nonneg_right h0 (sq_nonneg y)
    have h2 : 400 * y ^ 2 ≤ (2 : ℝ) ^ 48 * y ^ 2 :=
      mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg y)
    have e : y ^ 50 = y ^ 48 * y ^ 2 := by ring
    linarith
  have hpos : 0 ≤ 2 * M * (1 / y ^ 50) := by positivity
  have hvy := mul_le_mul_of_nonneg_left hpow hv.le
  calc Real.log ((40 * M + v) / v) * (2 * M * (1 / y ^ 50))
      ≤ 20 * y * (2 * M * (1 / y ^ 50)) := mul_le_mul_of_nonneg_right hlog hpos
    _ = 20 * v * y ^ 2 / y ^ 50 := by
        rw [hMy]
        field_simp
    _ ≤ v / 20 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith

lemma q_pow_le {v : ℝ} (hv : 0 < v) {M : ℕ} (hM : 0 < M) :
    ((1 + Real.exp (-Real.log ((40 * M + v) / v))) /
        (1 - Real.exp (-Real.log ((40 * M + v) / v)))) ^ M ≤ Real.exp (v / 20) := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hM0 : (M : ℝ) ≠ 0 := ne_of_gt hM'
  have hden : (40 * M + v : ℝ) ≠ 0 := by positivity
  have hr : Real.exp (-Real.log ((40 * M + v) / v)) = v / (40 * M + v) := by
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  rw [hr]
  have h1 : 1 - v / (40 * M + v) = 40 * M / (40 * M + v) := by
    field_simp
    ring
  have h2 : 1 + v / (40 * M + v) = (40 * M + 2 * v) / (40 * M + v) := by
    field_simp
    ring
  have e : (1 + v / (40 * M + v)) / (1 - v / (40 * M + v)) = v / (20 * M) + 1 := by
    rw [h1, h2]
    field_simp
    ring
  rw [e]
  calc (v / (20 * M) + 1) ^ M ≤ Real.exp (v / (20 * M)) ^ M :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) M
    _ = Real.exp (v / 20) := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp

lemma final_ineq {v : ℕ} (hv : 1 ≤ v) :
    ((1 + (4 / 5 : ℝ) ^ 10) / (4 / 5)) ^ v < 2 ^ v * Real.exp (-(v / 10 : ℝ)) := by
  have he : Real.exp (-(v / 10 : ℝ)) = Real.exp (-(1 / 10)) ^ v := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, ← mul_pow]
  have h1 : (9 / 10 : ℝ) ≤ Real.exp (-(1 / 10)) := by
    have := Real.add_one_le_exp (-(1 / 10) : ℝ)
    linarith
  apply pow_lt_pow_left₀ _ (by positivity) (by omega)
  calc (1 + (4 / 5 : ℝ) ^ 10) / (4 / 5) < 2 * (9 / 10) := by norm_num
    _ ≤ 2 * Real.exp (-(1 / 10)) := by linarith

end PartialAux

open PartialAux in
theorem partialColoringStatement_holds : PartialColoringStatement := by
  refine ⟨10, by norm_num, ?_⟩
  intro M v hv hvM A hA
  have hvpos : (0 : ℝ) < v := by exact_mod_cast hv
  have hvM' : (v : ℝ) ≤ M := by exact_mod_cast hvM
  have hMpos : 0 < M := by omega
  have hMpos' : (0 : ℝ) < M := by exact_mod_cast hMpos
  set L := Real.log (2 * M / v) with hL
  have h2le : (2 : ℝ) ≤ 2 * M / v := by
    rw [le_div_iff₀ hvpos]
    linarith
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) h2le
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hLpos : 0 < L := by linarith
  set Δ := 10 * Real.sqrt (v * L) with hΔ
  have hΔpos : 0 < Δ := by positivity
  have hΔsq : Δ ^ 2 = 100 * (v * L) := by
    rw [hΔ, mul_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have hvΔ : (v : ℝ) ≤ Δ ^ 2 := by
    rw [hΔsq]
    nlinarith
  set b : (Fin v → Bool) → Fin M → ℤ := fun σ i => round (rowS (A i) σ / (2 * Δ)) with hb
  set β := Real.log ((40 * M + v) / v) with hβdef
  have hβ : 0 < β := Real.log_pos (by rw [lt_div_iff₀ hvpos]; linarith)
  obtain ⟨σ₀, hσ₀⟩ := weighted_pigeonhole M b hβ
  have hcard : (Fintype.card (Fin v → Bool) : ℝ) = 2 ^ v := by simp
  rw [hcard] at hσ₀
  have hrow : ∀ i, ∑ σ, |(b σ i : ℝ)| ≤ 2 * 2 ^ v * Real.exp (-(50 * L)) := by
    intro i
    have := sum_abs_round_le hv (A i) (hA i) hΔpos hvΔ
    have e : Δ ^ 2 / (2 * v) = 50 * L := by
      rw [hΔsq]
      field_simp
      ring
    rw [e] at this
    exact this
  have hS : ∑ σ, ∑ i, |(b σ i : ℝ)| ≤ M * (2 * 2 ^ v * Real.exp (-(50 * L))) := by
    rw [Finset.sum_comm]
    calc ∑ i, ∑ σ, |(b σ i : ℝ)| ≤ ∑ _i : Fin M, (2 * 2 ^ v * Real.exp (-(50 * L))) :=
          Finset.sum_le_sum (fun i _ => hrow i)
      _ = M * (2 * 2 ^ v * Real.exp (-(50 * L))) := by simp
  have havg : β / 2 ^ v * ∑ σ, ∑ i, |(b σ i : ℝ)| ≤ v / 20 := by
    calc β / 2 ^ v * ∑ σ, ∑ i, |(b σ i : ℝ)|
        ≤ β / 2 ^ v * (M * (2 * 2 ^ v * Real.exp (-(50 * L)))) :=
          mul_le_mul_of_nonneg_left hS (by positivity)
      _ = β * (2 * M * Real.exp (-(50 * L))) := by
          field_simp
      _ ≤ v / 20 := key_ineq hvpos hvM'
  have hq := q_pow_le hvpos hMpos
  set F := Finset.univ.filter (fun σ => b σ = b σ₀) with hF
  have hFbig : (2 : ℝ) ^ v * Real.exp (-(v / 10 : ℝ)) ≤ F.card := by
    have h1 : (2 : ℝ) ^ v * Real.exp (-(v / 20 : ℝ)) ≤ F.card * Real.exp (v / 20) := by
      calc (2 : ℝ) ^ v * Real.exp (-(v / 20 : ℝ))
          ≤ 2 ^ v * Real.exp (-(β / 2 ^ v * ∑ σ, ∑ i, |(b σ i : ℝ)|)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
        _ ≤ _ := hσ₀
        _ ≤ _ := mul_le_mul_of_nonneg_left hq (by positivity)
    have h2 : Real.exp (-(v / 10 : ℝ)) =
        Real.exp (-(v / 20 : ℝ)) * Real.exp (-(v / 20 : ℝ)) := by
      rw [← Real.exp_add]
      ring_nf
    have h3 : Real.exp (v / 20) * Real.exp (-(v / 20 : ℝ)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc (2 : ℝ) ^ v * Real.exp (-(v / 10 : ℝ))
        = (2 ^ v * Real.exp (-(v / 20 : ℝ))) * Real.exp (-(v / 20 : ℝ)) := by
          rw [h2]
          ring
      _ ≤ (F.card * Real.exp (v / 20)) * Real.exp (-(v / 20 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = F.card := by rw [mul_assoc, h3, mul_one]
  have hball := hamming_ball_card_le σ₀
  have hfin := final_ineq hv
  set B := Finset.univ.filter (fun τ : Fin v → Bool =>
    10 * (Finset.univ.filter (fun j => σ₀ j ≠ τ j)).card < v) with hB
  have hlt : B.card < F.card := by
    have : (B.card : ℝ) < F.card := by linarith
    exact_mod_cast this
  obtain ⟨σ₁, hσ₁F, hσ₁B⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hbeq : b σ₁ = b σ₀ := (Finset.mem_filter.mp hσ₁F).2
  have hfar : v ≤ 10 * (Finset.univ.filter (fun j => σ₀ j ≠ σ₁ j)).card := by
    have : ¬ (10 * (Finset.univ.filter (fun j => σ₀ j ≠ σ₁ j)).card < v) := fun h =>
      hσ₁B (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    omega
  set x : Fin v → ℤ := fun j => if σ₀ j = σ₁ j then 0 else (if σ₀ j then 1 else -1) with hx
  refine ⟨x, ?_, ?_, ?_⟩
  · intro j
    simp only [hx]
    split_ifs <;> simp
  · have : Finset.univ.filter (fun j => x j ≠ 0) =
        Finset.univ.filter (fun j => σ₀ j ≠ σ₁ j) := by
      apply Finset.filter_congr
      intro j _
      simp only [hx]
      by_cases h : σ₀ j = σ₁ j
      · simp [h]
      · simp only [h, ite_false, ne_eq, not_false_eq_true, iff_true]
        split_ifs <;> norm_num
    rw [this]
    exact hfar
  · intro i
    have hxr : ∀ j, ((x j : ℤ) : ℝ) = (sgn (σ₀ j) - sgn (σ₁ j)) / 2 := by
      intro j
      simp only [hx]
      cases σ₀ j <;> cases σ₁ j <;> norm_num [sgn]
    have hsum : ∑ j, A i j * ((x j : ℤ) : ℝ) = (rowS (A i) σ₀ - rowS (A i) σ₁) / 2 := by
      simp_rw [hxr]
      rw [rowS, rowS, ← Finset.sum_sub_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hsum]
    have hbi : round (rowS (A i) σ₀ / (2 * Δ)) = round (rowS (A i) σ₁ / (2 * Δ)) := by
      have := congrFun hbeq i
      simp only [hb] at this
      exact this.symm
    have h0 := abs_sub_round (rowS (A i) σ₀ / (2 * Δ))
    have h1 := abs_sub_round (rowS (A i) σ₁ / (2 * Δ))
    rw [hbi] at h0
    have h2 : |rowS (A i) σ₀ / (2 * Δ) - rowS (A i) σ₁ / (2 * Δ)| ≤ 1 := by
      calc |rowS (A i) σ₀ / (2 * Δ) - rowS (A i) σ₁ / (2 * Δ)|
          = |(rowS (A i) σ₀ / (2 * Δ) - round (rowS (A i) σ₁ / (2 * Δ))) -
              (rowS (A i) σ₁ / (2 * Δ) - round (rowS (A i) σ₁ / (2 * Δ)))| := by ring_nf
        _ ≤ |rowS (A i) σ₀ / (2 * Δ) - round (rowS (A i) σ₁ / (2 * Δ))| +
              |rowS (A i) σ₁ / (2 * Δ) - round (rowS (A i) σ₁ / (2 * Δ))| := abs_sub _ _
        _ ≤ 1 := by linarith
    rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * Δ),
      div_le_iff₀ (by positivity)] at h2
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), div_le_iff₀ (by norm_num)]
    linarith

end ChowlaOpus
