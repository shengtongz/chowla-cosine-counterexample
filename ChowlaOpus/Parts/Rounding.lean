module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.RoundingAux

open Finset

/-- `x ↦ x log (A / x)` is monotone on `[0, A / e]`. -/
lemma mul_log_div_mono {A x y : ℝ} (hA : 0 < A) (hx : 0 ≤ x) (hxy : x ≤ y)
    (hy1 : 1 ≤ Real.log (A / y)) :
    x * Real.log (A / x) ≤ y * Real.log (A / y) := by
  have hy : 0 < y := by
    rcases (hx.trans hxy).eq_or_lt with h | h
    · rw [← h] at hy1; simp at hy1; linarith
    · exact h
  rcases hx.eq_or_lt with h | hx'
  · rw [← h]; simp; exact mul_nonneg hy.le (by linarith)
  · have h1 : Real.log (A / x) = Real.log (A / y) + Real.log (y / x) := by
      rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
    have h2 : Real.log (y / x) ≤ y / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : x * Real.log (y / x) ≤ y - x := by
      calc x * Real.log (y / x) ≤ x * (y / x - 1) := mul_le_mul_of_nonneg_left h2 hx
        _ = y - x := by field_simp
    rw [h1]; nlinarith

/-- The cost of one rounding level. -/
lemma cost_bound {A N U Δ L x : ℝ} (hA : 0 < A) (hN : 0 < N) (hU : 0 < U) (hΔ : 0 < Δ)
    (hΔ1 : Δ ≤ 1) (hx : 0 ≤ x) (hxN : x ≤ N) (hxU : x * Δ ≤ U)
    (hAN : 1 ≤ Real.log (A / N)) (hLN : Real.log (A / N) ≤ L) (hLU : Real.log (A / U) ≤ L) :
    Δ ^ 2 * (x * Real.log (A / x)) ≤ Δ * U * L := by
  rcases le_or_gt (N * Δ) U with h | h
  · have hm := mul_log_div_mono hA hx hxN hAN
    calc Δ ^ 2 * (x * Real.log (A / x)) ≤ Δ ^ 2 * (N * Real.log (A / N)) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ = Δ * (N * Δ) * Real.log (A / N) := by ring
      _ ≤ Δ * U * Real.log (A / N) := by gcongr
      _ ≤ Δ * U * L := by gcongr
  · set y := U / Δ with hy
    have hypos : 0 < y := by positivity
    have hyN : y < N := by rw [hy, div_lt_iff₀ hΔ]; linarith
    have hxy : x ≤ y := by rw [hy, le_div_iff₀ hΔ]; linarith
    have hy1 : 1 ≤ Real.log (A / y) := le_trans hAN
      (Real.log_le_log (by positivity) (div_le_div_of_nonneg_left hA.le hypos hyN.le))
    have hm := mul_log_div_mono hA hx hxy hy1
    have hlog : Real.log (A / y) ≤ L := by
      calc Real.log (A / y) = Real.log (A * Δ / U) := by
            congr 1; rw [hy]; field_simp
        _ ≤ Real.log (A / U) := Real.log_le_log (by positivity)
            (div_le_div_of_nonneg_right (by nlinarith) hU.le)
        _ ≤ L := hLU
    calc Δ ^ 2 * (x * Real.log (A / x)) ≤ Δ ^ 2 * (y * Real.log (A / y)) :=
          mul_le_mul_of_nonneg_left hm (by positivity)
      _ = Δ * U * Real.log (A / y) := by rw [hy]; field_simp
      _ ≤ Δ * U * L := by gcongr

/-- The per-level cost, in the form used by the iteration. -/
lemma level_bound {CS U L : ℝ} {N M : ℕ} (hCS : 0 ≤ CS) (hN : 0 < N) (hU : 0 < U) (hM : 0 < M)
    (hAN : 1 ≤ Real.log (2 * M / N)) (hLN : Real.log (2 * M / N) ≤ L)
    (hLU : Real.log (2 * M / U) ≤ L) (k v : ℕ) (hvN : v ≤ N) (hvU : (v : ℝ) / 2 ^ (k + 1) ≤ U) :
    CS * Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1) ≤
      CS * Real.sqrt (U * L) * (3 / 4) ^ (k + 1) := by
  set Δ : ℝ := 1 / 2 ^ (k + 1) with hΔ
  have hΔpos : 0 < Δ := by positivity
  have hΔ1 : Δ ≤ 1 := by
    rw [hΔ, div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
  have hc := cost_bound (A := 2 * M) (N := N) (U := U) (Δ := Δ) (L := L) (x := v)
    (by positivity) (by exact_mod_cast hN) hU hΔpos hΔ1 (by positivity)
    (by exact_mod_cast hvN) (by rw [hΔ, mul_one_div]; exact hvU) hAN hLN hLU
  have hsq : Real.sqrt Δ ≤ (3 / 4) ^ (k + 1) := by
    rw [Real.sqrt_le_left (by positivity), hΔ, ← pow_mul, mul_comm, pow_mul, ← one_div_pow]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have key : Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1) ≤
      Real.sqrt (U * L) * (3 / 4) ^ (k + 1) := by
    calc Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1)
          = Real.sqrt (Δ ^ 2 * (v * Real.log (2 * M / v))) := by
          rw [Real.sqrt_mul (sq_nonneg Δ) (↑v * _), Real.sqrt_sq hΔpos.le, hΔ]; ring
      _ ≤ Real.sqrt (Δ * U * L) := Real.sqrt_le_sqrt hc
      _ = Real.sqrt Δ * Real.sqrt (U * L) := by rw [mul_assoc, Real.sqrt_mul hΔpos.le]
      _ ≤ (3 / 4) ^ (k + 1) * Real.sqrt (U * L) := by gcongr
      _ = _ := by ring
  calc CS * Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1)
        = CS * (Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1)) := by ring
    _ ≤ CS * (Real.sqrt (U * L) * (3 / 4) ^ (k + 1)) := by gcongr
    _ = _ := by ring

/-- Spencer's theorem in the form used below. -/
def SpencerProp (CS : ℝ) : Prop :=
  ∀ (M v : ℕ), 1 ≤ v → v ≤ M → ∀ A : Fin M → Fin v → ℝ,
    (∀ i j, |A i j| ≤ 1) → ∃ ε : Fin v → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
      ∀ i, |∑ j, A i j * ε j| ≤ CS * Real.sqrt (v * Real.log (2 * M / v))

/-- One dyadic rounding step: numerators `m` at level `k + 1` become numerators `m'` at
level `k`. -/
lemma step {CS : ℝ} (hSp : SpencerProp CS) (N M : ℕ) (hNM : N ≤ M) (σ : ℕ → ℝ)
    (hσ : ∀ d, |σ d| ≤ 1) (k : ℕ) (m : ℕ → ℕ) (hm : ∀ d ∈ Icc 1 N, m d ≤ 2 ^ (k + 1)) :
    ∃ m' : ℕ → ℕ, (∀ d ∈ Icc 1 N, m' d ≤ 2 ^ k) ∧
      (∑ d ∈ Icc 1 N, (2 * (m' d : ℝ))) ≤ ∑ d ∈ Icc 1 N, (m d : ℝ) ∧
      ∀ i < M, |∑ d ∈ Icc 1 N, σ d * (2 * (m' d : ℝ) - m d) *
          Real.cos (2 * π * d * ((i : ℝ) / M))| ≤
        CS * Real.sqrt (((Icc 1 N).filter (fun d => Odd (m d))).card *
          Real.log (2 * M / ((Icc 1 N).filter (fun d => Odd (m d))).card)) := by
  classical
  set J := (Icc 1 N).filter (fun d => Odd (m d)) with hJ
  set v := J.card with hv
  let e : Fin v ≃ J := J.equivFin.symm
  obtain ⟨ε, hε1, hεsum, hεrow⟩ : ∃ ε : Fin v → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧ ∑ j, ε j ≤ 0 ∧
      ∀ i < M, |∑ j, σ (e j) * Real.cos (2 * π * ((e j : ℕ) : ℝ) * ((i : ℝ) / M)) * ε j| ≤
        CS * Real.sqrt (v * Real.log (2 * M / v)) := by
    rcases Nat.eq_zero_or_pos v with hv0 | hvpos
    · have : IsEmpty (Fin v) := by rw [hv0]; infer_instance
      refine ⟨fun _ => 1, fun _ => Or.inl rfl, by simp, fun i _ => ?_⟩
      simp [hv0]
    · have hvM : v ≤ M := by
        have : v ≤ (Icc 1 N).card := card_le_card (filter_subset _ _)
        simp at this; omega
      obtain ⟨ε, hε1, hεb⟩ := hSp M v hvpos hvM
        (fun i j => σ (e j) * Real.cos (2 * π * ((e j : ℕ) : ℝ) * (((i : ℕ) : ℝ) / M))) (by
          intro i j; rw [abs_mul]
          calc |σ (e j)| * |Real.cos (2 * π * ((e j : ℕ) : ℝ) * (((i : ℕ) : ℝ) / M))|
              ≤ 1 * 1 := mul_le_mul (hσ _) (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
            _ = 1 := one_mul 1)
      by_cases hs : ∑ j, ε j ≤ 0
      · exact ⟨ε, hε1, hs, fun i hi => hεb ⟨i, hi⟩⟩
      · refine ⟨fun j => -ε j, fun j => (hε1 j).elim (fun h => Or.inr (by simp [h]))
          (fun h => Or.inl (by simp [h])), ?_, ?_⟩
        · rw [Finset.sum_neg_distrib]; linarith
        · intro i hi
          have := hεb ⟨i, hi⟩
          simp only [mul_neg, Finset.sum_neg_distrib, abs_neg]
          exact this
  let δ : ℕ → ℝ := fun d => if h : d ∈ J then ε (e.symm ⟨d, h⟩) else 0
  have hδsum : ∀ f : ℕ → ℝ, ∑ d ∈ Icc 1 N, δ d * f d = ∑ j, ε j * f (e j) := by
    intro f
    have h1 : ∑ d ∈ J, δ d * f d = ∑ d ∈ Icc 1 N, δ d * f d :=
      Finset.sum_subset (filter_subset _ _) (fun d _ hdJ => by simp [δ, hdJ])
    rw [← h1, ← Finset.sum_coe_sort J, ← Equiv.sum_comp e]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [δ]
  have hex : ∀ d, ∃ n : ℕ, d ∈ Icc 1 N → n ≤ 2 ^ k ∧ (2 * (n : ℝ)) = m d + δ d := by
    intro d
    by_cases hd : d ∈ Icc 1 N
    · have hmd := hm d hd
      rw [pow_succ] at hmd
      by_cases hdJ : d ∈ J
      · obtain ⟨q, hq⟩ : Odd (m d) := (mem_filter.mp hdJ).2
        have hδ : δ d = ε (e.symm ⟨d, hdJ⟩) := by simp [δ, hdJ]
        rcases hε1 (e.symm ⟨d, hdJ⟩) with h | h
        · refine ⟨q + 1, fun _ => ⟨?_, ?_⟩⟩
          · omega
          · rw [hδ, h, hq]; push_cast; ring
        · refine ⟨q, fun _ => ⟨?_, ?_⟩⟩
          · omega
          · rw [hδ, h, hq]; push_cast; ring
      · have heven : Even (m d) := by
          have : ¬ Odd (m d) := fun h => hdJ (mem_filter.mpr ⟨hd, h⟩)
          exact Nat.not_odd_iff_even.mp this
        obtain ⟨q, hq⟩ := heven
        have hδ : δ d = 0 := by simp [δ, hdJ]
        refine ⟨q, fun _ => ⟨?_, ?_⟩⟩
        · omega
        · rw [hδ, hq]; push_cast; ring
    · exact ⟨0, fun h => absurd h hd⟩
  choose m' hm' using hex
  refine ⟨m', fun d hd => (hm' d hd).1, ?_, ?_⟩
  · have h2 : ∑ d ∈ Icc 1 N, 2 * (m' d : ℝ) =
        ∑ d ∈ Icc 1 N, (m d : ℝ) + ∑ d ∈ Icc 1 N, δ d * 1 := by
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun d hd => by rw [(hm' d hd).2]; ring)
    rw [h2, hδsum]; simp only [mul_one]; linarith
  · intro i hi
    have h3 : ∑ d ∈ Icc 1 N, σ d * (2 * (m' d : ℝ) - m d) *
          Real.cos (2 * π * d * ((i : ℝ) / M)) =
        ∑ d ∈ Icc 1 N, δ d * (σ d * Real.cos (2 * π * d * ((i : ℝ) / M))) :=
      sum_congr rfl (fun d hd => by rw [(hm' d hd).2]; ring)
    rw [h3, hδsum]
    calc _ = |∑ j, σ (e j) * Real.cos (2 * π * ((e j : ℕ) : ℝ) * ((i : ℝ) / M)) * ε j| := by
          congr 1; exact sum_congr rfl (fun j _ => by ring)
      _ ≤ _ := hεrow i hi

/-- The full dyadic rounding process, from level `k` down to level `0`. -/
lemma iterate {CS : ℝ} (hSp : SpencerProp CS) (N M : ℕ) (hNM : N ≤ M) (σ : ℕ → ℝ)
    (hσ : ∀ d, |σ d| ≤ 1) (U G : ℝ)
    (hlevel : ∀ k v : ℕ, v ≤ N → (v : ℝ) / 2 ^ (k + 1) ≤ U →
      CS * Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1) ≤ G * (3 / 4) ^ (k + 1)) :
    ∀ k (m : ℕ → ℕ), (∀ d ∈ Icc 1 N, m d ≤ 2 ^ k) → ∑ d ∈ Icc 1 N, (m d : ℝ) / 2 ^ k ≤ U →
      ∃ a : ℕ → ℕ, (∀ d ∈ Icc 1 N, a d ≤ 1) ∧ ∀ i < M,
        |∑ d ∈ Icc 1 N, σ d * ((a d : ℝ) - m d / 2 ^ k) *
            Real.cos (2 * π * d * ((i : ℝ) / M))| ≤
          ∑ j ∈ range k, G * (3 / 4) ^ (j + 1) := by
  intro k
  induction k with
  | zero =>
    intro m hm _
    exact ⟨m, by simpa using hm, fun i _ => by simp⟩
  | succ k ih =>
    intro m hm hU
    obtain ⟨m', hm'1, hm'2, hm'3⟩ := step hSp N M hNM σ hσ k m hm
    set J := (Icc 1 N).filter (fun d => Odd (m d))
    have hvN : J.card ≤ N := by
      calc J.card ≤ (Icc 1 N).card := card_le_card (filter_subset _ _)
        _ = N := by simp
    have hvm : (J.card : ℝ) ≤ ∑ d ∈ Icc 1 N, (m d : ℝ) := by
      calc (J.card : ℝ) = ∑ d ∈ J, (1 : ℝ) := by simp
        _ ≤ ∑ d ∈ J, (m d : ℝ) := sum_le_sum (fun d hd => by
            have := (mem_filter.mp hd).2; exact_mod_cast this.pos)
        _ ≤ ∑ d ∈ Icc 1 N, (m d : ℝ) := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
            (fun _ _ _ => by positivity)
    have hvU : (J.card : ℝ) / 2 ^ (k + 1) ≤ U := by
      calc (J.card : ℝ) / 2 ^ (k + 1) ≤ (∑ d ∈ Icc 1 N, (m d : ℝ)) / 2 ^ (k + 1) := by gcongr
        _ = ∑ d ∈ Icc 1 N, (m d : ℝ) / 2 ^ (k + 1) := by rw [sum_div]
        _ ≤ U := hU
    have hU' : ∑ d ∈ Icc 1 N, (m' d : ℝ) / 2 ^ k ≤ U := by
      calc ∑ d ∈ Icc 1 N, (m' d : ℝ) / 2 ^ k
            = (∑ d ∈ Icc 1 N, 2 * (m' d : ℝ)) / 2 ^ (k + 1) := by
            rw [sum_div]; refine sum_congr rfl (fun d _ => ?_); rw [pow_succ]; field_simp
        _ ≤ (∑ d ∈ Icc 1 N, (m d : ℝ)) / 2 ^ (k + 1) := by gcongr
        _ = ∑ d ∈ Icc 1 N, (m d : ℝ) / 2 ^ (k + 1) := by rw [sum_div]
        _ ≤ U := hU
    obtain ⟨a, ha1, ha2⟩ := ih m' hm'1 hU'
    refine ⟨a, ha1, fun i hi => ?_⟩
    have hsplit : ∑ d ∈ Icc 1 N, σ d * ((a d : ℝ) - m d / 2 ^ (k + 1)) *
          Real.cos (2 * π * d * ((i : ℝ) / M)) =
        ∑ d ∈ Icc 1 N, σ d * ((a d : ℝ) - m' d / 2 ^ k) *
          Real.cos (2 * π * d * ((i : ℝ) / M)) +
        (∑ d ∈ Icc 1 N, σ d * (2 * (m' d : ℝ) - m d) *
          Real.cos (2 * π * d * ((i : ℝ) / M))) / 2 ^ (k + 1) := by
      rw [sum_div, ← sum_add_distrib]
      refine sum_congr rfl (fun d _ => ?_)
      rw [pow_succ]; field_simp; ring
    rw [hsplit, sum_range_succ]
    refine (abs_add_le _ _).trans (add_le_add (ha2 i hi) ?_)
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (k + 1))]
    calc _ ≤ CS * Real.sqrt (J.card * Real.log (2 * M / J.card)) / 2 ^ (k + 1) := by
          gcongr; exact hm'3 i hi
      _ ≤ G * (3 / 4) ^ (k + 1) := hlevel k J.card hvN hvU

end ChowlaOpus.RoundingAux

namespace ChowlaOpus

open Finset RoundingAux in
theorem roundingStatement_holds (hS : SpencerStatement) (hM : MeshStatement) :
    RoundingStatement := by
  obtain ⟨CS, hCS, hSp⟩ := hS
  obtain ⟨K, hK1, hMesh⟩ := hM
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1'
  set cK : ℝ := Real.log K / Real.log 2 + 2 with hcK
  have hcK0 : 0 ≤ cK := by positivity
  set κ : ℝ := 3 * (CS * Real.sqrt (2 * cK)) + 1 with hκ
  have hκ0 : 0 < κ := by positivity
  refine ⟨2 * κ, by positivity, ?_⟩
  intro N w S hN hw hS0 hSN hvar
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set lam := Real.log (2 * N / S) with hlam_def
  have hlam : Real.log 2 ≤ lam :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hS0]; linarith)
  have hlampos : 0 < lam := lt_of_lt_of_le hlog2 hlam
  have hSlam : 0 < S * lam := mul_pos hS0 hlampos
  set M : ℕ := 2 * K * N with hM_def
  have hMpos : 0 < M := by positivity
  have hNM : N ≤ M := by rw [hM_def]; nlinarith
  have hMR : (M : ℝ) = 2 * K * N := by rw [hM_def]; push_cast; ring
  -- decomposition `w = c + σ u`
  let σ : ℕ → ℝ := fun d => if w d ≤ 1 / 2 then 1 else -1
  let u : ℕ → ℝ := fun d => if w d ≤ 1 / 2 then w d else 1 - w d
  let c : ℕ → ℝ := fun d => if w d ≤ 1 / 2 then 0 else 1
  have hσ : ∀ d, |σ d| ≤ 1 := fun d => by simp only [σ]; split_ifs <;> simp
  have hu0 : ∀ d, 0 ≤ u d := fun d => by
    simp only [u]; split_ifs <;> linarith [hw d]
  have hu1 : ∀ d, u d ≤ 1 := fun d => by
    simp only [u]; split_ifs <;> linarith [hw d]
  have hwcu : ∀ d, w d = c d + σ d * u d := fun d => by
    simp only [c, σ, u]; split_ifs <;> ring
  have huvar : ∀ d, u d ≤ 2 * (w d * (1 - w d)) := fun d => by
    simp only [u]; split_ifs with h <;> nlinarith [hw d]
  set U : ℝ := 2 * S with hU_def
  have hUpos : 0 < U := by positivity
  have hsumu : ∑ d ∈ Icc 1 N, u d ≤ U := by
    calc ∑ d ∈ Icc 1 N, u d ≤ ∑ d ∈ Icc 1 N, 2 * (w d * (1 - w d)) := sum_le_sum (fun d _ => huvar d)
      _ = 2 * ∑ d ∈ Icc 1 N, w d * (1 - w d) := by rw [mul_sum]
      _ ≤ U := by rw [hU_def]; linarith
  -- constants of the level bound
  set L : ℝ := cK * lam with hL_def
  have hAN_eq : 2 * (M : ℝ) / N = 4 * K := by rw [hMR]; field_simp; ring
  have hAN : 1 ≤ Real.log (2 * M / N) := by
    rw [hAN_eq]
    have h4 : (1 : ℝ) < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9; norm_num at this; linarith
    exact le_trans h4.le (Real.log_le_log (by norm_num) (by linarith))
  have hlogK' : Real.log K ≤ Real.log K / Real.log 2 * lam := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]; exact mul_le_mul_of_nonneg_left hlam hlogK
  have hLN : Real.log (2 * M / N) ≤ L := by
    rw [hAN_eq, Real.log_mul (by norm_num) (by positivity),
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow, hL_def, hcK]
    push_cast; nlinarith
  have hLU : Real.log (2 * M / U) ≤ L := by
    have : 2 * (M : ℝ) / U = K * (2 * N / S) := by rw [hMR, hU_def]; field_simp
    rw [this, Real.log_mul (by positivity) (by positivity), hL_def, hcK]
    nlinarith
  set G : ℝ := CS * Real.sqrt (U * L) with hG_def
  have hG0 : 0 ≤ G := by positivity
  have hGeq : G = CS * Real.sqrt (2 * cK) * Real.sqrt (S * lam) := by
    rw [hG_def, mul_assoc CS, ← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * cK)]
    congr 2; rw [hU_def, hL_def]; ring
  have hlevel : ∀ k v : ℕ, v ≤ N → (v : ℝ) / 2 ^ (k + 1) ≤ U →
      CS * Real.sqrt (v * Real.log (2 * M / v)) / 2 ^ (k + 1) ≤ G * (3 / 4) ^ (k + 1) :=
    fun k v hvN hvU => level_bound hCS.le hN hUpos hMpos hAN hLN hLU k v hvN hvU
  -- truncation
  obtain ⟨k₀, hk₀⟩ := pow_unbounded_of_one_lt ((N : ℝ) / Real.sqrt (S * lam)) one_lt_two
  have hsqrtpos : 0 < Real.sqrt (S * lam) := Real.sqrt_pos.mpr hSlam
  have hk₀' : (N : ℝ) / 2 ^ k₀ ≤ Real.sqrt (S * lam) := by
    rw [div_lt_iff₀ hsqrtpos] at hk₀
    rw [div_le_iff₀ (by positivity)]; linarith
  have hP : (0 : ℝ) < 2 ^ k₀ := by positivity
  let m₀ : ℕ → ℕ := fun d => ⌊u d * 2 ^ k₀⌋₊
  have hm₀le : ∀ d, (m₀ d : ℝ) ≤ u d * 2 ^ k₀ := fun d =>
    Nat.floor_le (mul_nonneg (hu0 d) hP.le)
  have hm₀lt : ∀ d, u d * 2 ^ k₀ < m₀ d + 1 := fun d => Nat.lt_floor_add_one _
  have hm₀ : ∀ d ∈ Icc 1 N, m₀ d ≤ 2 ^ k₀ := fun d _ => Nat.floor_le_of_le (by
    push_cast; nlinarith [hu1 d])
  have hm₀u : ∀ d, (m₀ d : ℝ) / 2 ^ k₀ ≤ u d := fun d => by
    rw [div_le_iff₀ hP]; exact hm₀le d
  have hm₀sum : ∑ d ∈ Icc 1 N, (m₀ d : ℝ) / 2 ^ k₀ ≤ U :=
    (sum_le_sum (fun d _ => hm₀u d)).trans hsumu
  have htrunc : ∀ d, |(m₀ d : ℝ) / 2 ^ k₀ - u d| ≤ 1 / 2 ^ k₀ := fun d => by
    rw [abs_sub_comm, abs_of_nonneg (by linarith [hm₀u d])]
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hP]; linarith [hm₀lt d]
  -- the dyadic rounding
  obtain ⟨af, haf1, haf2⟩ := iterate hSp N M hNM σ hσ U G hlevel k₀ m₀ hm₀ hm₀sum
  have hgeom : ∑ j ∈ range k₀, G * (3 / 4 : ℝ) ^ (j + 1) ≤ 3 * G := by
    have h1 : ∑ j ∈ range k₀, G * (3 / 4 : ℝ) ^ (j + 1) =
        G * (3 / 4) * ∑ j ∈ range k₀, (3 / 4 : ℝ) ^ j := by
      rw [mul_sum]; exact sum_congr rfl (fun j _ => by ring)
    have h2 : ∑ j ∈ range k₀, (3 / 4 : ℝ) ^ j ≤ (3 / 4 : ℝ) ^ 0 / (1 - 3 / 4) := by
      rw [range_eq_Ico]; exact geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)
    rw [h1]
    calc G * (3 / 4) * ∑ j ∈ range k₀, (3 / 4 : ℝ) ^ j
          ≤ G * (3 / 4) * ((3 / 4 : ℝ) ^ 0 / (1 - 3 / 4)) := by gcongr
      _ = 3 * G := by ring
  let a : ℕ → ℝ := fun d => if d ∈ Icc 1 N then c d + σ d * af d else 0
  refine ⟨a, ?_, ?_⟩
  · intro d
    simp only [a]
    split_ifs with hd
    · have : af d = 0 ∨ af d = 1 := by have := haf1 d hd; omega
      simp only [c, σ]
      rcases this with h | h <;> rw [h] <;> split_ifs <;> norm_num
    · exact Or.inl rfl
  · intro t
    have hE : ∀ i < M, |∑ d ∈ Icc 1 N, (a d - w d) * Real.cos (2 * π * d * ((i : ℝ) / M))| ≤
        κ * Real.sqrt (S * lam) := by
      intro i hi
      have hsplit : ∑ d ∈ Icc 1 N, (a d - w d) * Real.cos (2 * π * d * ((i : ℝ) / M)) =
          ∑ d ∈ Icc 1 N, σ d * ((af d : ℝ) - m₀ d / 2 ^ k₀) *
            Real.cos (2 * π * d * ((i : ℝ) / M)) +
          ∑ d ∈ Icc 1 N, σ d * ((m₀ d : ℝ) / 2 ^ k₀ - u d) *
            Real.cos (2 * π * d * ((i : ℝ) / M)) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl (fun d hd => ?_)
        simp only [a, hd, ↓reduceIte]; rw [hwcu d]; ring
      have hT : |∑ d ∈ Icc 1 N, σ d * ((m₀ d : ℝ) / 2 ^ k₀ - u d) *
            Real.cos (2 * π * d * ((i : ℝ) / M))| ≤ Real.sqrt (S * lam) := by
        refine (abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ d ∈ Icc 1 N, |σ d * ((m₀ d : ℝ) / 2 ^ k₀ - u d) *
              Real.cos (2 * π * d * ((i : ℝ) / M))| ≤ ∑ d ∈ Icc 1 N, (1 / 2 ^ k₀ : ℝ) := by
              refine sum_le_sum (fun d _ => ?_)
              rw [abs_mul, abs_mul]
              calc |σ d| * |(m₀ d : ℝ) / 2 ^ k₀ - u d| * |Real.cos (2 * π * d * ((i : ℝ) / M))|
                  ≤ 1 * (1 / 2 ^ k₀) * 1 := by
                    gcongr
                    · exact hσ d
                    · exact htrunc d
                    · exact Real.abs_cos_le_one _
                _ = 1 / 2 ^ k₀ := by ring
          _ = (N : ℝ) / 2 ^ k₀ := by simp; ring
          _ ≤ Real.sqrt (S * lam) := hk₀'
      rw [hsplit]
      refine (abs_add_le _ _).trans ?_
      calc _ ≤ 3 * G + Real.sqrt (S * lam) := add_le_add ((haf2 i hi).trans hgeom) hT
        _ = κ * Real.sqrt (S * lam) := by rw [hGeq, hκ]; ring
    have := hMesh N M (fun d => a d - w d) (κ * Real.sqrt (S * lam))
      (by rw [hM_def]; nlinarith) hMpos hE t
    calc _ ≤ 2 * (κ * Real.sqrt (S * lam)) := this
      _ = 2 * κ * Real.sqrt (S * Real.log (2 * N / S)) := by rw [hlam_def]; ring

end ChowlaOpus
