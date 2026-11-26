module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.SpencerAux

/-- The hypothesis of the partial colouring statement, for a fixed constant. -/
def PC (C : ℝ) : Prop :=
  ∀ (M v : ℕ), 1 ≤ v → v ≤ M → ∀ A : Fin M → Fin v → ℝ,
    (∀ i j, |A i j| ≤ 1) →
    ∃ x : Fin v → ℤ, (∀ j, |x j| ≤ 1) ∧
      v ≤ 10 * (Finset.univ.filter (fun j => x j ≠ 0)).card ∧
      ∀ i, |∑ j, A i j * (x j : ℝ)| ≤ C * Real.sqrt (v * Real.log (2 * M / v))

/-- Partial colouring transported to an arbitrary finite index type. -/
lemma pc_fintype {C : ℝ} (hC : PC C) {ι : Type} [Fintype ι] (M : ℕ)
    (h1 : 1 ≤ Fintype.card ι) (h2 : Fintype.card ι ≤ M) (A : Fin M → ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ 1) :
    ∃ x : ι → ℤ, (∀ j, |x j| ≤ 1) ∧
      Fintype.card ι ≤ 10 * (Finset.univ.filter (fun j => x j ≠ 0)).card ∧
      ∀ i, |∑ j, A i j * (x j : ℝ)| ≤
        C * Real.sqrt (Fintype.card ι * Real.log (2 * M / Fintype.card ι)) := by
  set e := Fintype.equivFin ι
  obtain ⟨x, hx1, hx2, hx3⟩ := hC M (Fintype.card ι) h1 h2 (fun i k => A i (e.symm k))
    (fun i k => hA _ _)
  refine ⟨fun j => x (e j), fun j => hx1 _, ?_, ?_⟩
  · have : (Finset.univ.filter (fun j => x (e j) ≠ 0)).card =
        (Finset.univ.filter (fun k => x k ≠ 0)).card := by
      rw [Finset.card_filter, Finset.card_filter]
      exact Equiv.sum_comp e (fun k => if x k ≠ 0 then 1 else 0)
    rw [this]; exact hx2
  · intro i
    have : ∑ j, A i j * (x (e j) : ℝ) = ∑ k, A i (e.symm k) * (x k : ℝ) := by
      rw [← Equiv.sum_comp e.symm]
      simp
    rw [this]; exact hx3 i

lemma log_ge (v M : ℕ) (hv : 1 ≤ v) (hvM : v ≤ M) :
    Real.log 2 ≤ Real.log (2 * M / v) := by
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have hvM' : (v:ℝ) ≤ M := by exact_mod_cast hvM
  apply Real.log_le_log (by norm_num)
  rw [le_div_iff₀ hv']
  linarith

lemma log_nonneg' (v M : ℕ) (hv : 1 ≤ v) (hvM : v ≤ M) :
    0 ≤ Real.log (2 * M / v) := by
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have hvM' : (v:ℝ) ≤ M := by exact_mod_cast hvM
  apply Real.log_nonneg
  rw [le_div_iff₀ hv']
  linarith

/-- Key numerical inequality closing the induction. -/
lemma key_ineq (u v M : ℕ) (hv : 1 ≤ v) (hvM : v ≤ M) (huv : 10 * u ≤ 9 * v) :
    (u : ℝ) * (Real.log (2 * M / u) + 20) ≤
      (39 / 40) ^ 2 * ((v : ℝ) * (Real.log (2 * M / v) + 20)) := by
  have hL := log_nonneg' v M hv hvM
  have hv' : (0:ℝ) < v := by exact_mod_cast hv
  have hvM' : (v:ℝ) ≤ M := by exact_mod_cast hvM
  have huv' : (10:ℝ) * u ≤ 9 * v := by exact_mod_cast huv
  rcases Nat.eq_zero_or_pos u with hu | hu
  · subst hu
    simp only [Nat.cast_zero, zero_mul]
    exact mul_nonneg (by norm_num) (mul_nonneg hv'.le (by linarith))
  · have hu' : (0:ℝ) < u := by exact_mod_cast hu
    have hM' : (0:ℝ) < M := by linarith
    have hsplit : Real.log (2 * M / u) = Real.log (2 * M / v) + Real.log (v / u) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have hlog : Real.log (v / u) ≤ v / u - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have hlog' : (u:ℝ) * Real.log (v / u) ≤ v - u := by
      have h1 := mul_le_mul_of_nonneg_left hlog hu'.le
      have h2 : (u:ℝ) * (v / u) = v := by field_simp
      rw [mul_sub, h2] at h1
      linarith
    rw [hsplit]
    nlinarith [mul_le_mul_of_nonneg_right huv' hL, mul_nonneg hv'.le hL]

lemma main (C : ℝ) (hC0 : 0 < C) (hC : PC C) (M : ℕ) :
    ∀ (v : ℕ) (ι : Type) [Fintype ι], Fintype.card ι = v → v ≤ M →
      ∀ A : Fin M → ι → ℝ, (∀ i j, |A i j| ≤ 1) →
      ∃ ε : ι → ℝ, (∀ j, ε j = 1 ∨ ε j = -1) ∧
        ∀ i, |∑ j, A i j * ε j| ≤
          40 * C * Real.sqrt (v * (Real.log (2 * M / v) + 20)) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
  intro ι _ hcard hvM A hA
  rcases Nat.eq_zero_or_pos v with hv0 | hv0
  · subst hv0
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, fun i => ?_⟩
    simp
  · obtain ⟨x, hx1, hx2, hx3⟩ := pc_fintype hC M (by omega) (by omega) A hA
    rw [hcard] at hx2 hx3
    set ι' := {j : ι // x j = 0}
    set u := Fintype.card ι' with hu
    have hu_eq : u = (Finset.univ.filter (fun j => x j = 0)).card := by
      rw [hu, Fintype.card_subtype]
    have hsum_card : (Finset.univ.filter (fun j => x j = 0)).card +
        (Finset.univ.filter (fun j => x j ≠ 0)).card = v := by
      rw [← hcard]
      exact Finset.card_filter_add_card_filter_not _
    have h10 : 10 * u ≤ 9 * v := by omega
    have huv : u < v := by omega
    obtain ⟨ε', hε'1, hε'2⟩ :=
      ih u huv ι' rfl (by omega) (fun i k => A i k.1) (fun i k => hA _ _)
    let ε : ι → ℝ := fun j => if h : x j = 0 then ε' ⟨j, h⟩ else (x j : ℝ)
    refine ⟨ε, ?_, ?_⟩
    · intro j
      by_cases h : x j = 0
      · simp only [ε, dite_eq_left h]; exact hε'1 _
      · simp only [ε, dite_eq_right h]
        have := abs_le.mp (hx1 j)
        have : x j = 1 ∨ x j = -1 := by omega
        rcases this with h' | h'
        · left; rw [h']; norm_num
        · right; rw [h']; norm_num
    · intro i
      have hdecomp : ∑ j, A i j * ε j =
          ∑ j, A i j * (x j : ℝ) + ∑ k : ι', A i k.1 * ε' k := by
        have h1 : ∑ j, A i j * ε j =
            ∑ j, (A i j * (x j : ℝ) + if x j = 0 then A i j * ε j else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases h : x j = 0
          · simp [h]
          · simp [h, ε]
        have h2 : ∑ j, (if x j = 0 then A i j * ε j else 0) = ∑ k : ι', A i k.1 * ε' k := by
          rw [← Finset.sum_filter, Finset.sum_subtype (p := fun j => x j = 0) _ (by simp)]
          apply Finset.sum_congr rfl
          intro k _
          simp only [ε, dite_eq_left k.2]
        rw [h1, Finset.sum_add_distrib, h2]
      rw [hdecomp]
      have hL := log_nonneg' v M hv0 hvM
      have hv' : (0:ℝ) ≤ v := by positivity
      have hY : (0:ℝ) ≤ v * (Real.log (2 * M / v) + 20) := mul_nonneg hv' (by linarith)
      have b1 : |∑ j, A i j * (x j : ℝ)| ≤
          C * Real.sqrt (v * (Real.log (2 * M / v) + 20)) := by
        refine (hx3 i).trans ?_
        apply mul_le_mul_of_nonneg_left _ hC0.le
        apply Real.sqrt_le_sqrt
        nlinarith
      have b2 : |∑ k : ι', A i k.1 * ε' k| ≤
          40 * C * ((39 / 40) * Real.sqrt (v * (Real.log (2 * M / v) + 20))) := by
        refine (hε'2 i).trans ?_
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hk := key_ineq u v M hv0 hvM h10
        calc Real.sqrt (u * (Real.log (2 * M / u) + 20))
            ≤ Real.sqrt ((39 / 40) ^ 2 * ((v : ℝ) * (Real.log (2 * M / v) + 20))) :=
              Real.sqrt_le_sqrt hk
          _ = (39 / 40) * Real.sqrt (v * (Real.log (2 * M / v) + 20)) := by
            rw [Real.sqrt_mul' _ hY, Real.sqrt_sq (by norm_num)]
      calc |∑ j, A i j * (x j : ℝ) + ∑ k : ι', A i k.1 * ε' k|
          ≤ |∑ j, A i j * (x j : ℝ)| + |∑ k : ι', A i k.1 * ε' k| := abs_add_le _ _
        _ ≤ C * Real.sqrt (v * (Real.log (2 * M / v) + 20)) +
            40 * C * ((39 / 40) * Real.sqrt (v * (Real.log (2 * M / v) + 20))) :=
              add_le_add b1 b2
        _ = 40 * C * Real.sqrt (v * (Real.log (2 * M / v) + 20)) := by ring

end ChowlaOpus.SpencerAux

namespace ChowlaOpus

theorem spencerStatement_holds (h : PartialColoringStatement) : SpencerStatement := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨280 * C, by positivity, ?_⟩
  intro M v hv hvM A hA
  obtain ⟨ε, hε1, hε2⟩ :=
    SpencerAux.main C hC0 hC M v (Fin v) (Fintype.card_fin v) hvM A hA
  refine ⟨ε, hε1, fun i => (hε2 i).trans ?_⟩
  have hL2 := SpencerAux.log_ge v M hv hvM
  have hlog2 := Real.log_two_gt_d9
  have hv' : (0:ℝ) ≤ v := by positivity
  have hL : 0 ≤ Real.log (2 * M / v) := by linarith
  calc 40 * C * Real.sqrt (v * (Real.log (2 * M / v) + 20))
      ≤ 40 * C * Real.sqrt (7 ^ 2 * (v * Real.log (2 * M / v))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.sqrt_le_sqrt
        nlinarith [mul_le_mul_of_nonneg_left
          (show (0.6931471803:ℝ) ≤ Real.log (2 * M / v) by linarith) hv']
    _ = 280 * C * Real.sqrt (v * Real.log (2 * M / v)) := by
        rw [Real.sqrt_mul' _ (mul_nonneg hv' hL), Real.sqrt_sq (by norm_num)]
        ring

end ChowlaOpus
