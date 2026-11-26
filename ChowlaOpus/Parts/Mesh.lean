module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.MeshAux

open Finset

/-- Dirichlet sum `∑_{a<L} e(a s)`. -/
noncomputable def dir (L : ℕ) (s : ℝ) : ℂ := ∑ a ∈ range L, ee ((a : ℝ) * s)

/-- Unnormalised Fejér kernel `|∑_{a<L} e(a s)|²`. -/
noncomputable def fej (L : ℕ) (s : ℝ) : ℝ := Complex.normSq (dir L s)

lemma fej_nonneg (L : ℕ) (s : ℝ) : 0 ≤ fej L s := Complex.normSq_nonneg _

lemma fej_eq (L : ℕ) (s : ℝ) :
    (fej L s : ℂ) = ∑ a ∈ range L, ∑ b ∈ range L, ee (((a : ℝ) - b) * s) := by
  rw [fej, ← Complex.mul_conj, dir, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← ee_neg, ← ee_add]; congr 1; ring

lemma ee_natMul (x : ℝ) (i : ℕ) : ee ((i : ℝ) * x) = ee x ^ i := by
  unfold ee
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma sum_ee_int (M : ℕ) (hM : 0 < M) (m : ℤ) (hm : |m| < M) :
    ∑ i ∈ range M, ee ((m : ℝ) * i / M) = if m = 0 then (M : ℂ) else 0 := by
  split_ifs with h
  · subst h; simp [ee_zero]
  · set z := ee ((m : ℝ) / M) with hz
    have hMr : (M : ℝ) ≠ 0 := by positivity
    have hpow : ∀ i : ℕ, ee ((m : ℝ) * i / M) = z ^ i := by
      intro i
      rw [hz, ← ee_natMul]; congr 1; ring
    have hz1 : z ≠ 1 := by
      intro h1
      have hc : Real.cos (2 * π * ((m : ℝ) / M)) = 1 := by
        rw [← ee_re, ← hz, h1, Complex.one_re]
      obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).mp hc
      have hn' : (n : ℝ) * M = m := by
        field_simp at hn
        nlinarith [Real.pi_pos]
      have hn'' : n * (M : ℤ) = m := by exact_mod_cast hn'
      have : n = 0 := by
        by_contra hne
        have h1 : 1 ≤ |n| := Int.one_le_abs hne
        rw [← hn'', abs_mul] at hm
        have : |(M : ℤ)| = M := abs_of_nonneg (by positivity)
        rw [this] at hm
        nlinarith
      apply h
      rw [← hn'', this, zero_mul]
    have hzM : z ^ M = 1 := by
      rw [← hpow, mul_div_assoc, div_self hMr, mul_one, ee_intCast]
    simp_rw [hpow]
    have := geom_sum_mul z M
    rw [hzM, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hz1)

/-- Discrete Fourier coefficients of the Fejér-type kernel on a mesh of `M` points. -/
lemma key (L M d : ℕ) (hM : 0 < M) (h : d + L ≤ M) (t : ℝ) :
    ∑ i ∈ range M, ee ((d : ℝ) * ((i : ℝ) / M)) * (fej L (t - i / M) : ℂ)
      = (((M : ℝ) * ((L - d : ℕ) : ℝ) : ℝ) : ℂ) * ee ((d : ℝ) * t) := by
  simp_rw [fej_eq, Finset.mul_sum]
  have step : ∀ i a b : ℕ, ee ((d : ℝ) * ((i : ℝ) / M)) * ee (((a : ℝ) - b) * (t - i / M)) =
      ee (((a : ℝ) - b) * t) * ee ((((d : ℤ) - a + b : ℤ) : ℝ) * i / M) := by
    intro i a b; rw [← ee_add, ← ee_add]; congr 1; push_cast; ring
  simp_rw [step]
  rw [Finset.sum_comm]
  have inner : ∀ a ∈ range L, ∑ i ∈ range M, ∑ b ∈ range L,
      ee (((a : ℝ) - b) * t) * ee ((((d : ℤ) - a + b : ℤ) : ℝ) * i / M) =
      ∑ b ∈ range L, if a = b + d then (M : ℂ) * ee ((d : ℝ) * t) else 0 := by
    intro a ha
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [← Finset.mul_sum]
    have hab : |((d : ℤ) - a + b : ℤ)| < M := by
      simp only [Finset.mem_range] at ha hb
      rw [abs_lt]; constructor <;> omega
    rw [sum_ee_int M hM _ hab]
    by_cases hc : a = b + d
    · subst hc
      have : ((d : ℤ) - ((b + d : ℕ) : ℤ) + b : ℤ) = 0 := by push_cast; ring
      simp only [this, ↓reduceIte]
      push_cast
      rw [mul_comm]; congr 2; ring
    · have : ((d : ℤ) - (a : ℤ) + b : ℤ) ≠ 0 := by omega
      simp only [this, hc, ↓reduceIte, mul_zero]
  rw [Finset.sum_congr rfl inner, Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq', Finset.mem_range]
  rw [← Finset.sum_filter, Finset.sum_const]
  have hf : (range L).filter (fun b => b + d < L) = range (L - d) := by
    ext b; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hf, Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

lemma key_re (L M d : ℕ) (hM : 0 < M) (h : d + L ≤ M) (t : ℝ) :
    ∑ i ∈ range M, Real.cos (2 * π * d * ((i : ℝ) / M)) * fej L (t - i / M)
      = (M : ℝ) * ((L - d : ℕ) : ℝ) * Real.cos (2 * π * d * t) := by
  have := congrArg Complex.re (key L M d hM h t)
  rw [Complex.re_sum] at this
  simp only [Complex.re_mul_ofReal, Complex.re_ofReal_mul, ee_re] at this
  have e1 : ∀ x : ℝ, 2 * π * d * x = 2 * π * (d * x) := fun x => by ring
  simp_rw [e1]
  exact this

lemma key0 (L M : ℕ) (hM : 0 < M) (h : L ≤ M) (t : ℝ) :
    ∑ i ∈ range M, fej L (t - i / M) = (M : ℝ) * L := by
  have := key_re L M 0 hM (by omega) t
  simpa using this

end ChowlaOpus.MeshAux

namespace ChowlaOpus

open Finset MeshAux

theorem meshStatement_holds : MeshStatement := by
  refine ⟨4, by norm_num, ?_⟩
  intro N M c E hKM hM hmesh t
  have hE : 0 ≤ E := (abs_nonneg _).trans (hmesh 0 hM)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp; linarith
  set P : ℝ → ℝ := fun x => ∑ d ∈ Finset.Icc 1 N, c d * Real.cos (2 * Real.pi * d * x) with hP
  set W : ℝ → ℝ := fun s => fej (3 * N) s - fej N s with hW
  have h3 : ∀ d ∈ Icc 1 N, ∑ i ∈ range M, Real.cos (2 * π * d * ((i : ℝ) / M)) *
      W (t - i / M) = M * (2 * N) * Real.cos (2 * π * d * t) := by
    intro d hd
    simp only [Finset.mem_Icc] at hd
    simp only [hW, mul_sub, Finset.sum_sub_distrib]
    rw [key_re (3 * N) M d hM (by omega) t, key_re N M d hM (by omega) t,
      Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  have hsum : (M : ℝ) * (2 * N) * P t = ∑ i ∈ range M, P (i / M) * W (t - i / M) := by
    calc (M : ℝ) * (2 * N) * P t
        = ∑ d ∈ Icc 1 N, c d * ((M : ℝ) * (2 * N) * Real.cos (2 * π * d * t)) := by
          rw [hP, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          ring
      _ = ∑ d ∈ Icc 1 N, c d * ∑ i ∈ range M, Real.cos (2 * π * d * ((i : ℝ) / M)) *
            W (t - i / M) := by
          refine Finset.sum_congr rfl fun d hd => ?_
          rw [h3 d hd]
      _ = ∑ i ∈ range M, P (i / M) * W (t - i / M) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hP, Finset.sum_mul]
          refine Finset.sum_congr rfl fun d _ => ?_
          ring
  have hbound : |∑ i ∈ range M, P (i / M) * W (t - i / M)| ≤
      ∑ i ∈ range M, E * (fej (3 * N) (t - i / M) + fej N (t - i / M)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    rw [abs_mul]
    have hi' : i < M := Finset.mem_range.mp hi
    have h1 : |P (i / M)| ≤ E := hmesh i hi'
    have h2 : |W (t - i / M)| ≤ fej (3 * N) (t - i / M) + fej N (t - i / M) := by
      have := fej_nonneg (3 * N) (t - i / M)
      have := fej_nonneg N (t - i / M)
      rw [hW, abs_le]; constructor <;> linarith
    calc |P (i / M)| * |W (t - i / M)| ≤ E * |W (t - i / M)| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hE
  rw [← Finset.mul_sum, Finset.sum_add_distrib, key0 (3 * N) M hM (by omega) t,
    key0 N M hM (by omega) t, ← hsum, abs_mul] at hbound
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : (0 : ℝ) < M * (2 * N) := by positivity
  rw [abs_of_pos hpos] at hbound
  have : (M : ℝ) * (2 * N) * |P t| ≤ (M * (2 * N)) * (2 * E) := by
    push_cast at hbound; nlinarith
  exact le_of_mul_le_mul_left this hpos

end ChowlaOpus
