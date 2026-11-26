module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.GaussAux

open Finset ChowlaOpus

/-! ### Exponential sums -/

lemma ee_eq_one_iff_int (x : ℝ) : ee x = 1 ↔ ∃ m : ℤ, x = m := by
  unfold ee
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (x : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ h
      linear_combination hn
    exact_mod_cast this
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

lemma ee_geom_sum (N : ℕ) (hN : 0 < N) (k : ℤ) :
    ∑ r ∈ range N, ee ((k : ℝ) * (r : ℝ) / (N : ℝ)) = if (N : ℤ) ∣ k then (N : ℂ) else 0 := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hterm : ∀ r : ℕ, ee ((k : ℝ) * (r : ℝ) / (N : ℝ)) = ee ((k : ℝ) / N) ^ r := by
    intro r
    rw [← zpow_natCast, ← ee_mul_intCast]
    congr 1; push_cast; ring
  simp_rw [hterm]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    have : ee ((((N : ℤ) * m : ℤ) : ℝ) / N) = 1 := by
      rw [show (((N : ℤ) * m : ℤ) : ℝ) / N = (m : ℝ) by push_cast; field_simp]
      exact ee_intCast m
    rw [this]
    simp
  · have hne : ee ((k : ℝ) / N) ≠ 1 := by
      intro h1
      rw [ee_eq_one_iff_int] at h1
      obtain ⟨m, hm⟩ := h1
      apply h
      refine ⟨m, ?_⟩
      have : (k : ℝ) = N * m := by
        rw [div_eq_iff hN'] at hm; rw [hm]; ring
      exact_mod_cast this
    rw [geom_sum_eq hne]
    have : ee ((k : ℝ) / N) ^ N = 1 := by
      rw [← zpow_natCast, ← ee_mul_intCast]
      rw [show (k : ℝ) / N * ((N : ℤ) : ℝ) = (k : ℝ) by push_cast; field_simp]
      exact ee_intCast k
    rw [this, sub_self, zero_div]

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### The additive character mod `p²` -/

/-- The standard additive character `x ↦ e(x/p²)` on `ZMod (p²)`. -/
noncomputable def psi (p : ℕ) (x : ZMod (p ^ 2)) : ℂ := ee ((x.val : ℝ) / (p : ℝ) ^ 2)

lemma psi_intCast (m : ℤ) : psi p (m : ZMod (p ^ 2)) = ee ((m : ℝ) / (p : ℝ) ^ 2) := by
  unfold psi
  have hp0 : ((p : ℝ) ^ 2) ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have h1 : (((m : ZMod (p ^ 2)).val : ℝ)) = ((m % ((p ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) := by
    rw [← Int.cast_natCast, ZMod.val_intCast]
  have h2 : (m : ℝ) = ((m % ((p ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) +
      (p : ℝ) ^ 2 * ((m / ((p ^ 2 : ℕ) : ℤ) : ℤ) : ℝ) := by
    have := Int.emod_add_mul_ediv m ((p ^ 2 : ℕ) : ℤ)
    have h' : ((m % ((p ^ 2 : ℕ) : ℤ) + ((p ^ 2 : ℕ) : ℤ) * (m / ((p ^ 2 : ℕ) : ℤ)) : ℤ) : ℝ) =
        (m : ℝ) := by rw [this]
    push_cast at h' ⊢
    linarith
  rw [h1]
  conv_rhs => rw [h2, add_div, mul_div_cancel_left₀ _ hp0, ee_add_intCast]

lemma psi_add (x y : ZMod (p ^ 2)) : psi p (x + y) = psi p x * psi p y := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective y
  rw [← Int.cast_add, psi_intCast, psi_intCast, psi_intCast, ← ee_add]
  congr 1; push_cast; ring

/-! ### Values of `χ` -/

lemma norm_chi_of_isUnit (χ : MulChar (ZMod (p ^ 2)) ℂ) {x : ZMod (p ^ 2)} (hx : IsUnit x) :
    ‖χ x‖ = 1 := by
  obtain ⟨u, rfl⟩ := hx
  have h1 : (χ u) ^ (p ^ 2).totient = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.pow_totient, Units.val_one, map_one]
  have h2 : ‖χ u‖ ^ (p ^ 2).totient = 1 := by rw [← norm_pow, h1, norm_one]
  have hpos : (p ^ 2).totient ≠ 0 := (Nat.totient_pos.mpr (pow_pos hp.out.pos 2)).ne'
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos).mp h2

lemma isUnit_intCast_of_not_dvd {n : ℤ} (h : ¬ (p : ℤ) ∣ n) : IsUnit (n : ZMod (p ^ 2)) := by
  rw [ZMod.isUnit_intCast_iff_isCoprime]
  push_cast
  exact ((Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp.out)).mpr h).pow_left

omit hp in
lemma chi_neg (χ : MulChar (ZMod (p ^ 2)) ℂ) (hχ : KernelChar p χ) (x : ZMod (p ^ 2)) :
    χ (-x) = χ x := by
  rw [neg_eq_neg_one_mul, map_mul, hχ.1, one_mul]

omit hp in
lemma chi_one_add (χ : MulChar (ZMod (p ^ 2)) ℂ) (hχ : KernelChar p χ) (j : ℕ) :
    χ (1 + (p : ZMod (p ^ 2)) * j) = ee ((j : ℝ) / p) := by
  have := hχ.2 j
  push_cast at this
  exact this

omit hp in
lemma isUnit_one_add (j : ℕ) : IsUnit (1 + (p : ZMod (p ^ 2)) * j) := by
  have hp2 : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  refine IsUnit.of_mul_eq_one (1 - (p : ZMod (p ^ 2)) * j) ?_
  linear_combination (-(j : ZMod (p ^ 2)) ^ 2) * hp2

lemma one_add_injOn : Set.InjOn (fun j : ℕ => 1 + (p : ZMod (p ^ 2)) * j) (range p) := by
  intro a ha b hb h
  have ha' : a < p := Finset.mem_range.mp (Finset.mem_coe.mp ha)
  have hb' : b < p := Finset.mem_range.mp (Finset.mem_coe.mp hb)
  have h' : ((p * a : ℕ) : ZMod (p ^ 2)) = ((p * b : ℕ) : ZMod (p ^ 2)) := by
    push_cast; exact add_left_cancel h
  have hpos := hp.out.pos
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by nlinarith),
    Nat.mod_eq_of_lt (by nlinarith)] at h'
  exact Nat.eq_of_mul_eq_mul_left hpos h'

/-! ### Row sums as sums over `ZMod (p²)` -/

lemma sum_range_eq_sum_zmod (f : ZMod (p ^ 2) → ℂ) :
    ∑ r ∈ range (p ^ 2), f (r : ZMod (p ^ 2)) = ∑ x : ZMod (p ^ 2), f x := by
  refine Finset.sum_nbij' (fun r => (r : ZMod (p ^ 2))) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intros; exact mem_univ _
  · intro x _; exact mem_range.mpr (ZMod.val_lt x)
  · intro r hr; exact ZMod.val_cast_of_lt (mem_range.mp hr)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intros; rfl

lemma rowSum_eq (χ : MulChar (ZMod (p ^ 2)) ℂ) (n k : ℤ) (hn : n ≠ 0) :
    rowSum p χ n k = ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) := by
  unfold rowSum
  rw [Finset.sum_filter_of_ne, ← sum_range_eq_sum_zmod]
  · refine Finset.sum_congr rfl (fun r _ => ?_)
    congr 1
    rw [show ((k : ZMod (p ^ 2)) * (r : ZMod (p ^ 2))) = ((k * (r : ℤ) : ℤ) : ZMod (p ^ 2)) by
      push_cast; ring, psi_intCast]
    push_cast
    ring_nf
  · intro r _ hne
    by_contra hc
    apply hne
    have : ¬ IsUnit (r : ZMod (p ^ 2)) := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff two_pos]; exact hc
    rw [MulChar.map_nonunit χ this, zero_zpow n hn, zero_mul]

/-- Averaging over the kernel `{1 + p j}` of reduction mod `p`. -/
lemma averaged (χ : MulChar (ZMod (p ^ 2)) ℂ) (hχ : KernelChar p χ) (n k : ℤ) :
    (p : ℂ) * ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) =
      ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) *
        (if (p : ℤ) ∣ n + k * (x.val : ℤ) then (p : ℂ) else 0) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hshift : ∀ (j : ℕ) (x : ZMod (p ^ 2)),
      χ (x * (1 + (p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2)))) ^ n *
          psi p ((k : ZMod (p ^ 2)) * (x * (1 + (p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2))))) =
        χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) *
          ee (((n + k * (x.val : ℤ) : ℤ) : ℝ) * (j : ℝ) / (p : ℝ)) := by
    intro j x
    rw [map_mul, chi_one_add χ hχ j, mul_zpow, ← ee_mul_intCast]
    have hxv : ((x.val : ℤ) : ZMod (p ^ 2)) = x := by simp
    have : (k : ZMod (p ^ 2)) * (x * (1 + (p : ZMod (p ^ 2)) * (j : ZMod (p ^ 2)))) =
        (k : ZMod (p ^ 2)) * x + ((k * (x.val : ℤ) * p * j : ℤ) : ZMod (p ^ 2)) := by
      rw [Int.cast_mul, Int.cast_mul, Int.cast_mul, hxv]; push_cast; ring
    rw [this, psi_add, psi_intCast]
    rw [show ((n + k * (x.val : ℤ) : ℤ) : ℝ) * (j : ℝ) / (p : ℝ) =
        (j : ℝ) / p * (n : ℝ) + ((k * (x.val : ℤ) * p * j : ℤ) : ℝ) / (p : ℝ) ^ 2 by
      push_cast; field_simp]
    rw [ee_add]
    ring
  have hsum : ∀ j ∈ range p, ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) =
      ∑ x : ZMod (p ^ 2), χ (x * (1 + (p : ZMod (p ^ 2)) * j)) ^ n *
        psi p ((k : ZMod (p ^ 2)) * (x * (1 + (p : ZMod (p ^ 2)) * j))) := by
    intro j _
    exact (Equiv.sum_comp (Units.mulRight (isUnit_one_add (p := p) j).unit)
      (fun x => χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x))).symm
  have hpS : (p : ℂ) * ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) =
      ∑ j ∈ range p, ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) := by
    rw [sum_const, card_range, nsmul_eq_mul]
  rw [hpS, sum_congr rfl hsum, sum_comm]
  refine sum_congr rfl (fun x _ => ?_)
  rw [sum_congr rfl (fun j _ => hshift j x), ← mul_sum, ee_geom_sum p hp.out.pos]

lemma cond_iff (n k : ℤ) (hn : ¬ (p : ℤ) ∣ n) (u : ZMod (p ^ 2))
    (hu : (k : ZMod (p ^ 2)) * u = -(n : ZMod (p ^ 2))) (y : ZMod (p ^ 2)) :
    (p : ℤ) ∣ n + k * ((u * y).val : ℤ) ↔
      y ∈ (range p).image (fun j : ℕ => 1 + (p : ZMod (p ^ 2)) * j) := by
  set red : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)
    with hred
  have hval : ∀ x : ZMod (p ^ 2), ((x.val : ℤ) : ZMod p) = red x := by
    intro x
    rw [hred, ZMod.castHom_apply, ZMod.cast_eq_val, Int.cast_natCast]
  have hku : (k : ZMod p) * red u = -(n : ZMod p) := by
    rw [← map_intCast red k, ← map_mul, hu, map_neg, map_intCast]
  have hn' : (n : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have step1 : (p : ℤ) ∣ n + k * ((u * y).val : ℤ) ↔ red y = 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add, Int.cast_mul, hval, map_mul]
    have key : (n : ZMod p) + (k : ZMod p) * (red u * red y) = (n : ZMod p) * (1 - red y) := by
      linear_combination (red y) * hku
    rw [key, mul_eq_zero, sub_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h hn'
      · exact h.symm
    · intro h; right; exact h.symm
  rw [step1, mem_image]
  constructor
  · intro hy
    have h1 : y.val % p = 1 := by
      have : ((y.val : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
        have := hval y
        rw [Int.cast_natCast] at this
        rw [this, hy, Nat.cast_one]
      rw [ZMod.natCast_eq_natCast_iff'] at this
      rw [this, Nat.mod_eq_of_lt hp.out.one_lt]
    refine ⟨y.val / p, ?_, ?_⟩
    · rw [mem_range, Nat.div_lt_iff_lt_mul hp.out.pos, ← pow_two]
      exact ZMod.val_lt y
    · have := Nat.mod_add_div y.val p
      rw [h1] at this
      conv_rhs => rw [← ZMod.natCast_zmod_val y, ← this]
      push_cast
      ring
  · rintro ⟨j, _, rfl⟩
    rw [map_add, map_one, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]

lemma rowSum_a (χ : MulChar (ZMod (p ^ 2)) ℂ) (hχ : KernelChar p χ) (n k : ℤ)
    (hn : ¬ (p : ℤ) ∣ n) (hk : ¬ (p : ℤ) ∣ k) :
    rowSum p χ n k = p * ((χ (k : ZMod (p ^ 2)))⁻¹) ^ n * gaussPhase p χ n := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hav := averaged χ hχ n k
  rw [rowSum_eq χ n k hn0]
  have h1 : ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) =
      ∑ x : ZMod (p ^ 2), if (p : ℤ) ∣ n + k * (x.val : ℤ) then
        χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) else 0 := by
    apply mul_left_cancel₀ hpne
    rw [hav, mul_sum]
    refine sum_congr rfl (fun x _ => ?_)
    split_ifs <;> ring
  have hku : IsUnit (k : ZMod (p ^ 2)) := isUnit_intCast_of_not_dvd hk
  have hnu : IsUnit (n : ZMod (p ^ 2)) := isUnit_intCast_of_not_dvd hn
  have hkk : (k : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ = 1 := ZMod.mul_inv_of_unit _ hku
  have hkinv : IsUnit ((k : ZMod (p ^ 2))⁻¹) := IsUnit.of_mul_eq_one_right _ hkk
  obtain ⟨u, hu_def⟩ : ∃ u : ZMod (p ^ 2), u = -(n : ZMod (p ^ 2)) * (k : ZMod (p ^ 2))⁻¹ :=
    ⟨_, rfl⟩
  have hku' : (k : ZMod (p ^ 2)) * u = -(n : ZMod (p ^ 2)) := by
    rw [hu_def]; linear_combination (-(n : ZMod (p ^ 2))) * hkk
  have hu : IsUnit u := by rw [hu_def]; exact hnu.neg.mul hkinv
  have hχk : χ (k : ZMod (p ^ 2)) ≠ 0 := by
    intro h
    have := norm_chi_of_isUnit χ hku
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hχu : χ u = χ (n : ZMod (p ^ 2)) * (χ (k : ZMod (p ^ 2)))⁻¹ := by
    have : χ (k : ZMod (p ^ 2)) * χ u = χ (n : ZMod (p ^ 2)) := by
      rw [← map_mul, hku', chi_neg χ hχ]
    rw [eq_mul_inv_iff_mul_eq₀ hχk, mul_comm]
    exact this
  have h2 : (∑ x : ZMod (p ^ 2), if (p : ℤ) ∣ n + k * (x.val : ℤ) then
        χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) else 0) =
      ∑ y : ZMod (p ^ 2), if (p : ℤ) ∣ n + k * ((u * y).val : ℤ) then
        χ (u * y) ^ n * psi p ((k : ZMod (p ^ 2)) * (u * y)) else 0 :=
    (Equiv.sum_comp (Units.mulLeft hu.unit) (fun x => if (p : ℤ) ∣ n + k * (x.val : ℤ) then
        χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) else 0)).symm
  rw [h1, h2, ← sum_filter]
  have hfilt : univ.filter (fun y : ZMod (p ^ 2) => (p : ℤ) ∣ n + k * ((u * y).val : ℤ)) =
      (range p).image (fun j : ℕ => 1 + (p : ZMod (p ^ 2)) * j) := by
    ext y
    rw [mem_filter, cond_iff n k hn u hku' y]
    simp only [mem_univ, true_and]
  rw [hfilt, sum_image one_add_injOn]
  have hterm : ∀ j ∈ range p, χ (u * (1 + (p : ZMod (p ^ 2)) * j)) ^ n *
      psi p ((k : ZMod (p ^ 2)) * (u * (1 + (p : ZMod (p ^ 2)) * j))) =
      χ (n : ZMod (p ^ 2)) ^ n * (χ (k : ZMod (p ^ 2)))⁻¹ ^ n * ee (-(n : ℝ) / (p : ℝ) ^ 2) := by
    intro j _
    rw [map_mul, chi_one_add χ hχ j, hχu, mul_zpow, mul_zpow, ← ee_mul_intCast]
    rw [show (k : ZMod (p ^ 2)) * (u * (1 + (p : ZMod (p ^ 2)) * j)) =
        ((-n - n * p * j : ℤ) : ZMod (p ^ 2)) by rw [← mul_assoc, hku']; push_cast; ring]
    rw [psi_intCast]
    have he : ee ((j : ℝ) / p * (n : ℝ)) * ee (((-n - n * p * j : ℤ) : ℝ) / (p : ℝ) ^ 2) =
        ee (-(n : ℝ) / (p : ℝ) ^ 2) := by
      rw [← ee_add]; congr 1; push_cast; field_simp; ring
    linear_combination (χ (n : ZMod (p ^ 2)) ^ n * (χ (k : ZMod (p ^ 2)))⁻¹ ^ n) * he
  rw [sum_congr rfl hterm, sum_const, card_range, nsmul_eq_mul]
  unfold gaussPhase
  ring

lemma rowSum_b (χ : MulChar (ZMod (p ^ 2)) ℂ) (hχ : KernelChar p χ) (n k : ℤ)
    (hn : ¬ (p : ℤ) ∣ n) (hk : (p : ℤ) ∣ k) : rowSum p χ n k = 0 := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hav := averaged χ hχ n k
  have hnd : ∀ x : ZMod (p ^ 2), ¬ (p : ℤ) ∣ n + k * (x.val : ℤ) := by
    intro x h
    exact hn ((dvd_add_left (dvd_mul_of_dvd_left hk _)).mp h)
  have h0 : ∑ x : ZMod (p ^ 2), χ x ^ n * psi p ((k : ZMod (p ^ 2)) * x) *
      (if (p : ℤ) ∣ n + k * (x.val : ℤ) then (p : ℂ) else 0) = 0 :=
    sum_eq_zero (fun x _ => by rw [ite_eq_right_of_eq_false _ _ (eq_false (hnd x)), mul_zero])
  rw [h0] at hav
  rw [rowSum_eq χ n k hn0]
  exact (mul_eq_zero.mp hav).resolve_left hpne

lemma rowSum_c (χ : MulChar (ZMod (p ^ 2)) ℂ) (k : ℤ) :
    rowSum p χ 0 k =
      (if (p : ℤ) ^ 2 ∣ k then ((p : ℂ) ^ 2) else 0) - (if (p : ℤ) ∣ k then (p : ℂ) else 0) := by
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  unfold rowSum
  simp only [zpow_zero, one_mul]
  have hfull : ∑ r ∈ range (p ^ 2), ee ((k : ℝ) * (r : ℝ) / (p : ℝ) ^ 2) =
      if (p : ℤ) ^ 2 ∣ k then (p : ℂ) ^ 2 else 0 := by
    have := ee_geom_sum (p ^ 2) (pow_pos hp.out.pos 2) k
    push_cast at this
    exact this
  have hnot : (range (p ^ 2)).filter (fun r => ¬ Nat.Coprime r p) =
      (range p).image (fun m => p * m) := by
    ext r
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hr, hc⟩
      have hd : p ∣ r := by
        by_contra hd
        exact hc (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hd))
      obtain ⟨m, rfl⟩ := hd
      refine ⟨m, ?_, rfl⟩
      by_contra hm
      have : p * p ≤ p * m := Nat.mul_le_mul_left p (not_lt.mp hm)
      rw [← pow_two] at this
      exact absurd hr (not_lt.mpr this)
    · rintro ⟨m, hm, rfl⟩
      have hpos := hp.out.pos
      refine ⟨by nlinarith, ?_⟩
      intro hc
      have h1 : Nat.Coprime p p := Nat.Coprime.coprime_dvd_left (dvd_mul_right p m) hc
      rw [Nat.coprime_self] at h1
      exact hp.out.one_lt.ne' h1
  have hpart : ∑ r ∈ (range (p ^ 2)).filter (fun r => ¬ Nat.Coprime r p),
      ee ((k : ℝ) * (r : ℝ) / (p : ℝ) ^ 2) = if (p : ℤ) ∣ k then (p : ℂ) else 0 := by
    rw [hnot, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.out.pos h),
      ← ee_geom_sum p hp.out.pos k]
    refine sum_congr rfl (fun m _ => ?_)
    congr 1
    push_cast
    field_simp
  rw [← hfull, ← hpart,
    ← Finset.sum_filter_add_sum_filter_not (range (p ^ 2)) (fun r => Nat.Coprime r p)]
  ring

lemma gauss_d (χ : MulChar (ZMod (p ^ 2)) ℂ) (n : ℤ) (hn : ¬ (p : ℤ) ∣ n) :
    ‖gaussPhase p χ n‖ = 1 := by
  unfold gaussPhase
  rw [norm_mul, norm_ee, norm_zpow, norm_chi_of_isUnit χ (isUnit_intCast_of_not_dvd hn),
    one_zpow, one_mul]

lemma conj_chi_zpow (χ : MulChar (ZMod (p ^ 2)) ℂ) (x : ZMod (p ^ 2)) (n : ℤ) :
    starRingEnd ℂ (χ x ^ n) = χ x ^ (-n) := by
  by_cases hx : IsUnit x
  · have h1 := norm_chi_of_isUnit χ hx
    have hconj : starRingEnd ℂ (χ x) = (χ x)⁻¹ := by
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1]; simp
    rw [map_zpow₀, hconj, inv_zpow']
  · rw [MulChar.map_nonunit χ hx, map_zpow₀, map_zero]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [zero_zpow _ hn, zero_zpow _ (neg_ne_zero.mpr hn)]

lemma gauss_e (χ : MulChar (ZMod (p ^ 2)) ℂ) (hχ : KernelChar p χ) (n : ℤ) :
    gaussPhase p χ (-n) = starRingEnd ℂ (gaussPhase p χ n) := by
  unfold gaussPhase
  rw [map_mul, ← ee_neg, conj_chi_zpow]
  simp only [Int.cast_neg]
  rw [chi_neg χ hχ]
  congr 2
  ring

end ChowlaOpus.GaussAux

namespace ChowlaOpus

open GaussAux in
theorem rowSumStatement_holds : RowSumStatement := by
  intro p hp _ χ hχ
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨fun n k hn hk => rowSum_a χ hχ n k hn hk, fun n k hn hk => rowSum_b χ hχ n k hn hk,
    fun k => rowSum_c χ k, fun n hn => gauss_d χ n hn, fun n => gauss_e χ hχ n⟩

end ChowlaOpus
