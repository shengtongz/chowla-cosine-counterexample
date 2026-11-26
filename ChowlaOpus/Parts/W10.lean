module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.W10Aux

lemma summable_inv_one_add_sq : Summable (fun k : ℤ => 1 / (1 + (k:ℝ)^2)) := by
  refine Summable.of_norm_bounded (((summable_one_div_int_pow (p := 2)).mpr one_lt_two).add
    (hasSum_ite_eq (0:ℤ) (1:ℝ)).summable) ?_
  intro k
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  by_cases hk : k = 0
  · subst hk; simp
  · simp only [hk, ite_false, add_zero]
    have : (0:ℝ) < (k:ℝ)^2 := by
      have : (k:ℝ) ≠ 0 := by exact_mod_cast hk
      positivity
    exact one_div_le_one_div_of_le this (by linarith)

/-- `∑_{k ∈ ℤ} 1/(1+k²)`. -/
noncomputable def S0 : ℝ := ∑' k : ℤ, 1 / (1 + (k:ℝ)^2)

lemma hasSum_S0 : HasSum (fun k : ℤ => 1 / (1 + (k:ℝ)^2)) S0 :=
  summable_inv_one_add_sq.hasSum

lemma S0_nonneg : 0 ≤ S0 := tsum_nonneg (fun k => by positivity)

lemma norm_chi {p : ℕ} (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ) {d : ℤ}
    (hd : ¬ (p:ℤ) ∣ d) : ‖χ (d : ZMod (p^2))‖ = 1 := by
  have hu : IsUnit (d : ZMod (p^2)) := by
    rw [ZMod.isUnit_intCast_iff_isCoprime]
    have hpz : Prime (p:ℤ) := Nat.prime_iff_prime_int.mp hp
    have : IsCoprime (p:ℤ) d := (Prime.coprime_iff_not_dvd hpz).mpr hd
    push_cast
    exact this.pow_left
  obtain ⟨u, hu⟩ := hu
  rw [← hu]
  have h1 : χ (u : ZMod (p^2)) ^ (orderOf u) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one]
  have hpos : 0 < orderOf u := orderOf_pos u
  have h2 : ‖χ (u : ZMod (p^2))‖ ^ (orderOf u) = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').mp h2

lemma exists_ee {c : ℂ} (hc : ‖c‖ = 1) : ∃ z : ℝ, c = ee z := by
  refine ⟨Complex.arg c / (2 * Real.pi), ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I c
  rw [hc, Complex.ofReal_one, one_mul] at h
  rw [ee]
  conv_lhs => rw [← h]
  congr 1
  have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

lemma hcs_of {E : Type*} [Zero E] {T : ℝ} {g : ℝ → E} (hg : ∀ x, T^2 < |x| → g x = 0) :
    HasCompactSupport g := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -T^2) (b := T^2))
  intro x hx
  apply hg
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  exact lt_abs.mpr (hx.elim (fun h => Or.inr (by linarith)) (fun h => Or.inl h))

/-- Lattice sums `m ∑_j 𝓕f(mj)` are `m 𝓕f(0) + O(K)`. -/
lemma lattice_bound {f : ℝ → ℂ} {Kf : ℝ} (hKf0 : 0 ≤ Kf) (hKf : ∀ y, ‖𝓕 f y‖ ≤ Kf / (1 + y^2))
    {m : ℕ} (hm : 1 ≤ m) :
    Summable (fun k : ℤ => if (m:ℤ) ∣ k then 𝓕 f k else 0) ∧
    ‖(m:ℂ) * (∑' k : ℤ, if (m:ℤ) ∣ k then 𝓕 f k else 0) - (m:ℂ) * 𝓕 f 0‖ ≤ 2 * Kf * S0 := by
  have hdom : ∀ k : ℤ, ‖if (m:ℤ) ∣ k then 𝓕 f k else 0‖ ≤ Kf * (1 / (1 + (k:ℝ)^2)) := by
    intro k
    split_ifs
    · rw [mul_one_div]; exact hKf k
    · rw [norm_zero]; positivity
  have hsum : Summable (fun k : ℤ => if (m:ℤ) ∣ k then 𝓕 f k else 0) :=
    Summable.of_norm_bounded (hasSum_S0.summable.mul_left Kf) hdom
  refine ⟨hsum, ?_⟩
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hinj : Function.Injective (fun j : ℤ => (m:ℤ) * j) := by
    intro a b h
    have hm0 : (m:ℤ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    exact mul_left_cancel₀ hm0 h
  have hre : (∑' j : ℤ, 𝓕 f ((m:ℝ) * (j:ℝ))) =
      ∑' k : ℤ, if (m:ℤ) ∣ k then 𝓕 f k else 0 := by
    rw [← hinj.tsum_eq (f := fun k : ℤ => if (m:ℤ) ∣ k then 𝓕 f k else 0)]
    · refine tsum_congr (fun j => ?_)
      rw [ite_eq_left (dvd_mul_right _ _)]
      push_cast; rfl
    · intro k hk
      rw [Function.mem_support] at hk
      split_ifs at hk with h
      · obtain ⟨j, rfl⟩ := h; exact ⟨j, rfl⟩
      · exact absurd rfl hk
  rw [← hre]
  have hdom2 : ∀ j : ℤ, ‖𝓕 f ((m:ℝ) * (j:ℝ))‖ ≤ Kf * (1 / (1 + (j:ℝ)^2)) := by
    intro j
    refine (hKf _).trans ?_
    rw [mul_one_div]
    apply div_le_div_of_nonneg_left hKf0 (by positivity)
    have : (j:ℝ)^2 ≤ ((m:ℝ) * j)^2 := by
      rw [mul_pow]
      exact le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ hm1)
    linarith
  have hs2 : Summable (fun j : ℤ => 𝓕 f ((m:ℝ) * (j:ℝ))) :=
    Summable.of_norm_bounded (hasSum_S0.summable.mul_left Kf) hdom2
  have hH : HasSum (fun j : ℤ => (m:ℂ) * (𝓕 f ((m:ℝ) * (j:ℝ)) - if j = 0 then 𝓕 f 0 else 0))
      ((m:ℂ) * (∑' j : ℤ, 𝓕 f ((m:ℝ) * (j:ℝ))) - (m:ℂ) * 𝓕 f 0) := by
    rw [← mul_sub]
    exact (hs2.hasSum.sub (hasSum_ite_eq (0:ℤ) (𝓕 f 0))).mul_left (m:ℂ)
  refine hH.norm_le_of_bounded (hasSum_S0.mul_left (2 * Kf)) (fun j => ?_)
  by_cases hj : j = 0
  · subst hj
    have e : (m:ℂ) * (𝓕 f ((m:ℝ) * ((0:ℤ):ℝ)) - if (0:ℤ) = 0 then 𝓕 f 0 else 0) = 0 := by simp
    rw [e, norm_zero]
    exact mul_nonneg (by linarith) (by positivity)
  · simp only [hj, ite_false, sub_zero]
    rw [norm_mul, Complex.norm_natCast]
    have hj1 : (1:ℝ) ≤ (j:ℝ)^2 := by
      have h := Int.one_le_abs hj
      have h' : (1:ℝ) ≤ |(j:ℝ)| := by exact_mod_cast h
      rw [← sq_abs]; nlinarith
    calc (m:ℝ) * ‖𝓕 f ((m:ℝ) * (j:ℝ))‖ ≤ m * (Kf / (1 + ((m:ℝ) * j)^2)) := by
          gcongr; exact hKf _
      _ = Kf * (m / (1 + ((m:ℝ) * j)^2)) := by ring
      _ ≤ Kf * (2 / (1 + (j:ℝ)^2)) := by
          apply mul_le_mul_of_nonneg_left _ hKf0
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          have h1 : (m:ℝ) ≤ (m:ℝ)^2 * (j:ℝ)^2 := by nlinarith
          have h2 : (m:ℝ) * (j:ℝ)^2 ≤ (m:ℝ)^2 * (j:ℝ)^2 := by nlinarith
          nlinarith
      _ = 2 * Kf * (1 / (1 + (j:ℝ)^2)) := by ring

/-- Poisson summation at `t = 0`. -/
lemma poisson0 (hP : PoissonStatement) {p : ℕ} (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ)
    (n : ℤ) {f : ℝ → ℂ} {Kf : ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hKf : ∀ y, ‖𝓕 f y‖ ≤ Kf / (1 + y^2)) :
    HasSum (fun d : ℤ => if (p:ℤ) ∣ d then 0 else
        f ((d:ℝ) / (p:ℝ)^2) * (χ (d : ZMod (p^2)))^n)
      (∑' k : ℤ, 𝓕 f k * rowSum p χ n k) := by
  obtain ⟨-, h⟩ := hP p hp χ n f Kf hf hfc hKf 0
  simp only [mul_zero, sub_zero, ee_zero, mul_one] at h
  exact h

/-- The row sum expansion `∑_k 𝓕f(k) rowSum(n,k)` equals `[n = 0](p² - p) 𝓕f(0) + O(p)`. -/
lemma row_bound (hR : RowSumStatement) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {χ : MulChar (ZMod (p ^ 2)) ℂ} (hχ : KernelChar p χ) {f : ℝ → ℂ} {Kf : ℝ}
    (hKf0 : 0 ≤ Kf) (hKf : ∀ y, ‖𝓕 f y‖ ≤ Kf / (1 + y^2)) {n : ℤ}
    (hn : n = 0 ∨ ¬ (p:ℤ) ∣ n) :
    ‖(∑' k : ℤ, 𝓕 f k * rowSum p χ n k) -
      (if n = 0 then (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 f 0 else 0)‖ ≤ 5 * p * Kf * S0 := by
  obtain ⟨hRa, hRb, hRc, hRd, -⟩ := hR p hp hp2 χ hχ
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hS0 := S0_nonneg
  have hKS : 0 ≤ Kf * S0 := mul_nonneg hKf0 hS0
  by_cases hn0 : n = 0
  · subst hn0
    rw [ite_eq_left rfl]
    have hpp : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.pos
    obtain ⟨hs1, hb1⟩ := lattice_bound hKf0 hKf hpp
    obtain ⟨hs2, hb2⟩ := lattice_bound hKf0 hKf hp.one_lt.le
    have heq : (fun k : ℤ => 𝓕 f k * rowSum p χ 0 k) = fun k =>
        ((p^2 : ℕ) : ℂ) * (if ((p^2:ℕ):ℤ) ∣ k then 𝓕 f k else 0) -
          (p:ℂ) * (if (p:ℤ) ∣ k then 𝓕 f k else 0) := by
      ext k; rw [hRc k]; push_cast; split_ifs <;> ring
    rw [heq, (hs1.mul_left _).tsum_sub (hs2.mul_left _), tsum_mul_left, tsum_mul_left]
    calc _ = ‖(((p^2:ℕ):ℂ) * (∑' k : ℤ, if ((p^2:ℕ):ℤ) ∣ k then 𝓕 f k else 0) -
            ((p^2:ℕ):ℂ) * 𝓕 f 0) -
          ((p:ℂ) * (∑' k : ℤ, if (p:ℤ) ∣ k then 𝓕 f k else 0) - (p:ℂ) * 𝓕 f 0)‖ := by
          congr 1; push_cast; ring
      _ ≤ 2 * Kf * S0 + 2 * Kf * S0 := norm_sub_le_of_le hb1 hb2
      _ ≤ 5 * p * Kf * S0 := by nlinarith
  · rw [ite_eq_right hn0, sub_zero]
    have hn' : ¬ (p:ℤ) ∣ n := hn.resolve_left hn0
    have hbd : ∀ k : ℤ, ‖rowSum p χ n k‖ ≤ p := by
      intro k
      by_cases hk : (p:ℤ) ∣ k
      · rw [hRb n k hn' hk, norm_zero]; positivity
      · rw [hRa n k hn' hk, norm_mul, norm_mul, hRd n hn', norm_zpow, norm_inv, norm_chi hp χ hk]
        simp
    have h1 : ‖∑' k : ℤ, 𝓕 f k * rowSum p χ n k‖ ≤ p * Kf * S0 := by
      refine tsum_of_norm_bounded (hasSum_S0.mul_left (p * Kf)) (fun k => ?_)
      rw [norm_mul]
      calc ‖𝓕 f k‖ * ‖rowSum p χ n k‖ ≤ (Kf / (1 + (k:ℝ)^2)) * p :=
            mul_le_mul (hKf k) (hbd k) (norm_nonneg _) (by positivity)
        _ = p * Kf * (1 / (1 + (k:ℝ)^2)) := by ring
    calc _ ≤ p * Kf * S0 := h1
      _ ≤ 5 * p * Kf * S0 := by nlinarith

/-- The exponent `n_v = L · v`. -/
def nL {k : ℕ} (L : Fin (k + 1) → ℤ) (v : Fin (k + 1) → ℤ) : ℤ := ∑ i, L i * v i

lemma nL_neg {k : ℕ} (L v : Fin (k + 1) → ℤ) : nL L (-v) = - nL L v := by
  simp [nL, Finset.sum_neg_distrib]

lemma nL_zero {k : ℕ} (L : Fin (k + 1) → ℤ) : nL L 0 = 0 := by
  simp [nL]

/-- The summand `[p ∤ d] f(d/p²) χ(d)^n`. -/
noncomputable def gfun (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) (n : ℤ) (f : ℝ → ℂ) (d : ℤ) : ℂ :=
  if (p:ℤ) ∣ d then 0 else f ((d:ℝ) / (p:ℝ)^2) * (χ (d : ZMod (p^2)))^n

section Weights

variable {k : ℕ} {T K : ℝ} {S : Finset (Fin (k + 1) → ℤ)} {cf : (Fin (k + 1) → ℤ) → ℝ → ℂ}

lemma wgt_eq (L : Fin (k + 1) → ℤ) (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) (d : ℤ) :
    wgt S cf L p χ d = (∑ v ∈ S, gfun p χ (nL L v) (cf v) d).re := by
  unfold wgt gfun
  by_cases hd : (p:ℤ) ∣ d
  · simp [hd]
  · simp only [hd, ite_false]
    rfl

lemma wgt_sq_eq (hS : IsProfile T S cf K (T ^ 2)) (L : Fin (k + 1) → ℤ) {p : ℕ}
    (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ) (d : ℤ) :
    (wgt S cf L p χ d) ^ 2 =
      (∑ v ∈ S, ∑ w ∈ S, gfun p χ (nL L v + nL L w) (fun x => cf v x * cf w x) d).re := by
  unfold wgt gfun
  by_cases hd : (p:ℤ) ∣ d
  · simp [hd]
  · simp only [hd, ite_false]
    set x := (d:ℝ) / (p:ℝ)^2
    set c := χ (d : ZMod (p^2)) with hcdef
    have hc : ‖c‖ = 1 := norm_chi hp χ hd
    have hc0 : c ≠ 0 := by intro h; rw [h, norm_zero] at hc; exact zero_ne_one hc
    obtain ⟨z, hz⟩ := exists_ee hc
    have him : (∑ v ∈ S, cf v x * c ^ (∑ i, L i * v i)).im = 0 := by
      have := (hS.range (fun i => z * L i) x).1
      convert this using 2
      unfold trigEval
      refine Finset.sum_congr rfl (fun v _ => ?_)
      congr 1
      rw [hz, ← ee_mul_intCast]
      congr 1
      dsimp only
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    set A := ∑ v ∈ S, cf v x * c ^ (∑ i, L i * v i) with hA
    have hsq : A.re ^ 2 = (A * A).re := by rw [Complex.mul_re, him]; ring
    rw [hsq, hA, Finset.sum_mul_sum]
    refine congrArg Complex.re
      (Finset.sum_congr rfl (fun v _ => Finset.sum_congr rfl (fun w _ => ?_)))
    simp only [nL]
    rw [zpow_add₀ hc0]; ring

lemma wgt_neg (hS : IsProfile T S cf K (T ^ 2)) (L : Fin (k + 1) → ℤ) {p : ℕ}
    {χ : MulChar (ZMod (p ^ 2)) ℂ} (hχ : KernelChar p χ) (d : ℤ) :
    wgt S cf L p χ (-d) = wgt S cf L p χ d := by
  unfold wgt
  have h1 : ((p:ℤ) ∣ -d) ↔ (p:ℤ) ∣ d := dvd_neg
  have h2 : χ ((-d : ℤ) : ZMod (p^2)) = χ (d : ZMod (p^2)) := by
    rw [Int.cast_neg, neg_eq_neg_one_mul, map_mul, hχ.1, one_mul]
  have h3 : ∀ v, cf v (((-d:ℤ):ℝ) / (p:ℝ)^2) = cf v ((d:ℝ)/(p:ℝ)^2) := by
    intro v; rw [Int.cast_neg, neg_div, hS.even]
  simp only [h1, h2, h3]

lemma wgt_zero (L : Fin (k + 1) → ℤ) (p : ℕ) (χ : MulChar (ZMod (p ^ 2)) ℂ) :
    wgt S cf L p χ 0 = 0 := by
  simp [wgt]

lemma wgt_large (hS : IsProfile T S cf K (T ^ 2)) (L : Fin (k + 1) → ℤ) {p : ℕ}
    (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ) (d : ℤ)
    (hd : (p:ℝ)^2 * T^2 < |(d:ℝ)|) : wgt S cf L p χ d = 0 := by
  unfold wgt
  split_ifs
  · rfl
  have hP : (0:ℝ) < (p:ℝ)^2 := by have := hp.pos; positivity
  have : ∀ v, cf v ((d:ℝ)/(p:ℝ)^2) = 0 := fun v => hS.supp v _ (by
    rw [abs_div, abs_of_pos hP, lt_div_iff₀ hP, mul_comm]; exact hd)
  simp [this]

end Weights

lemma sum_Icc_half {u : ℤ → ℝ} {s : ℝ} {N : ℕ} (hs : HasSum u s) (heven : ∀ d, u (-d) = u d)
    (h0 : u 0 = 0) (hN : ∀ n : ℕ, N < n → u n = 0) :
    ∑ d ∈ Finset.Icc 1 N, u d = s / 2 := by
  have e : ∀ n : ℕ, u n + u (-n) = 2 * u n := by intro n; rw [heven]; ring
  have h1 := hs.nat_add_neg
  rw [h0, add_zero] at h1
  have h2 : HasSum (fun n : ℕ => u n + u (-n)) (∑ n ∈ Finset.Icc 1 N, (u n + u (-(n:ℤ)))) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · have : n = 0 := by omega
      subst this; simp [h0]
    · rw [heven, hN n hn]; ring
  simp only [e] at h1 h2
  rw [← Finset.mul_sum] at h2
  have := h1.unique h2
  linarith

end ChowlaOpus.W10Aux

namespace ChowlaOpus

open W10Aux in
theorem w10Statement_holds (hR : RowSumStatement) (hP : PoissonStatement)
    (hD : FourierDecayStatement) : W10Statement := by
  intro k T K S cf hS hT L hL
  have hcont : ∀ v, Continuous (cf v) := fun v => (hS.smooth v).continuous
  have hcsv : ∀ v, HasCompactSupport (cf v) := fun v => hcs_of (hS.supp v)
  have hK0 : 0 ≤ K := by
    have h := hS.decay 0 0
    rw [show (1:ℝ) + 0^2 = 1 by norm_num, div_one] at h
    exact (norm_nonneg _).trans h
  have hpair : ∀ v w, ∃ Kp : ℝ, 0 ≤ Kp ∧
      ∀ y, ‖𝓕 (fun x => cf v x * cf w x) y‖ ≤ Kp / (1 + y^2) := fun v w =>
    hD _ ((hS.smooth v).mul (hS.smooth w))
      (hcs_of (fun x hx => by rw [hS.supp v x hx, zero_mul]))
  choose Kp hKp0 hKp using hpair
  have hS0 := S0_nonneg
  refine ⟨(S.card * (5 * K * S0)) / 2 + (∑ v ∈ S, ∑ w ∈ S, 5 * Kp v w * S0) / 2, ?_⟩
  intro p hp hp2 hn χ hχ N hN
  have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp0 : (0:ℝ) ≤ p := by positivity
  -- arithmetic of the exponents `n_v`
  have hlt : ∀ m : ℤ, m ≠ 0 → |m| < p → ¬ (p:ℤ) ∣ m := fun m hm hlt hdvd =>
    hm (Int.eq_zero_of_abs_lt_dvd hdvd hlt)
  have hnL0 : ∀ v ∈ S, nL L v = 0 ↔ v = 0 := by
    intro v hv
    constructor
    · intro h
      refine hL v hv 0 hS.zero_mem ?_
      have h0 := nL_zero L
      unfold nL at h h0
      rw [h, h0]
    · rintro rfl; exact nL_zero L
  have hpair0 : ∀ v ∈ S, ∀ w ∈ S, nL L v + nL L w = 0 ↔ w = -v := by
    intro v hv w hw
    constructor
    · intro h
      refine hL w hw (-v) (hS.neg_mem v hv) ?_
      have h1 := nL_neg L v
      unfold nL at h h1
      rw [h1]; linarith
    · rintro rfl; rw [nL_neg]; ring
  have hdivv : ∀ v ∈ S, nL L v = 0 ∨ ¬ (p:ℤ) ∣ nL L v := by
    intro v hv
    by_cases h : nL L v = 0
    · exact Or.inl h
    · right
      apply hlt _ h
      have h1 : 2 * |nL L v| < (p:ℤ) := hn v hv
      linarith [abs_nonneg (nL L v)]
  have hdivvw : ∀ v ∈ S, ∀ w ∈ S, nL L v + nL L w = 0 ∨ ¬ (p:ℤ) ∣ (nL L v + nL L w) := by
    intro v hv w hw
    by_cases h : nL L v + nL L w = 0
    · exact Or.inl h
    · right
      apply hlt _ h
      have h1 : 2 * |nL L v| < (p:ℤ) := hn v hv
      have h2 : 2 * |nL L w| < (p:ℤ) := hn w hw
      have := abs_add_le (nL L v) (nL L w)
      linarith [abs_nonneg (nL L v), abs_nonneg (nL L w)]
  -- Poisson summation for the first and second moments
  have hmass : HasSum (fun d : ℤ => wgt S cf L p χ d)
      (∑ v ∈ S, ∑' k : ℤ, 𝓕 (cf v) k * rowSum p χ (nL L v) k).re := by
    have h := hasSum_sum (fun v (_ : v ∈ S) =>
      poisson0 hP hp χ (nL L v) (hcont v) (hcsv v) (hS.decay v))
    convert Complex.hasSum_re h using 1
    ext d; rw [wgt_eq]; rfl
  have hsq : HasSum (fun d : ℤ => (wgt S cf L p χ d) ^ 2)
      (∑ v ∈ S, ∑ w ∈ S, ∑' k : ℤ, 𝓕 (fun x => cf v x * cf w x) k *
        rowSum p χ (nL L v + nL L w) k).re := by
    have h := hasSum_sum (fun v (_ : v ∈ S) => hasSum_sum (fun w (_ : w ∈ S) =>
      poisson0 (f := fun x => cf v x * cf w x) hP hp χ (nL L v + nL L w)
        ((hcont v).mul (hcont w))
        (hcs_of (fun x hx => by rw [hS.supp v x hx, zero_mul])) (hKp v w)))
    convert Complex.hasSum_re h using 1
    ext d; rw [wgt_sq_eq hS L hp χ d]; rfl
  -- folding the sums over `ℤ` to `1 ≤ d ≤ N`
  have hlarge : ∀ n : ℕ, N < n → (p:ℝ)^2 * T^2 < |((n:ℤ):ℝ)| := by
    intro n hn'
    have : (N:ℝ) < n := by exact_mod_cast hn'
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg _)]; linarith
  have hsum1 := sum_Icc_half (N := N) hmass (wgt_neg hS L hχ) (wgt_zero L p χ)
    (fun n hn' => wgt_large hS L hp χ n (hlarge n hn'))
  have hsum2 := sum_Icc_half (N := N) hsq (fun d => by rw [wgt_neg hS L hχ])
    (by rw [wgt_zero]; ring) (fun n hn' => by rw [wgt_large hS L hp χ n (hlarge n hn')]; ring)
  -- main terms
  have hF0 : ∀ f : ℝ → ℂ, 𝓕 f 0 = ∫ x, f x := by
    intro f; rw [fourier_eq_ee]; simp [ee_zero]
  have hint0 : Integrable (fun x => cf 0 x) :=
    (hcont 0).integrable_of_hasCompactSupport (hcsv 0)
  have hintRe : Integrable (fun x => (cf 0 x).re) :=
    (Complex.continuous_re.comp (hcont 0)).integrable_of_hasCompactSupport
      (hcs_of (T := T) (fun x hx => by simp [hS.supp 0 x hx]))
  have hint2 : ∀ v, Integrable (fun x => ‖cf v x‖ ^ 2) := fun v =>
    (show Continuous (fun x => ‖cf v x‖ ^ 2) from
      (hcont v).norm.pow 2).integrable_of_hasCompactSupport
      (hcs_of (T := T) (fun x hx => by rw [hS.supp v x hx, norm_zero]; ring))
  have hI0 : (𝓕 (cf 0) 0).re = ∫ x, (cf 0 x).re := by
    rw [hF0]; exact (integral_re hint0).symm
  have hI2 : (∑ v ∈ S, 𝓕 (fun x => cf v x * cf (-v) x) 0).re =
      ∫ x, ∑ v ∈ S, ‖cf v x‖ ^ 2 := by
    rw [integral_finsetSum _ (fun v _ => hint2 v), Complex.re_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have e : ∀ x, cf v x * cf (-v) x = ((‖cf v x‖ ^ 2 : ℝ) : ℂ) := by
      intro x; rw [hS.conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [hF0, e, integral_complex_ofReal, Complex.ofReal_re]
  -- error terms
  have hP0 : ∀ v ∈ S, ‖(∑' k : ℤ, 𝓕 (cf v) k * rowSum p χ (nL L v) k) -
      (if nL L v = 0 then (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (cf v) 0 else 0)‖ ≤
        5 * p * K * S0 :=
    fun v hv => row_bound hR hp hp2 hχ hK0 (hS.decay v) (hdivv v hv)
  have hmassErr : ‖(∑ v ∈ S, ∑' k : ℤ, 𝓕 (cf v) k * rowSum p χ (nL L v) k) -
      (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (cf 0) 0‖ ≤ S.card * (5 * p * K * S0) := by
    have e : (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (cf 0) 0 = ∑ v ∈ S,
        (if nL L v = 0 then (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (cf v) 0 else 0) := by
      rw [Finset.sum_eq_single 0]
      · rw [ite_eq_left (nL_zero L)]
      · intro v hv hv0; rw [ite_eq_right (fun h => hv0 ((hnL0 v hv).mp h))]
      · intro h; exact absurd hS.zero_mem h
    rw [e, ← Finset.sum_sub_distrib]
    calc _ ≤ ∑ v ∈ S, ‖(∑' k : ℤ, 𝓕 (cf v) k * rowSum p χ (nL L v) k) -
          (if nL L v = 0 then (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (cf v) 0 else 0)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ v ∈ S, 5 * p * K * S0 := Finset.sum_le_sum hP0
      _ = S.card * (5 * p * K * S0) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hP2 : ∀ v ∈ S, ∀ w ∈ S, ‖(∑' k : ℤ, 𝓕 (fun x => cf v x * cf w x) k *
        rowSum p χ (nL L v + nL L w) k) -
      (if nL L v + nL L w = 0 then
        (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (fun x => cf v x * cf w x) 0 else 0)‖ ≤
        5 * p * Kp v w * S0 :=
    fun v hv w hw => row_bound hR hp hp2 hχ (hKp0 v w) (hKp v w) (hdivvw v hv w hw)
  have hsqErr : ‖(∑ v ∈ S, ∑ w ∈ S, ∑' k : ℤ, 𝓕 (fun x => cf v x * cf w x) k *
        rowSum p χ (nL L v + nL L w) k) -
      (((p:ℝ)^2 - p : ℝ) : ℂ) * ∑ v ∈ S, 𝓕 (fun x => cf v x * cf (-v) x) 0‖ ≤
      ∑ v ∈ S, ∑ w ∈ S, 5 * p * Kp v w * S0 := by
    have e : (((p:ℝ)^2 - p : ℝ) : ℂ) * ∑ v ∈ S, 𝓕 (fun x => cf v x * cf (-v) x) 0 =
        ∑ v ∈ S, ∑ w ∈ S, (if nL L v + nL L w = 0 then
          (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (fun x => cf v x * cf w x) 0 else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v hv => ?_)
      rw [Finset.sum_eq_single (-v)]
      · rw [ite_eq_left ((hpair0 v hv (-v) (hS.neg_mem v hv)).mpr rfl)]
      · intro w hw hwv; rw [ite_eq_right (fun h => hwv ((hpair0 v hv w hw).mp h))]
      · intro h; exact absurd (hS.neg_mem v hv) h
    rw [e, ← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun v hv => ?_))
    rw [← Finset.sum_sub_distrib]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun w hw => hP2 v hv w hw))
  -- conclusion
  have hb1 : |∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d -
      ((p:ℝ)^2 - p) / 2 * ∫ x, (cf 0 x).re| ≤ S.card * (5 * p * K * S0) / 2 := by
    rw [hsum1]
    have e : (∑ v ∈ S, ∑' k : ℤ, 𝓕 (cf v) k * rowSum p χ (nL L v) k).re / 2 -
        ((p:ℝ)^2 - p) / 2 * ∫ x, (cf 0 x).re =
        ((∑ v ∈ S, ∑' k : ℤ, 𝓕 (cf v) k * rowSum p χ (nL L v) k) -
          (((p:ℝ)^2 - p : ℝ) : ℂ) * 𝓕 (cf 0) 0).re / 2 := by
      rw [Complex.sub_re, Complex.re_ofReal_mul, hI0]; ring
    rw [e, abs_div, abs_two]
    gcongr
    exact (Complex.abs_re_le_norm _).trans hmassErr
  have hb2 : |∑ d ∈ Finset.Icc 1 N, (wgt S cf L p χ d) ^ 2 -
      ((p:ℝ)^2 - p) / 2 * ∫ x, ∑ v ∈ S, ‖cf v x‖ ^ 2| ≤
      (∑ v ∈ S, ∑ w ∈ S, 5 * p * Kp v w * S0) / 2 := by
    rw [hsum2]
    have e : (∑ v ∈ S, ∑ w ∈ S, ∑' k : ℤ, 𝓕 (fun x => cf v x * cf w x) k *
          rowSum p χ (nL L v + nL L w) k).re / 2 -
        ((p:ℝ)^2 - p) / 2 * ∫ x, ∑ v ∈ S, ‖cf v x‖ ^ 2 =
        ((∑ v ∈ S, ∑ w ∈ S, ∑' k : ℤ, 𝓕 (fun x => cf v x * cf w x) k *
          rowSum p χ (nL L v + nL L w) k) -
          (((p:ℝ)^2 - p : ℝ) : ℂ) * ∑ v ∈ S, 𝓕 (fun x => cf v x * cf (-v) x) 0).re / 2 := by
      rw [Complex.sub_re, Complex.re_ofReal_mul, hI2]; ring
    rw [e, abs_div, abs_two]
    gcongr
    exact (Complex.abs_re_le_norm _).trans hsqErr
  have hE2 : 0 ≤ (∑ v ∈ S, ∑ w ∈ S, 5 * Kp v w * S0) / 2 := by
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg (fun v _ => Finset.sum_nonneg (fun w _ => by
      have := hKp0 v w; positivity))
  have hE2' : (∑ v ∈ S, ∑ w ∈ S, 5 * p * Kp v w * S0) =
      p * ∑ v ∈ S, ∑ w ∈ S, 5 * Kp v w * S0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun w _ => by ring)
  constructor
  · calc _ ≤ S.card * (5 * p * K * S0) / 2 := hb1
      _ ≤ _ := by nlinarith [mul_nonneg hp0 hE2]
  · have hsplit : ∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d * (1 - wgt S cf L p χ d) =
        ∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d -
          ∑ d ∈ Finset.Icc 1 N, (wgt S cf L p χ d) ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun d _ => by ring)
    have hint : ∫ x, ((cf 0 x).re - ∑ v ∈ S, ‖cf v x‖ ^ 2) =
        (∫ x, (cf 0 x).re) - ∫ x, ∑ v ∈ S, ‖cf v x‖ ^ 2 :=
      integral_sub hintRe (integrable_finsetSum _ (fun v _ => hint2 v))
    rw [hsplit, hint]
    calc _ = |(∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d -
            ((p:ℝ)^2 - p) / 2 * ∫ x, (cf 0 x).re) -
          (∑ d ∈ Finset.Icc 1 N, (wgt S cf L p χ d) ^ 2 -
            ((p:ℝ)^2 - p) / 2 * ∫ x, ∑ v ∈ S, ‖cf v x‖ ^ 2)| := by
          congr 1; ring
      _ ≤ _ := abs_sub _ _
      _ ≤ S.card * (5 * p * K * S0) / 2 + (∑ v ∈ S, ∑ w ∈ S, 5 * p * Kp v w * S0) / 2 :=
          add_le_add hb1 hb2
      _ = _ := by rw [hE2']; ring

end ChowlaOpus
