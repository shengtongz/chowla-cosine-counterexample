module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.PhaseAux

open Finset ComplexConjugate

/-! ### Generalities on characters -/

lemma norm_apply_of_isUnit {R : Type*} [CommRing R] [Finite Rˣ] (χ : MulChar R ℂ) {a : R}
    (ha : IsUnit a) : ‖χ a‖ = 1 := by
  cases nonempty_fintype Rˣ
  have : NeZero (Fintype.card Rˣ) := ⟨Fintype.card_ne_zero⟩
  obtain ⟨u, rfl⟩ := ha
  rw [← MulChar.coe_equivToUnitHom]
  exact Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)

lemma conj_apply {p : ℕ} [Fact p.Prime] (χ : MulChar (ZMod p) ℂ) (a : ZMod p) :
    conj (χ a) = χ a⁻¹ := by
  rw [← MulChar.inv_apply', ← MulChar.star_apply']; rfl

lemma mul_conj_eq_one (v : ℂ) (hv : ‖v‖ = 1) : v * conj v = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]; norm_num

lemma natCast_ne_zero_of_lt {p n : ℕ} (hn : 0 < n) (hnp : n < p) : (n : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have := Nat.le_of_dvd hn h
  omega

/-- Lift of a character mod `p` to a character mod `p²` through reduction mod `p`. -/
noncomputable def lift (p : ℕ) [Fact p.Prime] (ξ : MulChar (ZMod p) ℂ) :
    MulChar (ZMod (p ^ 2)) ℂ where
  toFun a := ξ (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) a)
  map_one' := by simp
  map_mul' a b := by simp
  map_nonunit' a ha := by
    apply MulChar.map_nonunit
    intro hu
    apply ha
    have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Fact.out : p.Prime).ne_zero⟩
    obtain ⟨v, rfl⟩ : ∃ v : ℕ, (v : ZMod (p ^ 2)) = a := ⟨a.val, ZMod.natCast_zmod_val a⟩
    rw [map_natCast, ZMod.isUnit_iff_coprime] at hu
    rw [ZMod.isUnit_iff_coprime]
    exact Nat.Coprime.pow_right 2 hu

lemma lift_apply (p : ℕ) [Fact p.Prime] (ξ : MulChar (ZMod p) ℂ) (a : ZMod (p ^ 2)) :
    lift p ξ a = ξ (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p) a) := rfl

lemma gaussPhase_mul_lift (p : ℕ) [Fact p.Prime] (χ₀ : MulChar (ZMod (p ^ 2)) ℂ)
    (ξ : MulChar (ZMod p) ℂ) (m : ℕ) :
    gaussPhase p (χ₀ * lift p ξ) (m : ℤ) =
      gaussPhase p χ₀ (m : ℤ) * ξ ((m ^ m : ℕ) : ZMod p) := by
  unfold gaussPhase
  rw [MulChar.mul_apply, mul_zpow, lift_apply]
  simp only [Int.cast_natCast, map_natCast, zpow_natCast, Nat.cast_pow, map_pow]
  ring

lemma kernelChar_mul_lift (p : ℕ) [Fact p.Prime] (χ₀ : MulChar (ZMod (p ^ 2)) ℂ)
    (hχ₀ : KernelChar p χ₀) (ψ : MulChar (ZMod p) ℂ) :
    KernelChar p (χ₀ * lift p (ψ * ψ)) := by
  obtain ⟨h1, h2⟩ := hχ₀
  refine ⟨?_, fun t => ?_⟩
  · rw [MulChar.mul_apply, h1, lift_apply, map_neg, map_one, MulChar.mul_apply, ← map_mul]
    norm_num
  · rw [MulChar.mul_apply, h2, lift_apply, map_intCast]
    have : (((1 + (p : ℤ) * t : ℤ)) : ZMod p) = 1 := by
      push_cast; rw [ZMod.natCast_self]; ring
    rw [this, map_one, mul_one]

lemma norm_gaussPhase (p : ℕ) [Fact p.Prime] (χ : MulChar (ZMod (p ^ 2)) ℂ) (m : ℕ)
    (hm0 : 0 < m) (hmp : m < p) : ‖gaussPhase p χ (m : ℤ)‖ = 1 := by
  have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 (Fact.out : p.Prime).ne_zero⟩
  have hu : IsUnit ((m : ℤ) : ZMod (p ^ 2)) := by
    rw [Int.cast_natCast, ZMod.isUnit_iff_coprime]
    apply Nat.Coprime.pow_right
    exact ((Nat.Prime.coprime_iff_not_dvd Fact.out).2
      (fun h => absurd (Nat.le_of_dvd hm0 h) (by omega))).symm
  unfold gaussPhase
  rw [norm_mul, norm_ee, norm_zpow, norm_apply_of_isUnit χ hu, one_zpow, one_mul]

lemma multIndep_pow {ι : Type} [Fintype ι] (n : ι → ℕ) (hn : ∀ i, 0 < n i)
    (h : MultIndep n) : MultIndep (fun i => n i ^ n i) := by
  intro e he
  have := h (fun i => (n i : ℤ) * e i) (by
    rw [← he]
    refine Finset.prod_congr rfl fun i _ => ?_
    push_cast
    rw [zpow_mul, zpow_natCast])
  funext i
  have hi := congrFun this i
  simp only [Pi.zero_apply, mul_eq_zero, Nat.cast_eq_zero] at hi
  rcases hi with hi | hi
  · exact absurd hi (hn i).ne'
  · exact hi

/-! ### Elementary estimates -/

lemma diag_lower (K : ℕ) :
    1 / ((K : ℝ) + 1) ≤ ∑ j ∈ range (K + 1), ((K.choose j : ℝ) ^ 2 / 4 ^ K) := by
  have h1 : (∑ j ∈ range (K + 1), (K.choose j : ℝ)) ^ 2 ≤
      ((range (K + 1)).card : ℝ) * ∑ j ∈ range (K + 1), (K.choose j : ℝ) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2 : ∑ j ∈ range (K + 1), (K.choose j : ℝ) = 2 ^ K := by
    exact_mod_cast Nat.sum_range_choose K
  have h4 : ((2 : ℝ) ^ K) ^ 2 = 4 ^ K := by rw [sq, ← mul_pow]; norm_num
  rw [h2, card_range, h4] at h1
  rw [← Finset.sum_div, div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast at h1
  linarith

lemma exists_K (d : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ K : ℕ, r ^ K < (1 / ((K : ℝ) + 1)) ^ d := by
  have ht := tendsto_pow_const_mul_const_pow_of_abs_lt_one d (r := r)
    (by rwa [abs_of_nonneg hr0])
  have hev : ∀ᶠ K : ℕ in Filter.atTop, (K : ℝ) ^ d * r ^ K < 1 / 2 ^ d :=
    (tendsto_order.1 ht).2 _ (by positivity)
  obtain ⟨K, hK, hK1⟩ := (hev.and (Filter.eventually_ge_atTop 1)).exists
  refine ⟨K, ?_⟩
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have h2 : ((K : ℝ) + 1) ^ d ≤ 2 ^ d * (K : ℝ) ^ d := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) d
  rw [div_pow, one_pow, lt_div_iff₀ (by positivity)]
  calc r ^ K * ((K : ℝ) + 1) ^ d ≤ r ^ K * (2 ^ d * (K : ℝ) ^ d) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg hr0 K)
    _ = 2 ^ d * ((K : ℝ) ^ d * r ^ K) := by ring
    _ < 2 ^ d * (1 / 2 ^ d) := by gcongr
    _ = 1 := by field_simp

lemma norm_half_sq (w : ℂ) (hw : ‖w‖ = 1) : ‖(1 + w) / 2‖ ^ 2 = 1 - ‖w - 1‖ ^ 2 / 4 := by
  have h2 : w.re * w.re + w.im * w.im = 1 := by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, hw]; norm_num
  have h4 : ‖(2 : ℂ)‖ ^ 2 = 4 := by norm_num
  rw [norm_div, div_pow, h4]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.sub_re, Complex.sub_im]
  linear_combination (1 / 2 : ℝ) * h2

lemma prod_le_of_far {ι : Type} [Fintype ι] [DecidableEq ι] (K : ℕ) (u v : ι → ℂ)
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1) {η' : ℝ} (hη' : 0 ≤ η') (i₀ : ι)
    (h : η' ≤ ‖u i₀ - v i₀‖) :
    ∏ i, ‖(1 + u i * conj (v i)) / 2‖ ^ (2 * K) ≤ (1 - η' ^ 2 / 4) ^ K := by
  have key : ∀ i, ‖(1 + u i * conj (v i)) / 2‖ ^ 2 = 1 - ‖u i - v i‖ ^ 2 / 4 := by
    intro i
    have hw : ‖u i * conj (v i)‖ = 1 := by rw [norm_mul, Complex.norm_conj, hu, hv, one_mul]
    have hw1 : ‖u i * conj (v i) - 1‖ = ‖u i - v i‖ := by
      have h3 : u i * conj (v i) - 1 = (u i - v i) * conj (v i) := by
        have := mul_conj_eq_one (v i) (hv i)
        linear_combination this
      rw [h3, norm_mul, Complex.norm_conj, hv, mul_one]
    rw [norm_half_sq _ hw, hw1]
  calc ∏ i, ‖(1 + u i * conj (v i)) / 2‖ ^ (2 * K)
      ≤ ∏ i, (if i = i₀ then (1 - η' ^ 2 / 4) ^ K else 1) := by
        apply Finset.prod_le_prod₀ (fun i _ => by positivity)
        intro i _
        rw [pow_mul, key i]
        split_ifs with hi
        · rw [hi]
          have h0 := key i₀
          apply pow_le_pow_left₀ (by rw [← h0]; positivity)
          have : η' ^ 2 ≤ ‖u i₀ - v i₀‖ ^ 2 := pow_le_pow_left₀ hη' h 2
          linarith
        · have h0 := key i
          apply pow_le_one₀ (by rw [← h0]; positivity)
          have : 0 ≤ ‖u i - v i‖ ^ 2 := by positivity
          linarith
    _ = (1 - η' ^ 2 / 4) ^ K := by simp

/-! ### The Fourier expansion of the test function -/

/-- Coefficient of `w^j \bar w^l` in `|(1 + w \bar z)/2|^{2K}` (after factoring out `z`). -/
noncomputable def coef (K : ℕ) (z : ℂ) (s : ℕ × ℕ) : ℂ :=
  (K.choose s.1 * K.choose s.2 : ℂ) / 4 ^ K * conj z ^ s.1 * z ^ s.2

lemma one_add_div_two_pow (w : ℂ) (K : ℕ) :
    ((1 + w) / 2) ^ K = ∑ j ∈ range (K + 1), (K.choose j : ℂ) / 2 ^ K * w ^ j := by
  rw [div_pow, add_comm, add_pow, Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [one_pow, mul_one]; ring

lemma expand_one (w : ℂ) (K : ℕ) :
    ((‖(1 + w) / 2‖ ^ (2 * K) : ℝ) : ℂ) =
      ∑ s ∈ range (K + 1) ×ˢ range (K + 1),
        (K.choose s.1 * K.choose s.2 : ℂ) / 4 ^ K * w ^ s.1 * conj w ^ s.2 := by
  have hu : ((‖(1 + w) / 2‖ ^ (2 * K) : ℝ) : ℂ) =
      ((1 + w) / 2) ^ K * (conj ((1 + w) / 2)) ^ K := by
    rw [← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]; push_cast; ring
  have hc : conj ((1 + w) / 2) = (1 + conj w) / 2 := by
    rw [map_div₀, map_add, map_one, map_ofNat]
  rw [hu, hc, one_add_div_two_pow, one_add_div_two_pow, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  have h4 : (4 : ℂ) ^ K = 2 ^ K * 2 ^ K := by rw [← mul_pow]; norm_num
  dsimp only
  rw [h4]; ring

lemma expand_prod {ι : Type} [Fintype ι] [DecidableEq ι] (K : ℕ) (u v : ι → ℂ) :
    ((∏ i, ‖(1 + u i * conj (v i)) / 2‖ ^ (2 * K) : ℝ) : ℂ) =
      ∑ x ∈ Fintype.piFinset (fun _ : ι => range (K + 1) ×ˢ range (K + 1)),
        (∏ i, coef K (v i) (x i)) * ((∏ i, u i ^ (x i).1) * conj (∏ i, u i ^ (x i).2)) := by
  rw [Complex.ofReal_prod]
  simp_rw [expand_one]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [coef, map_mul, map_pow, Complex.conj_conj, mul_pow]
  ring

lemma diag_sum (K : ℕ) (z : ℂ) (hz : ‖z‖ = 1) :
    ∑ s ∈ range (K + 1) ×ˢ range (K + 1), (coef K z s * if s.1 = s.2 then (1 : ℂ) else 0) =
      ((∑ j ∈ range (K + 1), ((K.choose j : ℝ) ^ 2 / 4 ^ K) : ℝ) : ℂ) := by
  rw [Finset.sum_product, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, ite_eq_left hj]
  have h1 : conj z * z = 1 := by rw [mul_comm]; exact mul_conj_eq_one z hz
  have h2 : conj z ^ j * z ^ j = 1 := by rw [← mul_pow, h1, one_pow]
  simp only [coef]
  push_cast
  linear_combination ((K.choose j : ℂ) * K.choose j / 4 ^ K) * h2

/-! ### Orthogonality -/

lemma char_sum_sq {p : ℕ} [Fact p.Prime] (α β : ZMod p) (hβ : β ≠ 0) :
    ∑ ψ : MulChar (ZMod p) ℂ, (ψ * ψ) α * conj ((ψ * ψ) β) =
      if β * β = α * α then (p.totient : ℂ) else 0 := by
  have hu : IsUnit (β * β) := (mul_ne_zero hβ hβ).isUnit
  rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (α * α)]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [conj_apply, MulChar.mul_apply, MulChar.mul_apply, ← map_mul, ← map_mul, mul_inv, mul_comm]

lemma diag_iff {ι : Type} [Fintype ι] (B : ι → ℕ) (hB : ∀ i, 0 < B i) (hind : MultIndep B)
    (p : ℕ) [Fact p.Prime] (x : ι → ℕ × ℕ)
    (hab : (∏ i, B i ^ (x i).1) + (∏ i, B i ^ (x i).2) < p) :
    ((∏ i, B i ^ (x i).2 : ℕ) : ZMod p) * ((∏ i, B i ^ (x i).2 : ℕ) : ZMod p) =
        ((∏ i, B i ^ (x i).1 : ℕ) : ZMod p) * ((∏ i, B i ^ (x i).1 : ℕ) : ZMod p) ↔
      ∀ i, (x i).1 = (x i).2 := by
  have hpos : 0 < ∏ i, B i ^ (x i).2 := Finset.prod_pos fun i _ => pow_pos (hB i) _
  constructor
  · intro h
    have hab' : (∏ i, B i ^ (x i).1) = ∏ i, B i ^ (x i).2 := by
      rcases mul_self_eq_mul_self_iff.1 h with h | h
      · rw [ZMod.natCast_eq_natCast_iff'] at h
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
        exact h.symm
      · exfalso
        have h2 : (((∏ i, B i ^ (x i).2) + (∏ i, B i ^ (x i).1) : ℕ) : ZMod p) = 0 := by
          rw [Nat.cast_add, h]; ring
        rw [ZMod.natCast_eq_zero_iff] at h2
        have := Nat.le_of_dvd (by omega) h2
        omega
    have hB0 : ∀ i, (B i : ℚ) ≠ 0 := fun i => by exact_mod_cast (hB i).ne'
    have hq : ∏ i, (B i : ℚ) ^ (((x i).1 : ℤ) - (x i).2) = 1 := by
      rw [show ∏ i, (B i : ℚ) ^ (((x i).1 : ℤ) - (x i).2) =
          ∏ i, ((B i : ℚ) ^ (x i).1 / (B i : ℚ) ^ (x i).2) from
        Finset.prod_congr rfl fun i _ => by rw [zpow_sub₀ (hB0 i), zpow_natCast, zpow_natCast]]
      rw [Finset.prod_div_distrib, div_eq_one_iff_eq
        (Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hB0 i))]
      exact_mod_cast hab'
    have he := hind _ hq
    intro i
    have := congrFun he i
    simp only [Pi.zero_apply, sub_eq_zero, Nat.cast_inj] at this
    exact this
  · intro h
    have : (∏ i, B i ^ (x i).1) = ∏ i, B i ^ (x i).2 :=
      Finset.prod_congr rfl fun i _ => by rw [h i]
    rw [this]

/-! ### The averaging identity -/

lemma sum_Phi_eq {ι : Type} [Fintype ι] [DecidableEq ι] (B : ι → ℕ) (hB : ∀ i, 0 < B i)
    (hind : MultIndep B) (K p : ℕ) [Fact p.Prime] (hp : 2 * (∏ i, B i ^ K) < p)
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    ((∑ ψ : MulChar (ZMod p) ℂ,
        ∏ i, ‖(1 + (ψ * ψ) (B i : ZMod p) * conj (z i)) / 2‖ ^ (2 * K) : ℝ) : ℂ) =
      (p.totient : ℂ) *
        ((∏ _i : ι, ∑ j ∈ range (K + 1), ((K.choose j : ℝ) ^ 2 / 4 ^ K) : ℝ) : ℂ) := by
  have hbound : ∀ x ∈ Fintype.piFinset (fun _ : ι => range (K + 1) ×ˢ range (K + 1)),
      ∀ i, (x i).1 ≤ K ∧ (x i).2 ≤ K := by
    intro x hx i
    have := Fintype.mem_piFinset.1 hx i
    simp only [Finset.mem_product, Finset.mem_range] at this
    omega
  have hle : ∀ x ∈ Fintype.piFinset (fun _ : ι => range (K + 1) ×ˢ range (K + 1)),
      (∏ i, B i ^ (x i).1) ≤ ∏ i, B i ^ K ∧ (∏ i, B i ^ (x i).2) ≤ ∏ i, B i ^ K := by
    intro x hx
    exact ⟨Finset.prod_le_prod fun i _ => Nat.pow_le_pow_right (hB i) (hbound x hx i).1,
      Finset.prod_le_prod fun i _ => Nat.pow_le_pow_right (hB i) (hbound x hx i).2⟩
  have hpos : ∀ x : ι → ℕ × ℕ, 0 < ∏ i, B i ^ (x i).2 :=
    fun x => Finset.prod_pos fun i _ => pow_pos (hB i) _
  rw [Complex.ofReal_sum]
  calc ∑ ψ : MulChar (ZMod p) ℂ,
        ((∏ i, ‖(1 + (ψ * ψ) (B i : ZMod p) * conj (z i)) / 2‖ ^ (2 * K) : ℝ) : ℂ)
      = ∑ ψ : MulChar (ZMod p) ℂ,
          ∑ x ∈ Fintype.piFinset (fun _ : ι => range (K + 1) ×ˢ range (K + 1)),
            (∏ i, coef K (z i) (x i)) *
              ((ψ * ψ) ((∏ i, B i ^ (x i).1 : ℕ) : ZMod p) *
                conj ((ψ * ψ) ((∏ i, B i ^ (x i).2 : ℕ) : ZMod p))) := by
        refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [expand_prod K (fun i => (ψ * ψ) (B i : ZMod p)) z]
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [Nat.cast_prod, Nat.cast_pow, map_prod, map_pow]
    _ = ∑ x ∈ Fintype.piFinset (fun _ : ι => range (K + 1) ×ˢ range (K + 1)),
          (∏ i, coef K (z i) (x i)) * ∑ ψ : MulChar (ZMod p) ℂ,
            ((ψ * ψ) ((∏ i, B i ^ (x i).1 : ℕ) : ZMod p) *
              conj ((ψ * ψ) ((∏ i, B i ^ (x i).2 : ℕ) : ZMod p))) := by
        rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
    _ = ∑ x ∈ Fintype.piFinset (fun _ : ι => range (K + 1) ×ˢ range (K + 1)),
          (∏ i, coef K (z i) (x i)) *
            ((p.totient : ℂ) * ∏ i, (if (x i).1 = (x i).2 then (1 : ℂ) else 0)) := by
        refine Finset.sum_congr rfl fun x hx => ?_
        have hx' := hle x hx
        rw [char_sum_sq _ _ (natCast_ne_zero_of_lt (hpos x) (by omega)), Finset.prod_boole]
        have hd := diag_iff B hB hind p x (by omega)
        by_cases h : ∀ i, (x i).1 = (x i).2
        · rw [ite_eq_left (hd.2 h), ite_eq_left (fun i _ => h i)]; ring
        · rw [ite_eq_right (fun h' => h (hd.1 h')),
            ite_eq_right (fun h' => h (fun i => h' i (Finset.mem_univ i)))]
          ring
    _ = (p.totient : ℂ) * ∏ i, ∑ s ∈ range (K + 1) ×ˢ range (K + 1),
          (coef K (z i) s * if s.1 = s.2 then (1 : ℂ) else 0) := by
        rw [Finset.prod_univ_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    _ = _ := by
        congr 1
        rw [Complex.ofReal_prod]
        exact Finset.prod_congr rfl fun i _ => diag_sum K (z i) (hz i)

/-! ### The equidistribution statement for squares of characters -/

theorem exists_char {ι : Type} [Fintype ι] (B : ι → ℕ) (hB : ∀ i, 0 < B i)
    (hind : MultIndep B) (η : ℝ) (hη : 0 < η) :
    ∃ P₀ : ℕ, ∀ p : ℕ, p.Prime → P₀ ≤ p → ∀ z : ι → ℂ, (∀ i, ‖z i‖ = 1) →
      ∃ ψ : MulChar (ZMod p) ℂ, ∀ i, ‖(ψ * ψ) (B i : ZMod p) - z i‖ < η := by
  classical
  have hη'0 : 0 < min η 1 := lt_min hη one_pos
  have hη'1 : min η 1 ≤ 1 := min_le_right _ _
  have hη'η : min η 1 ≤ η := min_le_left _ _
  have hr0 : 0 ≤ 1 - (min η 1) ^ 2 / 4 := by nlinarith
  have hr1 : 1 - (min η 1) ^ 2 / 4 < 1 := by have := pow_pos hη'0 2; linarith
  obtain ⟨K, hKr⟩ := exists_K (Fintype.card ι) hr0 hr1
  refine ⟨2 * (∏ i, B i ^ K) + ∑ i, B i + 1, fun p hp hpP z hz => ?_⟩
  have := Fact.mk hp
  have hpM : 2 * (∏ i, B i ^ K) < p := by omega
  have hBp : ∀ i, B i < p := fun i => by
    have := Finset.single_le_sum (f := B) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hsum := sum_Phi_eq B hB hind K p hpM z hz
  have hDlow : (1 / ((K : ℝ) + 1)) ^ Fintype.card ι ≤
      ∏ _i : ι, ∑ j ∈ range (K + 1), ((K.choose j : ℝ) ^ 2 / 4 ^ K) := by
    rw [Finset.prod_const, Finset.card_univ]
    exact pow_le_pow_left₀ (by positivity) (diag_lower K) _
  have hcard : (Fintype.card (MulChar (ZMod p) ℂ) : ℂ) = (p.totient : ℂ) := by
    have := DirichletCharacter.sum_characters_eq ℂ (1 : ZMod p)
    simpa using this
  have hreal : ∑ _ψ : MulChar (ZMod p) ℂ,
        ∏ _i : ι, ∑ j ∈ range (K + 1), ((K.choose j : ℝ) ^ 2 / 4 ^ K) ≤
      ∑ ψ : MulChar (ZMod p) ℂ,
        ∏ i, ‖(1 + (ψ * ψ) (B i : ZMod p) * conj (z i)) / 2‖ ^ (2 * K) := by
    apply le_of_eq
    apply Complex.ofReal_injective
    rw [hsum, Complex.ofReal_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  obtain ⟨ψ, -, hψ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hreal
  refine ⟨ψ, fun i => ?_⟩
  by_contra hcon
  replace hcon := not_lt.1 hcon
  have hunit : ∀ j, ‖(ψ * ψ) (B j : ZMod p)‖ = 1 := fun j =>
    norm_apply_of_isUnit _ (natCast_ne_zero_of_lt (hB j) (hBp j)).isUnit
  have hle := prod_le_of_far K (fun j => (ψ * ψ) (B j : ZMod p)) z hunit hz hη'0.le i
    (le_trans hη'η hcon)
  exact absurd (hle.trans_lt (hKr.trans_le hDlow)) (not_lt.2 hψ)

end ChowlaOpus.PhaseAux

namespace ChowlaOpus

open ComplexConjugate

theorem phaseStatement_holds (hK : KernelCharStatement) : PhaseStatement := by
  intro ι _ n hn hind η hη
  obtain ⟨P₁, hP₁⟩ := PhaseAux.exists_char (fun i => n i ^ n i) (fun i => pow_pos (hn i) _)
    (PhaseAux.multIndep_pow n hn hind) η hη
  refine ⟨max P₁ (∑ i, n i + 3), fun p hp hpP μ hμ => ?_⟩
  have hp1 : P₁ ≤ p := le_trans (le_max_left _ _) hpP
  have hp2 : ∑ i, n i + 3 ≤ p := le_trans (le_max_right _ _) hpP
  have hnp : ∀ i, n i < p := fun i => by
    have := Finset.single_le_sum (f := n) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hp2' : p ≠ 2 := by omega
  have := Fact.mk hp
  obtain ⟨χ₀, hχ₀⟩ := hK p hp hp2'
  have hg : ∀ i, ‖gaussPhase p χ₀ (n i)‖ = 1 := fun i =>
    PhaseAux.norm_gaussPhase p χ₀ (n i) (hn i) (hnp i)
  obtain ⟨ψ, hψ⟩ := hP₁ p hp hp1 (fun i => μ i * conj (gaussPhase p χ₀ (n i))) (fun i => by
    rw [norm_mul, Complex.norm_conj, hμ, hg, one_mul])
  refine ⟨χ₀ * PhaseAux.lift p (ψ * ψ), PhaseAux.kernelChar_mul_lift p χ₀ hχ₀ ψ, fun i => ?_⟩
  rw [PhaseAux.gaussPhase_mul_lift]
  have key : gaussPhase p χ₀ (n i) * (ψ * ψ) ((n i ^ n i : ℕ) : ZMod p) - μ i =
      gaussPhase p χ₀ (n i) *
        ((ψ * ψ) ((n i ^ n i : ℕ) : ZMod p) - μ i * conj (gaussPhase p χ₀ (n i))) := by
    have := PhaseAux.mul_conj_eq_one _ (hg i)
    linear_combination (μ i) * this
  rw [key, norm_mul, hg, one_mul]
  exact hψ i

end ChowlaOpus
