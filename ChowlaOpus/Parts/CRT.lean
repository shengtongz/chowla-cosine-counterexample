module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.CRTAux

open Finset Polynomial

/-- The polynomial `∑ i, c i X^i` attached to a coefficient vector. -/
noncomputable def vecPoly {k : ℕ} (c : Fin (k + 1) → ℤ) : ℤ[X] :=
  ∑ i : Fin (k + 1), Polynomial.C (c i) * X ^ (i : ℕ)

lemma vecPoly_coeff {k : ℕ} (c : Fin (k + 1) → ℤ) (j : Fin (k + 1)) :
    (vecPoly c).coeff j = c j := by
  rw [vecPoly, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    exact ite_eq_right_iff.mpr fun h => absurd (Fin.ext h).symm hb
  · simp

lemma vecPoly_ne_zero {k : ℕ} {c : Fin (k + 1) → ℤ} (hc : c ≠ 0) : vecPoly c ≠ 0 := by
  intro h
  apply hc
  funext j
  rw [← vecPoly_coeff c j, h]
  simp

lemma vecPoly_eval {k : ℕ} (c : Fin (k + 1) → ℤ) (x : ℤ) :
    (vecPoly c).eval x = ∑ i : Fin (k + 1), x ^ (i : ℕ) * c i := by
  simp [vecPoly, Polynomial.eval_finsetSum, mul_comm]

lemma exists_avoid {k : ℕ} (C : Finset (Fin (k + 1) → ℤ)) (hC : ∀ c ∈ C, c ≠ 0) :
    ∃ y : Fin (k + 1) → ℤ, ∀ c ∈ C, ∑ i, y i * c i ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ :=
    Infinite.exists_notMem_finset (C.biUnion fun c => (vecPoly c).roots.toFinset)
  refine ⟨fun i => x ^ (i : ℕ), fun c hc h => hx ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨c, hc, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (vecPoly_ne_zero (hC c hc)),
    Polynomial.IsRoot, vecPoly_eval]
  exact h

lemma minor_ne_zero {k : ℕ} {v w : Fin (k + 1) → ℤ} (hv : v 0 ≠ 0)
    (h : ¬ ∀ i j, v i * w j = v j * w i) : (fun i => v 0 * w i - w 0 * v i) ≠ 0 := by
  intro h0
  apply h
  intro i j
  have hi : v 0 * w i = w 0 * v i := sub_eq_zero.mp (congrFun h0 i)
  have hj : v 0 * w j = w 0 * v j := sub_eq_zero.mp (congrFun h0 j)
  apply mul_left_cancel₀ hv
  calc v 0 * (v i * w j) = v i * (v 0 * w j) := by ring
    _ = v i * (w 0 * v j) := by rw [hj]
    _ = v j * (w 0 * v i) := by ring
    _ = v j * (v 0 * w i) := by rw [hi]
    _ = v 0 * (v j * w i) := by ring

lemma padicValRat_prod {ι : Type*} (p : ℕ) [Fact p.Prime] (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    padicValRat p (∏ i ∈ s, f i) = ∑ i ∈ s, padicValRat p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      padicValRat.mul (hf a (mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hf i (mem_insert_of_mem hi)),
      ih fun i hi => hf i (mem_insert_of_mem hi)]

/-- Private-prime criterion for multiplicative independence. -/
lemma multIndep_of_primes {ι : Type*} [Fintype ι] (n : ι → ℕ) (hn : ∀ i, n i ≠ 0)
    (r : ι → ℕ) (hr : ∀ i, (r i).Prime) (hdvd : ∀ i, r i ∣ n i)
    (hndvd : ∀ i j, i ≠ j → ¬ r i ∣ n j) : MultIndep n := by
  classical
  intro e he
  funext i
  have : Fact (r i).Prime := ⟨hr i⟩
  have h1 := congrArg (padicValRat (r i)) he
  rw [padicValRat_prod _ _ _ (fun j _ => zpow_ne_zero _ (Nat.cast_ne_zero.mpr (hn j))),
    padicValRat.one] at h1
  simp only [padicValRat.zpow, padicValRat.of_nat] at h1
  rw [Finset.sum_eq_single i] at h1
  · have : multiplicity (r i) (n i) ≠ 0 := (dvd_iff_multiplicity_ne_zero (hn i)).mp (hdvd i)
    simpa [this] using h1
  · intro j _ hji
    rw [multiplicity_eq_zero_of_not_dvd (hndvd i j (Ne.symm hji))]
    simp
  · simp

/-- Main lemma for an indexed family. -/
lemma main {ι : Type*} [Fintype ι] {k : ℕ} (V : ι → Fin (k + 1) → ℤ) (hpos : ∀ i, 0 < V i 0)
    (hnp : ∀ i j, (∀ a b, V i a * V j b = V i b * V j a) → i = j) :
    ∃ L : Fin (k + 1) → ℤ, (∀ i, 0 < ∑ a, L a * V i a) ∧
      MultIndep (fun i => (∑ a, L a * V i a).toNat) := by
  classical
  -- the minors `c i j`
  set c : ι → ι → Fin (k + 1) → ℤ := fun i j b => V i 0 * V j b - V j 0 * V i b with hc
  have hc0 : ∀ i j, i ≠ j → c i j ≠ 0 := fun i j hij =>
    minor_ne_zero (hpos i).ne' (fun h => hij (hnp i j h))
  obtain ⟨y, hy⟩ := exists_avoid
    ((univ.filter fun p : ι × ι => p.1 ≠ p.2).image fun p => c p.1 p.2)
    (by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact hc0 _ _ (Finset.mem_filter.mp hp).2)
  -- the integer forms `a i j = ℓ_i · V j`
  set a : ι → ι → ℤ := fun i j => V i 0 * (y ⬝ᵥ V j) - (y ⬝ᵥ V i) * V j 0 with ha
  have haii : ∀ i, a i i = 0 := fun i => by simp only [ha]; ring
  have hane : ∀ i j, i ≠ j → a i j ≠ 0 := by
    intro i j hij
    have := hy (c i j) (Finset.mem_image.mpr ⟨(i, j), by simp [hij], rfl⟩)
    convert this using 1
    simp only [ha, hc, dotProduct]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by ring
  set B : ℕ := ∑ i, ∑ j, (a i j).natAbs with hB
  have haB : ∀ i j, (a i j).natAbs ≤ B := fun i j =>
    (Finset.single_le_sum (f := fun j => (a i j).natAbs) (fun _ _ => Nat.zero_le _)
      (mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, (a i j).natAbs) (fun _ _ => Nat.zero_le _)
        (mem_univ i))
  -- distinct primes `r i > B`
  set idx : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ) with hidx
  have hidx_inj : Function.Injective idx := fun i j h =>
    (Fintype.equivFin ι).injective (Fin.ext h)
  set r : ι → ℕ := fun i => Nat.nth Nat.Prime (B + 1 + idx i) with hr
  have hrp : ∀ i, (r i).Prime := fun i => Nat.prime_nth_prime _
  have hr_inj : Function.Injective r := fun i j h =>
    hidx_inj (Nat.add_left_cancel (Nat.nth_injective Nat.infinite_setOfPred_prime h))
  have hrB : ∀ i, B < r i := fun i => by
    have : B + 1 + idx i ≤ Nat.nth Nat.Prime (B + 1 + idx i) :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le (B + 1 + idx i)
    show B < Nat.nth Nat.Prime (B + 1 + idx i)
    omega
  -- products of the primes
  set Q : ℤ := ∏ i, (r i : ℤ) with hQ
  set Qx : ι → ℤ := fun i => ∏ j ∈ univ.erase i, (r j : ℤ) with hQx
  have hQpos : 1 ≤ Q := by
    have : 0 < Q := Finset.prod_pos fun i _ => by exact_mod_cast (hrp i).pos
    omega
  set X : ι → ℤ := fun j => ∑ i, Qx i * a i j with hX
  set M : ℤ := ∑ j, |X j| + 1 with hM
  set L : Fin (k + 1) → ℤ :=
    ∑ i, Qx i • (V i 0 • y - (y ⬝ᵥ V i) • Pi.single 0 1) + (M * Q) • Pi.single 0 1 with hL
  set n : ι → ℤ := fun j => X j + M * Q * V j 0 with hn
  have hLv : ∀ j, ∑ b, L b * V j b = n j := by
    intro j
    show L ⬝ᵥ V j = _
    simp only [hL, add_dotProduct, sum_dotProduct, smul_dotProduct, sub_dotProduct,
      single_dotProduct, smul_eq_mul, hn, hX, ha, one_mul]
  have hnpos : ∀ j, 0 < n j := by
    intro j
    have h1 : |X j| ≤ ∑ j, |X j| :=
      Finset.single_le_sum (f := fun j => |X j|) (fun _ _ => abs_nonneg _) (mem_univ j)
    have h2 : -|X j| ≤ X j := neg_abs_le _
    have h3 : 1 ≤ V j 0 := hpos j
    have h4 : 1 ≤ Q * V j 0 := by nlinarith
    have h6 : 1 ≤ M := by rw [hM]; linarith [abs_nonneg (X j)]
    have h5 : M ≤ M * Q * V j 0 := by rw [mul_assoc]; nlinarith
    simp only [hn]
    linarith
  have hcong : ∀ i j, (r i : ℤ) ∣ n j - Qx i * a i j := by
    intro i j
    simp only [hn, hX]
    rw [← Finset.add_sum_erase univ (fun l => Qx l * a l j) (mem_univ i)]
    have h1 : (r i : ℤ) ∣ ∑ l ∈ univ.erase i, Qx l * a l j := Finset.dvd_sum fun l hl =>
      Dvd.dvd.mul_right (by
        simp only [hQx]
        exact Finset.dvd_prod_of_mem _
          (Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hl).1 h.symm, mem_univ _⟩)) _
    have hQ' : (r i : ℤ) ∣ Q := Finset.dvd_prod_of_mem _ (mem_univ i)
    have h2 : Qx i * a i j + ∑ l ∈ univ.erase i, Qx l * a l j + M * Q * V j 0 - Qx i * a i j
        = ∑ l ∈ univ.erase i, Qx l * a l j + M * Q * V j 0 := by ring
    rw [h2]
    exact dvd_add h1 (Dvd.dvd.mul_right (Dvd.dvd.mul_left hQ' _) _)
  have hdvd : ∀ i, (r i : ℤ) ∣ n i := by
    intro i
    simpa [haii] using hcong i i
  have hndvd : ∀ i j, i ≠ j → ¬ (r i : ℤ) ∣ n j := by
    intro i j hij hd
    have h1 : (r i : ℤ) ∣ Qx i * a i j := by
      have := dvd_sub hd (hcong i j)
      rwa [sub_sub_cancel] at this
    have hpr : Prime (r i : ℤ) := Nat.prime_iff_prime_int.mp (hrp i)
    rcases hpr.dvd_or_dvd h1 with h2 | h2
    · simp only [hQx] at h2
      obtain ⟨l, hl, h3⟩ := (Prime.dvd_finsetProd_iff hpr _).mp h2
      have h4 : r i ∣ r l := Int.natCast_dvd_natCast.mp h3
      have h5 : r i = r l := (Nat.prime_dvd_prime_iff_eq (hrp i) (hrp l)).mp h4
      exact (Finset.mem_erase.mp hl).1 (hr_inj h5).symm
    · have h3 : r i ∣ (a i j).natAbs := Int.ofNat_dvd_left.mp h2
      have h4 := Nat.le_of_dvd (Int.natAbs_pos.mpr (hane i j hij)) h3
      have := haB i j
      have := hrB i
      omega
  refine ⟨L, fun j => hLv j ▸ hnpos j, ?_⟩
  simp_rw [hLv]
  have hnat : ∀ j, ((n j).toNat : ℤ) = n j := fun j => Int.toNat_of_nonneg (hnpos j).le
  refine multIndep_of_primes _ (fun j => by have := hnpos j; omega) r hrp
    (fun i => ?_) (fun i j hij => ?_)
  · rw [← Int.natCast_dvd_natCast, hnat]
    exact hdvd i
  · rw [← Int.natCast_dvd_natCast, hnat]
    exact hndvd i j hij

end ChowlaOpus.CRTAux

namespace ChowlaOpus

theorem crtStatement_holds : CRTStatement := by
  intro k S hpos hnp
  obtain ⟨L, hL1, hL2⟩ := CRTAux.main (fun v : S => (v : Fin (k + 1) → ℤ))
    (fun v => hpos v v.2) (fun v w h => Subtype.ext (hnp v v.2 w w.2 h))
  exact ⟨L, fun v hv => hL1 ⟨v, hv⟩, hL2⟩

end ChowlaOpus
