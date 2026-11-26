module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.AsmBAux

open ChowlaOpus

lemma exists_ee_of_norm_eq_one (u : ℂ) (hu : ‖u‖ = 1) : ∃ z : ℝ, ee z = u := by
  refine ⟨Complex.arg u / (2 * Real.pi), ?_⟩
  have h := Complex.norm_mul_exp_arg_mul_I u
  rw [hu, Complex.ofReal_one, one_mul] at h
  unfold ee
  conv_rhs => rw [← h]
  congr 1
  have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

lemma norm_chi_eq_one {p : ℕ} (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ) (d : ℕ)
    (hd : ¬ p ∣ d) : ‖χ (d : ZMod (p ^ 2))‖ = 1 := by
  have hu : IsUnit (d : ZMod (p ^ 2)) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow hp (by norm_num)).mpr hd
  obtain ⟨u, hu⟩ := hu
  have : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  refine Complex.norm_eq_one_of_pow_eq_one (n := orderOf u) ?_ (orderOf_pos u).ne'
  rw [← hu, ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one,
    map_one]

lemma wgt_mem {k : ℕ} {T K : ℝ} {S : Finset (Fin (k + 1) → ℤ)}
    {cf : (Fin (k + 1) → ℤ) → ℝ → ℂ} (hP : IsProfile T S cf K (T ^ 2))
    (L : Fin (k + 1) → ℤ) {p : ℕ} (hp : p.Prime) (χ : MulChar (ZMod (p ^ 2)) ℂ) (d : ℕ) :
    0 ≤ wgt S cf L p χ d ∧ wgt S cf L p χ d ≤ 1 := by
  unfold wgt
  split_ifs with h
  · simp
  · have hd : ¬ p ∣ d := fun h' => h (Int.natCast_dvd_natCast.mpr h')
    obtain ⟨z, hz⟩ := exists_ee_of_norm_eq_one _ (norm_chi_eq_one hp χ d hd)
    have key : (∑ v ∈ S, cf v (((d : ℤ) : ℝ) / (p : ℝ) ^ 2) *
        (χ ((d : ℤ) : ZMod (p ^ 2))) ^ (∑ i, L i * v i)) =
        trigEval S (fun v => cf v (((d : ℤ) : ℝ) / (p : ℝ) ^ 2)) (fun i => z * L i) := by
      unfold trigEval
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Int.cast_natCast (R := ZMod (p ^ 2)), ← hz, ← ee_mul_intCast]
      congr 2
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [key]
    exact ⟨(hP.range _ _).2.1, (hP.range _ _).2.2⟩

lemma pos_inj {k : ℕ} (Sp : Finset (Fin (k + 1) → ℤ)) (L : Fin (k + 1) → ℤ)
    (hpos : ∀ v ∈ Sp, 0 < ∑ i, L i * v i)
    (hind : MultIndep (fun v : Sp => (∑ i, L i * (v : Fin (k + 1) → ℤ) i).toNat)) :
    ∀ v ∈ Sp, ∀ w ∈ Sp, ∑ i, L i * v i = ∑ i, L i * w i → v = w := by
  intro v hv w hw hvw
  by_contra hne
  set v' : Sp := ⟨v, hv⟩ with hv'
  set w' : Sp := ⟨w, hw⟩ with hw'
  have hne' : v' ≠ w' := fun h => hne (congrArg Subtype.val h)
  set x : Sp → ℚ := fun u => ((∑ i, L i * (u : Fin (k + 1) → ℤ) i).toNat : ℚ) with hx
  have hxw : x w' ≠ 0 := by
    simp only [hx, hw']
    have := hpos w hw
    exact_mod_cast (by omega : (∑ i, L i * w i).toNat ≠ 0)
  have hxvw : x v' = x w' := by simp only [hx, hv', hw', hvw]
  set e : Sp → ℤ := fun u => (if u = v' then 1 else 0) - (if u = w' then 1 else 0) with he
  have hterm : ∀ u, x u ^ e u =
      (if u = v' then x u else 1) * (if u = w' then (x u)⁻¹ else 1) := by
    intro u
    by_cases h1 : u = v'
    · rw [h1]; simp [he, hne']
    · by_cases h2 : u = w'
      · rw [h2]; simp [he, Ne.symm hne']
      · simp [he, h1, h2]
  have hprod : ∏ u, x u ^ e u = 1 := by
    rw [Finset.prod_congr rfl (fun u _ => hterm u), Finset.prod_mul_distrib,
      Finset.prod_ite_eq', Finset.prod_ite_eq']
    simp only [Finset.mem_univ, ite_true]
    rw [hxvw, mul_inv_cancel₀ hxw]
  have he0 := hind e hprod
  have : e v' = 0 := by rw [he0]; rfl
  simp [he, hne'] at this

lemma L_inj {k : ℕ} {S : Finset (Fin (k + 1) → ℤ)}
    (hneg : ∀ v ∈ S, -v ∈ S) (hlab : ∀ v ∈ S, v ≠ 0 → v 0 ≠ 0) (L : Fin (k + 1) → ℤ)
    (hpos : ∀ v ∈ S.filter (fun v => 0 < v 0), 0 < ∑ i, L i * v i)
    (hind : MultIndep (fun v : S.filter (fun v => 0 < v 0) =>
      (∑ i, L i * (v : Fin (k + 1) → ℤ) i).toNat)) :
    ∀ v ∈ S, ∀ w ∈ S, ∑ i, L i * v i = ∑ i, L i * w i → v = w := by
  have hpi := pos_inj _ L hpos hind
  have hnegf : ∀ v : Fin (k + 1) → ℤ, ∑ i, L i * (-v) i = -∑ i, L i * v i := by
    intro v; simp [Finset.sum_neg_distrib]
  have hf0 : ∑ i, L i * (0 : Fin (k + 1) → ℤ) i = 0 := by simp
  have hsign : ∀ v ∈ S, v = 0 ∨ (v ∈ S.filter (fun v => 0 < v 0)) ∨
      (-v ∈ S.filter (fun v => 0 < v 0)) := by
    intro v hv
    by_cases h : v = 0
    · exact Or.inl h
    · rcases lt_or_gt_of_ne (hlab v hv h) with hlt | hgt
      · right; right; exact Finset.mem_filter.mpr ⟨hneg v hv, by simp; omega⟩
      · right; left; exact Finset.mem_filter.mpr ⟨hv, hgt⟩
  intro v hv w hw hvw
  rcases hsign v hv with h1 | h1 | h1 <;> rcases hsign w hw with h2 | h2 | h2
  · rw [h1, h2]
  · exfalso; have := hpos w h2; rw [h1, hf0] at hvw; omega
  · exfalso; have := hpos _ h2; rw [hnegf] at this; rw [h1, hf0] at hvw; omega
  · exfalso; have := hpos v h1; rw [h2, hf0] at hvw; omega
  · exact hpi v h1 w h2 hvw
  · exfalso; have := hpos v h1; have := hpos _ h2; rw [hnegf] at this; omega
  · exfalso; have := hpos _ h1; rw [hnegf] at this; rw [h2, hf0] at hvw; omega
  · exfalso; have := hpos _ h1; rw [hnegf] at this; have := hpos w h2; omega
  · have := hpi _ h1 _ h2 (by rw [hnegf, hnegf, hvw]); exact neg_inj.mp this

end ChowlaOpus.AsmBAux

namespace ChowlaOpus

open ChowlaOpus.AsmBAux in
theorem weightsStatement_holds (hPr : ProfileStatement) (hC : CRTStatement)
    (hPh : PhaseStatement) (hR : RowSumStatement) (hM : MultStatement)
    (h9 : W9Statement) (h10 : W10Statement) : WeightsStatement := by
  obtain ⟨C, c, hC0, hc0, T₀, hPrT⟩ := hPr
  refine ⟨C + 1, c / 8, by linarith, by positivity, fun T₀' => ?_⟩
  set T : ℝ := max (max T₀ T₀') 3 with hTdef
  have hT3 : 3 ≤ T := le_max_right _ _
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
  have hTT₀' : T₀' ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨T, hTT₀', hT3, ?_⟩
  obtain ⟨k, S, cf, K, hP, -, hsumle, hmass, hvar⟩ := hPrT T hTT₀
  have hTpos : 0 < T := by linarith
  have hlogT : 1 ≤ Real.log T := by
    have h1 : Real.exp 1 ≤ T := by linarith [Real.exp_one_lt_d9]
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) h1
  have hK : 0 ≤ K := by
    have h := hP.decay 0 0
    have h1 : (1 : ℝ) + 0 ^ 2 = 1 := by norm_num
    rw [h1, div_one] at h
    exact le_trans (norm_nonneg _) h
  -- positive half of the frequency set
  set Sp := S.filter (fun v => 0 < v 0) with hSp
  obtain ⟨L, hLpos, hLind⟩ := hC k Sp (fun v hv => (Finset.mem_filter.mp hv).2)
    (fun v hv w hw hvw => hP.nonprop v (Finset.mem_filter.mp hv).1 w
      (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hv).2 (Finset.mem_filter.mp hw).2 hvw)
  have hinj := L_inj hP.neg_mem hP.label_ne L hLpos hLind
  obtain ⟨E, hE⟩ := h10 k T K S cf hP hTpos L hinj
  set η : ℝ := 1 / (T * (5 * K * S.card + 1)) with hηdef
  have hA : 0 ≤ 5 * K * (S.card : ℝ) := by positivity
  have hη : 0 < η := by positivity
  have hηK : η * (5 * K * S.card) ≤ 1 / T := by
    rw [hηdef, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hTpos]
    nlinarith
  obtain ⟨P₀, hP₀⟩ := hPh Sp (fun v => (∑ i, L i * (v : Fin (k + 1) → ℤ) i).toNat)
    (fun v => by have := hLpos v v.2; omega) hLind η hη
  intro p₀
  set D : ℕ := ∑ v ∈ S, (∑ i, L i * v i).natAbs with hD
  set M₁ : ℕ := ⌈8 * E * T / c⌉₊ with hM₁
  set M₂ : ℕ := ⌈2 * E * T ^ 3 / (C * Real.log T)⌉₊ with hM₂
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (p₀ + P₀ + 3 + (2 * D + 1) + M₁ + M₂)
  have hp3 : 3 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have hbound : ∀ v ∈ S, 2 * |∑ i, L i * v i| < p := by
    intro v hv
    have h1 : (∑ i, L i * v i).natAbs ≤ D :=
      Finset.single_le_sum (f := fun v => (∑ i, L i * v i).natAbs)
        (fun _ _ => Nat.zero_le _) hv
    rw [Int.abs_eq_natAbs]
    omega
  obtain ⟨χ, hχ, hχphase⟩ := hP₀ p hp (by omega)
    (fun v => mult (2 * Real.pi * (v : Fin (k + 1) → ℤ) 0 / T)) (fun v => hM.1 _)
  have hphase : ∀ v ∈ S, v ≠ 0 →
      ‖gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T)‖ ≤ η := by
    have hposcase : ∀ v ∈ Sp,
        ‖gaussPhase p χ (∑ i, L i * v i) - mult (2 * Real.pi * v 0 / T)‖ ≤ η := by
      intro v hv
      have h1 := hχphase ⟨v, hv⟩
      simp only at h1
      rw [Int.toNat_of_nonneg (hLpos v hv).le] at h1
      exact h1.le
    intro v hv hv0
    rcases lt_or_gt_of_ne (hP.label_ne v hv hv0) with hlt | hgt
    · have hmem : -v ∈ Sp := Finset.mem_filter.mpr ⟨hP.neg_mem v hv, by simp; omega⟩
      have h1 := hposcase (-v) hmem
      have e1 : ∑ i, L i * v i = -(∑ i, L i * (-v) i) := by simp [Finset.sum_neg_distrib]
      have e2 : mult (2 * Real.pi * v 0 / T) =
          starRingEnd ℂ (mult (2 * Real.pi * ((-v) 0 : ℤ) / T)) := by
        rw [← hM.2.2]; congr 1; simp; ring
      rw [e1, (hR p hp hp2 χ hχ).2.2.2.2, e2, ← map_sub, Complex.norm_conj]
      exact h1
    · exact hposcase v (Finset.mem_filter.mpr ⟨hv, hgt⟩)
  set N : ℕ := ⌈(p : ℝ) ^ 2 * T ^ 2⌉₊ with hNdef
  have hN : (p : ℝ) ^ 2 * T ^ 2 ≤ N := Nat.le_ceil _
  have hN' : (N : ℝ) < (p : ℝ) ^ 2 * T ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hp3' : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hq0 : (0 : ℝ) ≤ p := by positivity
  have hpT : (1 : ℝ) ≤ (p : ℝ) ^ 2 * T ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ (by linarith))
  have hpp : 0 ≤ (p : ℝ) ^ 2 - p := by
    have : (p : ℝ) ^ 2 - p = p * (p - 1) := by ring
    rw [this]; exact mul_nonneg hq0 (by linarith)
  refine ⟨p, N, fun d => wgt S cf L p χ d, by omega, ?_, ?_, fun d => wgt_mem hP L hp χ d,
    ?_, ?_, ?_⟩
  · have : (1 : ℝ) ≤ N := le_trans hpT hN
    exact_mod_cast this
  · linarith
  · intro t
    have h := h9 k T K S cf hP hTpos L p hp hp2 hbound hinj χ hχ η hη.le hηK hphase N hN t
    refine le_trans ?_ h
    have h1 : ∑' j : ℤ, (cf 0 j).re + 1 / T ≤ (C + 1) * Real.log T / T := by
      have : 1 / T ≤ Real.log T / T := div_le_div_of_nonneg_right hlogT hTpos.le
      have : (C + 1) * Real.log T / T = C * Real.log T / T + Real.log T / T := by ring
      linarith
    have hX : 0 ≤ (C + 1) * Real.log T / T := by
      apply div_nonneg _ hTpos.le
      apply mul_nonneg (by linarith) (by linarith)
    have h2 : (p : ℝ) / 2 * (∑' j : ℤ, (cf 0 j).re + 1 / T) ≤ (C + 1) * p * Real.log T / T := by
      calc (p : ℝ) / 2 * (∑' j : ℤ, (cf 0 j).re + 1 / T)
          ≤ (p : ℝ) / 2 * ((C + 1) * Real.log T / T) := by gcongr
        _ ≤ (p : ℝ) * ((C + 1) * Real.log T / T) := by
          have := mul_nonneg hq0 hX; linarith
        _ = (C + 1) * p * Real.log T / T := by ring
    linarith
  · have h := (hE p hp hp2 hbound χ hχ N hN).1
    rw [abs_le] at h
    have hM1 : 8 * E * T / c ≤ p :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : M₁ ≤ p))
    rw [div_le_iff₀ hc0] at hM1
    have hTI : c ≤ T * ∫ x, (cf 0 x).re := by
      rw [div_le_iff₀ hTpos] at hmass; linarith
    beta_reduce
    rw [div_le_iff₀ hTpos]
    have k0 : 0 ≤ (∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d -
        ((p : ℝ) ^ 2 - p) / 2 * (∫ x, (cf 0 x).re) + E * p) * T :=
      mul_nonneg (by linarith [h.1]) hTpos.le
    have k1' : 0 ≤ T * (∫ x, (cf 0 x).re) - c := by linarith
    have k1 : 0 ≤ ((p : ℝ) ^ 2 - p) * (T * (∫ x, (cf 0 x).re) - c) := mul_nonneg hpp k1'
    have k2' : 0 ≤ (p : ℝ) * c - 8 * E * T := by linarith
    have k2 : 0 ≤ (p : ℝ) * ((p : ℝ) * c - 8 * E * T) := mul_nonneg hq0 k2'
    have k3' : 0 ≤ (p : ℝ) - 2 := by linarith
    have k3 : 0 ≤ (p : ℝ) * ((p : ℝ) - 2) * c := mul_nonneg (mul_nonneg hq0 k3') hc0.le
    linarith
  · have h := (hE p hp hp2 hbound χ hχ N hN).2
    rw [abs_le] at h
    have hCl : 0 < C * Real.log T := mul_pos hC0 (by linarith)
    have hM2 : 2 * E * T ^ 3 / (C * Real.log T) ≤ p :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast (by omega : M₂ ≤ p))
    rw [div_le_iff₀ hCl] at hM2
    set V := ∫ x, ((cf 0 x).re - ∑ v ∈ S, ‖cf v x‖ ^ 2) with hV
    have hT3pos : 0 < T ^ 3 := by positivity
    have hVT : V * T ^ 3 ≤ C * Real.log T := by
      rw [le_div_iff₀ hT3pos] at hvar; linarith
    beta_reduce
    rw [le_div_iff₀ hT3pos]
    have k0 : 0 ≤ (E * p - ∑ d ∈ Finset.Icc 1 N, wgt S cf L p χ d * (1 - wgt S cf L p χ d) +
        ((p : ℝ) ^ 2 - p) / 2 * V) * T ^ 3 :=
      mul_nonneg (by linarith [h.2]) hT3pos.le
    have k1' : 0 ≤ C * Real.log T - V * T ^ 3 := by linarith
    have k1 : 0 ≤ ((p : ℝ) ^ 2 - p) * (C * Real.log T - V * T ^ 3) := mul_nonneg hpp k1'
    have k2' : 0 ≤ (p : ℝ) * (C * Real.log T) - 2 * E * T ^ 3 := by linarith
    have k2 : 0 ≤ (p : ℝ) * ((p : ℝ) * (C * Real.log T) - 2 * E * T ^ 3) := mul_nonneg hq0 k2'
    have k3 : 0 ≤ (p : ℝ) * (C * Real.log T) := mul_nonneg hq0 hCl.le
    have k4' : 0 ≤ Real.log T := by linarith
    have k4 : 0 ≤ (p : ℝ) ^ 2 * Real.log T := mul_nonneg (sq_nonneg _) k4'
    linarith

end ChowlaOpus
