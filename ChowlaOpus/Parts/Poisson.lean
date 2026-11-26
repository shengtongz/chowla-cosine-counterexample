module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.PoissonAux

open Filter Asymptotics

lemma continuous_ee : Continuous ee := by
  unfold ee; fun_prop

lemma finite_support_shift (h : ℝ → ℂ) (hcs : HasCompactSupport h) (x : ℝ) :
    (Function.support fun m : ℤ => h (x + m)).Finite := by
  obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
  apply (Finset.Icc (-⌈R + |x|⌉) ⌈R + |x|⌉).finite_toSet.subset
  intro m hm
  have h1 : x + m ∈ tsupport h := subset_tsupport _ hm
  have h2 := hR h1
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h2
  have h3 : |(m : ℝ)| ≤ ⌈R + |x|⌉ := by
    have h4 : |(m:ℝ)| ≤ |x + m| + |x| := by
      have := abs_add_le (x + m) (-x)
      simp only [add_neg_cancel_comm, abs_neg] at this
      linarith
    linarith [Int.le_ceil (R + |x|)]
  have h5 : |m| ≤ ⌈R + |x|⌉ := by exact_mod_cast h3
  simp only [Finset.coe_Icc, Set.mem_Icc]
  exact abs_le.mp h5

lemma summable_shift (h : ℝ → ℂ) (hcs : HasCompactSupport h) (x : ℝ) :
    Summable fun m : ℤ => h (x + m) := by
  apply summable_of_ne_finset_zero (s := (finite_support_shift h hcs x).toFinset)
  intro m hm
  simpa using hm

lemma isBigO_of_hasCompactSupport (h : ℝ → ℂ) (hcs : HasCompactSupport h) (b : ℝ) :
    h =O[cocompact ℝ] (|·| ^ (-b)) := by
  have : h =ᶠ[cocompact ℝ] 0 := by
    filter_upwards [hcs.isCompact.compl_mem_cocompact] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  exact this.trans_isBigO (isBigO_zero _ _)

lemma summable_inv_one_add_sq_shift (a : ℝ) :
    Summable fun k : ℤ => 1 / (1 + ((k : ℝ) + a) ^ 2) := by
  have hs := (Real.summable_one_div_int_add_rpow a 2).mpr one_lt_two
  apply Summable.of_norm_bounded_eventually hs
  have hfin : {k : ℤ | (k : ℝ) + a = 0}.Subsingleton := by
    intro k hk l hl
    simp only [Set.mem_ofPred_eq] at hk hl
    exact_mod_cast (by linarith : (k : ℝ) = l)
  filter_upwards [hfin.finite.compl_mem_cofinite] with k hk
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hk
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), Real.rpow_two, sq_abs]
  apply one_div_le_one_div_of_le (by positivity)
  linarith

lemma summable_norm_decay (F : ℝ → ℂ) (K : ℝ) (hK : ∀ y, ‖F y‖ ≤ K / (1 + y ^ 2)) (a : ℝ) :
    Summable fun k : ℤ => ‖F (k + a)‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hK _) ?_
  exact ((summable_inv_one_add_sq_shift a).mul_left K).congr fun k => mul_one_div _ _

lemma fourier_modulate (f : ℝ → ℂ) (c w : ℝ) :
    𝓕 (fun x => f x * ee (x * c)) w = 𝓕 f (w - c) := by
  rw [fourier_eq_ee, fourier_eq_ee]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [mul_comm (f v), ← mul_assoc, ← ee_add]
  congr 2; ring

lemma poisson_core (h : ℝ → ℂ) (hc : Continuous h) (hcs : HasCompactSupport h)
    (hF : Summable fun n : ℤ => 𝓕 h n) (x : ℝ) :
    ∑' m : ℤ, h (x + m) = ∑' k : ℤ, 𝓕 h k * ee (k * x) := by
  have hb : (1 : ℝ) < 2 := one_lt_two
  have hO := isBigO_of_hasCompactSupport h hcs 2
  have := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable hc hb hO hF x
  rw [this]
  refine tsum_congr fun k => ?_
  rw [fourier_coe_apply]
  have he : 2 * (π : ℂ) * Complex.I * (k : ℂ) * (x : ℂ) / ((1 : ℝ) : ℂ) =
      2 * π * Complex.I * (((k : ℝ) * x : ℝ) : ℂ) := by
    push_cast; ring
  rw [he]
  rfl

end ChowlaOpus.PoissonAux

namespace ChowlaOpus

open PoissonAux

theorem fourierDecayStatement_holds : FourierDecayStatement := by
  intro f hf hcs
  have hint : ∀ k ≤ 2, Integrable (iteratedDeriv k f) := by
    intro k hk
    have hc : Continuous (iteratedDeriv k f) :=
      hf.continuous_iteratedDeriv k (by exact_mod_cast hk)
    have hs : HasCompactSupport (iteratedDeriv k f) := by
      rw [iteratedDeriv_eq_iterate]
      clear hc hk
      induction k with
      | zero => simpa using hcs
      | succ k ih => rw [Function.iterate_succ_apply']; exact ih.deriv
    exact hc.integrable_of_hasCompactSupport hs
  refine ⟨(∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * ∫ v, ‖iteratedDeriv 2 f v‖, ?_, ?_⟩
  · have h1 : 0 ≤ ∫ v, ‖f v‖ := integral_nonneg fun _ => norm_nonneg _
    have h2 : 0 ≤ ∫ v, ‖iteratedDeriv 2 f v‖ := integral_nonneg fun _ => norm_nonneg _
    positivity
  · intro y
    have := Real.one_add_sq_mul_norm_fourier_le hf hint y
    rw [le_div_iff₀ (by positivity), mul_comm]
    exact this

theorem plainPoissonStatement_holds : PlainPoissonStatement := by
  intro f K hc hcs hK y
  set g : ℝ → ℂ := fun x => f x * ee (x * (-y)) with hg
  have hgc : Continuous g := hc.mul (continuous_ee.comp (continuous_id.mul continuous_const))
  have hgcs : HasCompactSupport g := hcs.mul_right
  have hFg : ∀ w, 𝓕 g w = 𝓕 f (w + y) := by
    intro w; rw [hg, fourier_modulate, sub_neg_eq_add]
  have hsumF : Summable fun k : ℤ => 𝓕 f (k + y) :=
    (summable_norm_decay _ K hK y).of_norm
  have hgj : ∀ j : ℤ, f j * ee (-((j : ℝ) * y)) = g (0 + j) := by
    intro j; simp [hg]
  refine ⟨?_, ?_⟩
  · simp_rw [hgj]; exact summable_shift g hgcs 0
  · convert hsumF.hasSum using 1
    simp_rw [hgj]
    rw [poisson_core g hgc hgcs (by simpa [hFg] using hsumF) 0]
    simp [hFg, ee_zero]


theorem poissonStatement_holds : PoissonStatement := by
  intro p hp χ n f K hc hcs hK t
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp2 : (0 : ℤ) < (p : ℤ) ^ 2 := pow_pos (by exact_mod_cast hp.pos) 2
  obtain ⟨h, hh⟩ : ∃ h : ℝ → ℂ, h = fun x => f x * ee (x * ((p : ℝ) ^ 2 * t)) := ⟨_, rfl⟩
  have hhc : Continuous h := by
    rw [hh]; exact hc.mul (continuous_ee.comp (continuous_id.mul continuous_const))
  have hhcs : HasCompactSupport h := by rw [hh]; exact hcs.mul_right
  have hFh : ∀ w, 𝓕 h w = 𝓕 f (w - (p : ℝ) ^ 2 * t) := fun w => by rw [hh, fourier_modulate]
  have hsumF : Summable fun k : ℤ => ‖𝓕 h k‖ := by
    refine (summable_norm_decay _ K hK (-((p : ℝ) ^ 2 * t))).congr fun k => ?_
    rw [hFh, sub_eq_add_neg]
  set R := (Finset.range (p ^ 2)).filter (fun r => Nat.Coprime r p) with hR
  have hterm_sum : ∀ x : ℝ, Summable fun k : ℤ => 𝓕 h k * ee (k * x) := by
    intro x
    refine Summable.of_norm_bounded hsumF (fun k => ?_)
    rw [norm_mul, norm_ee, mul_one]
  have key : ∀ k : ℤ, 𝓕 f (k - (p : ℝ) ^ 2 * t) * rowSum p χ n k =
      ∑ r ∈ R, (χ (r : ZMod (p ^ 2))) ^ n * (𝓕 h k * ee (k * ((r : ℝ) / (p : ℝ) ^ 2))) := by
    intro k
    rw [rowSum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hFh, mul_div_assoc]; ring
  have hsumk : Summable fun k : ℤ => 𝓕 f (k - (p : ℝ) ^ 2 * t) * rowSum p χ n k := by
    simp_rw [key]
    exact summable_sum fun r _ => (hterm_sum _).mul_left _
  refine ⟨hsumk, ?_⟩
  have hRHS : ∑' k : ℤ, 𝓕 f (k - (p : ℝ) ^ 2 * t) * rowSum p χ n k =
      ∑ r ∈ R, (χ (r : ZMod (p ^ 2))) ^ n * ∑' m : ℤ, h ((r : ℝ) / (p : ℝ) ^ 2 + m) := by
    simp_rw [key]
    rw [Summable.tsum_finsetSum fun r _ => (hterm_sum _).mul_left _]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [tsum_mul_left, poisson_core h hhc hhcs hsumF.of_norm]
  rw [hRHS]
  set a : ℤ → ℂ := fun d => (if (p : ℤ) ∣ d then 0 else
          f ((d : ℝ) / (p : ℝ) ^ 2) * (χ (d : ZMod (p ^ 2))) ^ n) * ee (d * t) with ha
  set b : ℕ → ℤ → ℂ := fun r d => if d % ((p : ℤ) ^ 2) = r then a d else 0 with hb
  have hab : ∀ d, ∑ r ∈ R, b r d = a d := by
    intro d
    simp only [hb]
    obtain ⟨r0, hr0⟩ : ∃ r0 : ℕ, (r0 : ℤ) = d % (p : ℤ) ^ 2 :=
      ⟨_, Int.toNat_of_nonneg (Int.emod_nonneg _ hp2.ne')⟩
    have hiff : ∀ r : ℕ, (d % (p : ℤ) ^ 2 = (r : ℤ)) ↔ r0 = r := by
      intro r; rw [← hr0, Nat.cast_inj]
    simp_rw [hiff]
    rw [Finset.sum_ite_eq]
    split_ifs with hmem
    · rfl
    · have hlt : r0 < p ^ 2 := by
        have := Int.emod_lt_of_pos d hp2
        rw [← hr0] at this
        exact_mod_cast this
      have hnc : ¬ Nat.Coprime r0 p := by
        intro hc'
        exact hmem (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hc'⟩)
      have hpr : p ∣ r0 := by
        by_contra hnd
        exact hnc (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))
      have hpd : (p : ℤ) ∣ d := by
        have h1 : (p : ℤ) ∣ d % (p : ℤ) ^ 2 := by
          rw [← hr0]; exact Int.natCast_dvd_natCast.mpr hpr
        have h2 : (p : ℤ) ∣ (p : ℤ) ^ 2 * (d / (p : ℤ) ^ 2) :=
          Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _
        have := dvd_add h1 h2
        rwa [Int.emod_add_mul_ediv] at this
      simp [ha, hpd]
  have hbr : ∀ r ∈ R, HasSum (b r)
      ((χ (r : ZMod (p ^ 2))) ^ n * ∑' m : ℤ, h ((r : ℝ) / (p : ℝ) ^ 2 + m)) := by
    intro r hr
    have hrR := Finset.mem_filter.mp hr
    have hrlt : r < p ^ 2 := Finset.mem_range.mp hrR.1
    have hcop : Nat.Coprime r p := hrR.2
    have hginj : Function.Injective (fun m : ℤ => (r : ℤ) + (p : ℤ) ^ 2 * m) := by
      intro m1 m2 hm
      simp only at hm
      exact mul_left_cancel₀ hp2.ne' (add_left_cancel hm)
    have hout : ∀ d, d ∉ Set.range (fun m : ℤ => (r : ℤ) + (p : ℤ) ^ 2 * m) → b r d = 0 := by
      intro d hd
      simp only [hb]
      rw [ite_eq_right]
      intro hdr
      apply hd
      refine ⟨d / (p : ℤ) ^ 2, ?_⟩
      simp only
      rw [← hdr]; exact Int.emod_add_mul_ediv d _
    rw [← hginj.hasSum_iff hout]
    have hcomp : b r ∘ (fun m : ℤ => (r : ℤ) + (p : ℤ) ^ 2 * m) =
        fun m : ℤ => (χ (r : ZMod (p ^ 2))) ^ n * h ((r : ℝ) / (p : ℝ) ^ 2 + m) := by
      funext m
      simp only [Function.comp, hb]
      have hmod : ((r : ℤ) + (p : ℤ) ^ 2 * m) % (p : ℤ) ^ 2 = r := by
        rw [Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hrlt)
      rw [ite_eq_left hmod]
      have hndvd : ¬ (p : ℤ) ∣ (r : ℤ) + (p : ℤ) ^ 2 * m := by
        intro hdv
        have h2 : (p : ℤ) ∣ (p : ℤ) ^ 2 * m := Dvd.dvd.mul_right (dvd_pow_self _ two_ne_zero) _
        have h3 : (p : ℤ) ∣ (r : ℤ) := (dvd_add_left h2).mp hdv
        have h4 : p ∣ r := Int.natCast_dvd_natCast.mp h3
        exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.coprime_comm.mp hcop) h4
      simp only [ha, ite_eq_right hndvd]
      have hchi : χ ((((r : ℤ) + (p : ℤ) ^ 2 * m : ℤ)) : ZMod (p ^ 2)) = χ (r : ZMod (p ^ 2)) := by
        congr 1
        have hz : ((p : ZMod (p ^ 2))) ^ 2 = 0 := by exact_mod_cast ZMod.natCast_self (p ^ 2)
        push_cast
        rw [hz]; ring
      rw [hchi, hh]
      have e1 : (((r : ℤ) + (p : ℤ) ^ 2 * m : ℤ) : ℝ) / (p : ℝ) ^ 2 = (r : ℝ) / (p : ℝ) ^ 2 + m := by
        push_cast; field_simp
      have e2 : (((r : ℤ) + (p : ℤ) ^ 2 * m : ℤ) : ℝ) * t =
          ((r : ℝ) / (p : ℝ) ^ 2 + m) * ((p : ℝ) ^ 2 * t) := by
        push_cast; field_simp
      rw [e1, e2]; ring
    rw [hcomp]
    exact ((summable_shift h hhcs _).hasSum).mul_left _
  have hfin := hasSum_sum hbr
  convert hfin using 1
  funext d
  exact (hab d).symm

end ChowlaOpus
