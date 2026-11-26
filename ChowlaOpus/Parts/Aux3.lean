module

public import ChowlaOpus.Statements

@[expose] public section

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus

namespace Aux3Aux

open Finset Filter Topology

lemma continuous_ee : Continuous ee := by
  unfold ee; fun_prop

lemma ee_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ee (∑ i ∈ s, f i) = ∏ i ∈ s, ee (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ee_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ee_add, ih]

lemma measurable_saw (α : ℝ) : Measurable (saw α) := by
  show Measurable (fun t => ee (α * Int.fract t))
  exact continuous_ee.measurable.comp (measurable_const.mul measurable_fract)

lemma hasCompactSupport_of_supp {E : Type*} [Zero E] [TopologicalSpace E] (g : ℝ → E) (X : ℝ)
    (h : ∀ x, X < |x| → g x = 0) : HasCompactSupport g :=
  HasCompactSupport.intro (isCompact_Icc (a := -X) (b := X)) (fun x hx => h x (by
    by_contra hcon
    exact hx (abs_le.mp (not_lt.mp hcon))))

/-- The coefficient of the mode `v` (before multiplying by `b (v 0)`). -/
noncomputable def coef (J R : ℕ) (v : Fin (J + 1) → ℤ) : ℂ :=
  ∏ j : Fin J, (fejerCoeff R (v j.succ) : ℂ) * sawCoeff ((v 0 : ℝ) / ((j : ℝ) + 1)) (v j.succ)

/-- The box `[-J,J] × [-R,R]^J`. -/
def box (J R : ℕ) : Finset (Fin (J + 1) → ℤ) :=
  ((Finset.Icc (-(J : ℤ)) J) ×ˢ (Fintype.piFinset fun _ : Fin J => Finset.Icc (-(R : ℤ)) R)).image
    (fun p => (Fin.cons p.1 p.2 : Fin (J + 1) → ℤ))

/-- Structural condition on the modes. -/
def good (J : ℕ) (v : Fin (J + 1) → ℤ) : Prop :=
  (v 0 = 0 → ∀ j : Fin J, v j.succ = 0) ∧
    ∀ j : Fin J, ((j : ℤ) + 1 = |v 0| → v j.succ = (v 0).sign)

instance (J : ℕ) : DecidablePred (good J) := fun v => by unfold good; infer_instance

/-- The frequency set. -/
def Sset (J R : ℕ) : Finset (Fin (J + 1) → ℤ) := (box J R).filter (good J)

/-- Fejér-smoothed sawtooth multiplier. -/
noncomputable def Dfun (R : ℕ) (d u : ℝ) (l : ℤ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(R : ℤ)) R, (fejerCoeff R k : ℂ) * sawCoeff ((l : ℝ) / d) k * ee (k * u)

noncomputable def aR (R : ℕ) (α : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(R : ℤ)) R, fejerCoeff R k ^ 2 * ‖sawCoeff α k‖ ^ 2

noncomputable def AR (J R : ℕ) (l : ℤ) : ℝ := ∏ j : Fin J, aR R ((l : ℝ) / ((j : ℝ) + 1))

lemma mem_box {J R : ℕ} {v : Fin (J + 1) → ℤ} :
    v ∈ box J R ↔ v 0 ∈ Finset.Icc (-(J : ℤ)) J ∧
      ∀ j : Fin J, v j.succ ∈ Finset.Icc (-(R : ℤ)) R := by
  unfold box
  rw [Finset.mem_image]
  constructor
  · rintro ⟨⟨l, k⟩, hp, rfl⟩
    rw [Finset.mem_product, Fintype.mem_piFinset] at hp
    exact ⟨by simpa using hp.1, fun j => by simpa using hp.2 j⟩
  · rintro ⟨h0, hj⟩
    refine ⟨(v 0, Fin.tail v), ?_, Fin.cons_self_tail v⟩
    rw [Finset.mem_product, Fintype.mem_piFinset]
    exact ⟨h0, hj⟩

lemma box_sum {M : Type*} [CommSemiring M] (J R : ℕ) (g : ℤ → M) (h : ℤ → Fin J → ℤ → M) :
    ∑ v ∈ box J R, g (v 0) * ∏ j : Fin J, h (v 0) j (v j.succ) =
      ∑ l ∈ Finset.Icc (-(J : ℤ)) J, g l * ∏ j : Fin J, ∑ k ∈ Finset.Icc (-(R : ℤ)) R, h l j k := by
  unfold box
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← Finset.mul_sum, Finset.sum_prod_piFinset]
  · rintro ⟨l, k⟩ _ ⟨l', k'⟩ _ hlk
    obtain ⟨rfl, rfl⟩ := Fin.cons_inj.mp hlk
    rfl

lemma good_of_coef_ne (hS : SawStatement) {J R : ℕ} {v : Fin (J + 1) → ℤ}
    (h : coef J R v ≠ 0) : good J v := by
  have hfac : ∀ j : Fin J, sawCoeff ((v 0 : ℝ) / ((j : ℝ) + 1)) (v j.succ) ≠ 0 := by
    intro j hj
    apply h
    unfold coef
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, mul_zero])
  refine ⟨fun h0 j => ?_, fun j hj => ?_⟩
  · have h1 := hfac j
    rw [h0] at h1
    have h3 := hS.2.2.1 0 (v j.succ)
    simp only [Int.cast_zero, zero_div] at h1 h3
    rw [h3] at h1
    by_contra hne
    exact h1 (by simp [hne])
  · have hv0 : v 0 ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at hj
      omega
    have hv0' : (v 0 : ℝ) ≠ 0 := by exact_mod_cast hv0
    have hd : ((v 0 : ℝ) / ((j : ℝ) + 1)) = (((v 0).sign : ℤ) : ℝ) := by
      have hj' : ((j : ℝ) + 1) = |(v 0 : ℝ)| := by exact_mod_cast hj
      rw [hj']
      rcases lt_or_gt_of_ne hv0 with hneg | hpos
      · rw [Int.sign_eq_neg_one_of_neg hneg, abs_of_neg (by exact_mod_cast hneg), div_neg,
          div_self hv0']
        norm_num
      · rw [Int.sign_eq_one_of_pos hpos, abs_of_pos (by exact_mod_cast hpos), div_self hv0']
        norm_num
    have h1 := hfac j
    rw [hd, hS.2.2.1] at h1
    by_contra hne
    exact h1 (by simp [hne])

lemma coef_zero (hS : SawStatement) (J R : ℕ) : coef J R 0 = 1 := by
  unfold coef
  apply Finset.prod_eq_one
  intro j _
  have h3 := hS.2.2.1 0 0
  simp only [Int.cast_zero] at h3
  simp [fejerCoeff_zero, h3]

lemma coef_neg (hS : SawStatement) (J R : ℕ) (v : Fin (J + 1) → ℤ) :
    coef J R (-v) = starRingEnd ℂ (coef J R v) := by
  unfold coef
  rw [map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  simp only [Pi.neg_apply]
  rw [map_mul, Complex.conj_ofReal, fejerCoeff_neg, ← hS.2.1]
  rw [show (((-v 0 : ℤ)) : ℝ) / ((j : ℝ) + 1) = -((v 0 : ℝ) / ((j : ℝ) + 1)) by push_cast; ring]

lemma norm_sawCoeff_le (hS : SawStatement) (α : ℝ) (k : ℤ) : ‖sawCoeff α k‖ ≤ 1 := by
  have h := le_hasSum (hS.1 α) k (fun j _ => by positivity)
  have h0 : 0 ≤ ‖sawCoeff α k‖ := norm_nonneg _
  nlinarith

lemma norm_coef_le (hS : SawStatement) (J R : ℕ) (v : Fin (J + 1) → ℤ) : ‖coef J R v‖ ≤ 1 := by
  unfold coef
  rw [norm_prod]
  apply Finset.prod_le_one₀ (fun j _ => norm_nonneg _)
  intro j _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (fejerCoeff_nonneg _ _)]
  have h0 := norm_sawCoeff_le hS ((v 0 : ℝ) / ((j : ℝ) + 1)) (v j.succ)
  have h1 := fejerCoeff_le_one R (v j.succ)
  have h2 := fejerCoeff_nonneg R (v j.succ)
  nlinarith [norm_nonneg (sawCoeff ((v 0 : ℝ) / ((j : ℝ) + 1)) (v j.succ))]

lemma coef_mul_eq_zero (hS : SawStatement) {J R : ℕ} (β : ℤ → ℂ)
    (hβ : ∀ l, (J : ℤ) < |l| → β l = 0) {v : Fin (J + 1) → ℤ} (hv : v ∉ Sset J R) :
    coef J R v * β (v 0) = 0 := by
  unfold Sset at hv
  rw [Finset.mem_filter, not_and_or] at hv
  rcases hv with hv | hv
  · rw [mem_box, not_and_or] at hv
    rcases hv with hv | hv
    · rw [Finset.mem_Icc] at hv
      rw [hβ (v 0) (by rw [lt_abs]; omega), mul_zero]
    · push Not at hv
      obtain ⟨j, hj⟩ := hv
      rw [Finset.mem_Icc] at hj
      have hf : fejerCoeff R (v j.succ) = 0 := fejerCoeff_eq_zero R _ (by rw [lt_abs]; omega)
      unfold coef
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hf]; simp), zero_mul]
  · by_contra hne
    exact hv (good_of_coef_ne hS (left_ne_zero_of_mul hne))

lemma zero_mem_Sset (J R : ℕ) : (0 : Fin (J + 1) → ℤ) ∈ Sset J R := by
  unfold Sset
  rw [Finset.mem_filter, mem_box]
  refine ⟨⟨by simp, fun j => by simp⟩, fun _ j => rfl, fun j hj => ?_⟩
  rw [Pi.zero_apply, abs_zero] at hj
  omega

lemma neg_mem_Sset {J R : ℕ} {v : Fin (J + 1) → ℤ} (hv : v ∈ Sset J R) : -v ∈ Sset J R := by
  unfold Sset at hv ⊢
  rw [Finset.mem_filter, mem_box] at hv ⊢
  obtain ⟨⟨h0, hj⟩, g1, g2⟩ := hv
  simp only [Pi.neg_apply, Finset.mem_Icc] at h0 hj ⊢
  refine ⟨⟨⟨by omega, by omega⟩, fun j => ?_⟩, fun h j => ?_, fun j h => ?_⟩
  · have := hj j
    constructor <;> omega
  · have := g1 (by simpa using h) j
    rw [Pi.neg_apply, this, neg_zero]
  · simp only [Pi.neg_apply, abs_neg] at h ⊢
    rw [g2 j h, Int.sign_neg]

lemma trigEval_expand (hS : SawStatement) (J R : ℕ) (c : ℤ → ℂ) (θ : Fin (J + 1) → ℝ) :
    trigEval (Sset J R) (fun v => coef J R v * c (v 0)) θ =
      ∑ l ∈ Finset.Icc (-(J : ℤ)) J,
        c l * (∏ j : Fin J, Dfun R ((j : ℝ) + 1) (θ j.succ) l) * ee (l * θ 0) := by
  unfold trigEval Sset
  rw [Finset.sum_filter_of_ne (fun v _ hv => good_of_coef_ne hS (R := R) (by
    intro h0; apply hv; simp only [h0, zero_mul]))]
  have key : ∀ v : Fin (J + 1) → ℤ, coef J R v * c (v 0) * ee (∑ i, (v i : ℝ) * θ i) =
      (c (v 0) * ee ((v 0 : ℝ) * θ 0)) * ∏ j : Fin J, ((fejerCoeff R (v j.succ) : ℂ) *
        sawCoeff ((v 0 : ℝ) / ((j : ℝ) + 1)) (v j.succ) * ee ((v j.succ : ℝ) * θ j.succ)) := by
    intro v
    rw [Fin.sum_univ_succ, ee_add, ee_sum, Finset.prod_mul_distrib]
    unfold coef
    ring
  rw [Finset.sum_congr rfl (fun v _ => key v)]
  have hb := box_sum J R (fun l => c l * ee ((l : ℝ) * θ 0))
    (fun l j k => (fejerCoeff R k : ℂ) * sawCoeff ((l : ℝ) / ((j : ℝ) + 1)) k *
      ee ((k : ℝ) * θ j.succ))
  beta_reduce at hb
  rw [hb]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold Dfun
  ring

/-- Multipliers preserving a property of the label profile. -/
def MulPres (P : ℂ → Prop) (I : Finset ℤ) (D : ℤ → ℂ) : Prop :=
  ∀ c : ℤ → ℂ, (∀ s : ℝ, P (∑ l ∈ I, c l * ee (l * s))) →
    ∀ s : ℝ, P (∑ l ∈ I, c l * D l * ee (l * s))

lemma mulPres_prod {P : ℂ → Prop} {I : Finset ℤ} {ι : Type*} (s : Finset ι) (D : ι → ℤ → ℂ)
    (h : ∀ i ∈ s, MulPres P I (D i)) : MulPres P I (fun l => ∏ i ∈ s, D i l) := by
  have := Finset.prod_induction D (MulPres P I) ?_ ?_ h
  · have heq : (fun l => ∏ i ∈ s, D i l) = ∏ i ∈ s, D i := by
      funext l; rw [Finset.prod_apply]
    rw [heq]; exact this
  · intro D₁ D₂ h₁ h₂ c hc s'
    have := h₂ (fun l => c l * D₁ l) (h₁ c hc) s'
    simpa only [Pi.mul_apply, mul_assoc] using this
  · intro c hc s'
    simpa only [Pi.one_apply, mul_one] using hc s'

lemma intInt_fejer_mul_C (hF : FejerStatement) (R : ℕ) (u : ℝ) (h : ℝ → ℂ) (hm : Measurable h)
    (B : ℝ) (hb : ∀ t, ‖h t‖ ≤ B) :
    IntervalIntegrable (fun t => (fejer R (u - t) : ℂ) * h t) volume 0 1 := by
  have h1 : IntervalIntegrable h volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable B (ae_of_all _ hb))
  exact h1.continuousOn_mul (Complex.continuous_ofReal.comp
    ((hF.1 R).comp (continuous_const.sub continuous_id))).continuousOn

lemma intInt_fejer_mul_R (hF : FejerStatement) (R : ℕ) (u : ℝ) (h : ℝ → ℝ) (hm : Measurable h)
    (B : ℝ) (hb : ∀ t, ‖h t‖ ≤ B) :
    IntervalIntegrable (fun t => fejer R (u - t) * h t) volume 0 1 := by
  have h1 : IntervalIntegrable h volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (IntegrableOn.of_bound measure_Ioc_lt_top hm.aestronglyMeasurable B (ae_of_all _ hb))
  exact h1.continuousOn_mul ((hF.1 R).comp (continuous_const.sub continuous_id)).continuousOn

lemma fejer_shift_integral (hF : FejerStatement) (R : ℕ) (u : ℝ) :
    ∫ t in (0 : ℝ)..1, fejer R (u - t) = 1 := by
  rw [intervalIntegral.integral_comp_sub_left (fejer R) u]
  have hper : Function.Periodic (fejer R) 1 := fun t => hF.2.2.1 R t
  have h1 := hper.intervalIntegral_add_eq (u - 1) 0
  rw [sub_add_cancel, zero_add] at h1
  rw [sub_zero, h1]
  exact hF.2.2.2.2.1 R

lemma Dfun_sum_eq (hS : SawStatement) (hF : FejerStatement) (R : ℕ) (d u : ℝ) (I : Finset ℤ)
    (c : ℤ → ℂ) (s : ℝ) :
    ∑ l ∈ I, c l * Dfun R d u l * ee (l * s) =
      ∫ t in (0 : ℝ)..1, (fejer R (u - t) : ℂ) * ∑ l ∈ I, c l * ee (l * (s + Int.fract t / d)) := by
  have hD : ∀ l : ℤ, Dfun R d u l =
      ∫ t in (0 : ℝ)..1, (fejer R (u - t) : ℂ) * saw ((l : ℝ) / d) t :=
    fun l => hS.2.2.2 _ R u
  have hint : ∀ l : ℤ, IntervalIntegrable
      (fun t => (fejer R (u - t) : ℂ) * saw ((l : ℝ) / d) t) volume 0 1 :=
    fun l => intInt_fejer_mul_C hF R u _ (measurable_saw _) 1 (fun t => (norm_ee _).le)
  calc ∑ l ∈ I, c l * Dfun R d u l * ee (l * s)
      = ∑ l ∈ I, ∫ t in (0 : ℝ)..1,
          (c l * ee (l * s)) * ((fejer R (u - t) : ℂ) * saw ((l : ℝ) / d) t) := by
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [intervalIntegral.integral_const_mul, hD]; ring
    _ = ∫ t in (0 : ℝ)..1, ∑ l ∈ I,
          (c l * ee (l * s)) * ((fejer R (u - t) : ℂ) * saw ((l : ℝ) / d) t) := by
        rw [intervalIntegral.integral_finsetSum]
        intro l _
        exact (hint l).const_mul _
    _ = _ := by
        congr 1; ext t
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        unfold saw
        rw [show (l : ℝ) * (s + Int.fract t / d) = (l : ℝ) / d * Int.fract t + l * s by ring,
          ee_add]
        ring

def P1 (z : ℂ) : Prop := z.im = 0 ∧ 0 ≤ z.re ∧ z.re ≤ 1

def P2 (z : ℂ) : Prop := z.im = 0 ∧ 0 ≤ z.re

lemma avg_P1 (hF : FejerStatement) (R : ℕ) (u : ℝ) (G : ℝ → ℂ) (hG : Measurable G)
    (hP : ∀ t, P1 (G t)) : P1 (∫ t in (0 : ℝ)..1, (fejer R (u - t) : ℂ) * G t) := by
  have heq : (fun t => (fejer R (u - t) : ℂ) * G t) =
      fun t => ((fejer R (u - t) * (G t).re : ℝ) : ℂ) := by
    funext t
    apply Complex.ext <;> simp [(hP t).1]
  rw [heq, intervalIntegral.integral_ofReal]
  have hw : ∫ t in (0 : ℝ)..1, fejer R (u - t) = 1 := fejer_shift_integral hF R u
  refine ⟨Complex.ofReal_im _, ?_, ?_⟩
  · rw [Complex.ofReal_re]
    exact intervalIntegral.integral_nonneg zero_le_one
      (fun t _ => mul_nonneg (hF.2.1 R _) (hP t).2.1)
  · rw [Complex.ofReal_re]
    refine le_trans ?_ hw.le
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact intInt_fejer_mul_R hF R u _ (Complex.measurable_re.comp hG) 1 (fun t => by
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith [(hP t).2.1, (hP t).2.2])
    · exact ((hF.1 R).comp (continuous_const.sub continuous_id)).intervalIntegrable _ _
    · intro t _
      exact mul_le_of_le_one_right (hF.2.1 R _) (hP t).2.2

lemma avg_P2 (hF : FejerStatement) (R : ℕ) (u : ℝ) (G : ℝ → ℂ)
    (hP : ∀ t, P2 (G t)) : P2 (∫ t in (0 : ℝ)..1, (fejer R (u - t) : ℂ) * G t) := by
  have heq : (fun t => (fejer R (u - t) : ℂ) * G t) =
      fun t => ((fejer R (u - t) * (G t).re : ℝ) : ℂ) := by
    funext t
    apply Complex.ext <;> simp [(hP t).1]
  rw [heq, intervalIntegral.integral_ofReal]
  refine ⟨Complex.ofReal_im _, ?_⟩
  rw [Complex.ofReal_re]
  exact intervalIntegral.integral_nonneg zero_le_one
    (fun t _ => mul_nonneg (hF.2.1 R _) (hP t).2)

lemma measurable_shifted (I : Finset ℤ) (c : ℤ → ℂ) (s d : ℝ) :
    Measurable (fun t : ℝ => ∑ l ∈ I, c l * ee (l * (s + Int.fract t / d))) := by
  have hcont : Continuous (fun s' : ℝ => ∑ l ∈ I, c l * ee (l * s')) :=
    continuous_finsetSum _ (fun l _ => continuous_const.mul
      (continuous_ee.comp (continuous_const.mul continuous_id)))
  exact hcont.measurable.comp (measurable_const.add (measurable_fract.div_const d))

lemma mulPres_Dfun_P1 (hS : SawStatement) (hF : FejerStatement) (R : ℕ) (d u : ℝ)
    (I : Finset ℤ) : MulPres P1 I (Dfun R d u) := by
  intro c hc s
  rw [Dfun_sum_eq hS hF R d u I c s]
  exact avg_P1 hF R u _ (measurable_shifted I c s d) (fun t => hc _)

lemma mulPres_Dfun_P2 (hS : SawStatement) (hF : FejerStatement) (R : ℕ) (d u : ℝ)
    (I : Finset ℤ) : MulPres P2 I (Dfun R d u) := by
  intro c hc s
  rw [Dfun_sum_eq hS hF R d u I c s]
  exact avg_P2 hF R u _ (fun t => hc _)

lemma sum_normsq (hS : SawStatement) (J R : ℕ) (β : ℤ → ℂ) :
    ∑ v ∈ Sset J R, ‖coef J R v * β (v 0)‖ ^ 2 =
      ∑ l ∈ Finset.Icc (-(J : ℤ)) J, AR J R l * ‖β l‖ ^ 2 := by
  unfold Sset
  rw [Finset.sum_filter_of_ne (fun v _ hv => good_of_coef_ne hS (R := R) (by
    intro h0; apply hv; simp only [h0, zero_mul, norm_zero]; ring))]
  have key : ∀ v : Fin (J + 1) → ℤ, ‖coef J R v * β (v 0)‖ ^ 2 =
      ‖β (v 0)‖ ^ 2 * ∏ j : Fin J, (fejerCoeff R (v j.succ) ^ 2 *
        ‖sawCoeff ((v 0 : ℝ) / ((j : ℝ) + 1)) (v j.succ)‖ ^ 2) := by
    intro v
    unfold coef
    rw [norm_mul, mul_pow, norm_prod, ← Finset.prod_pow, mul_comm]
    congr 1
    refine Finset.prod_congr rfl (fun j _ => ?_)
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg (fejerCoeff_nonneg _ _)]
  rw [Finset.sum_congr rfl (fun v _ => key v)]
  have hb := box_sum J R (fun l => ‖β l‖ ^ 2)
    (fun l j k => fejerCoeff R k ^ 2 * ‖sawCoeff ((l : ℝ) / ((j : ℝ) + 1)) k‖ ^ 2)
  beta_reduce at hb
  rw [hb]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  unfold AR aR
  ring

lemma tendsto_fejerCoeff (k : ℤ) : Tendsto (fun R : ℕ => fejerCoeff R k) atTop (𝓝 1) := by
  have h1 : Tendsto (fun R : ℕ => |(k : ℝ)| / ((R : ℝ) + 1)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul |(k : ℝ)|
    rw [mul_zero] at this
    refine this.congr (fun R => ?_)
    ring
  have h2 : Tendsto (fun R : ℕ => max 0 (1 - |(k : ℝ)| / ((R : ℝ) + 1))) atTop
      (𝓝 (max 0 (1 - 0))) :=
    tendsto_const_nhds.max (tendsto_const_nhds.sub h1)
  have h3 : max (0 : ℝ) (1 - 0) = 1 := by norm_num
  rw [h3] at h2
  exact h2

lemma tendsto_aR (hS : SawStatement) (α : ℝ) : Tendsto (fun R : ℕ => aR R α) atTop (𝓝 1) := by
  have heq : ∀ R : ℕ, aR R α = ∑' k : ℤ, fejerCoeff R k ^ 2 * ‖sawCoeff α k‖ ^ 2 := by
    intro R
    unfold aR
    rw [tsum_eq_sum (s := Finset.Icc (-(R : ℤ)) R)]
    intro k hk
    rw [Finset.mem_Icc, not_and_or] at hk
    rw [fejerCoeff_eq_zero R k (by rw [lt_abs]; omega)]
    ring
  have hab : ∀ k : ℤ, Tendsto (fun R : ℕ => fejerCoeff R k ^ 2 * ‖sawCoeff α k‖ ^ 2) atTop
      (𝓝 (‖sawCoeff α k‖ ^ 2)) := by
    intro k
    have := ((tendsto_fejerCoeff k).pow 2).mul_const (‖sawCoeff α k‖ ^ 2)
    rwa [one_pow, one_mul] at this
  have hbound : ∀ᶠ R : ℕ in atTop, ∀ k : ℤ,
      ‖fejerCoeff R k ^ 2 * ‖sawCoeff α k‖ ^ 2‖ ≤ ‖sawCoeff α k‖ ^ 2 := by
    refine Eventually.of_forall (fun R k => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have h0 := fejerCoeff_nonneg R k
    have h1 := fejerCoeff_le_one R k
    have : fejerCoeff R k ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg ‖sawCoeff α k‖]
  have h := tendsto_tsum_of_dominated_convergence
    (f := fun (R : ℕ) (k : ℤ) => fejerCoeff R k ^ 2 * ‖sawCoeff α k‖ ^ 2)
    (g := fun k => ‖sawCoeff α k‖ ^ 2) (bound := fun k => ‖sawCoeff α k‖ ^ 2)
    (hS.1 α).summable hab hbound
  beta_reduce at h
  rw [(hS.1 α).tsum_eq] at h
  exact h.congr (fun R => (heq R).symm)

lemma tendsto_AR (hS : SawStatement) (J : ℕ) (l : ℤ) :
    Tendsto (fun R : ℕ => AR J R l) atTop (𝓝 1) := by
  unfold AR
  have := tendsto_finsetProd (Finset.univ : Finset (Fin J))
    (fun j _ => tendsto_aR hS ((l : ℝ) / ((j : ℝ) + 1)))
  simpa using this

lemma fourier_const_mul (a : ℂ) (f : ℝ → ℂ) (y : ℝ) :
    𝓕 (fun x => a * f x) y = a * 𝓕 f y := by
  rw [fourier_eq_ee, fourier_eq_ee, ← integral_const_mul]
  congr 1; ext v; ring

lemma nonprop_aux {J R : ℕ} (v w : Fin (J + 1) → ℤ) (hv : v ∈ Sset J R) (hw : w ∈ Sset J R)
    (hv0 : 0 < v 0) (hw0 : 0 < w 0) (h : ∀ i j, v i * w j = v j * w i) : v = w := by
  unfold Sset at hv hw
  rw [Finset.mem_filter, mem_box] at hv hw
  obtain ⟨⟨hv1, -⟩, -, hv2⟩ := hv
  obtain ⟨⟨hw1, -⟩, -, hw2⟩ := hw
  rw [Finset.mem_Icc] at hv1 hw1
  have hJv : (v 0).toNat - 1 < J := by omega
  have hJw : (w 0).toNat - 1 < J := by omega
  obtain ⟨a, ha_def⟩ : ∃ a : Fin J, (a : ℤ) + 1 = v 0 :=
    ⟨⟨(v 0).toNat - 1, hJv⟩, by show (((v 0).toNat - 1 : ℕ) : ℤ) + 1 = v 0; omega⟩
  obtain ⟨b, hb_def⟩ : ∃ b : Fin J, (b : ℤ) + 1 = w 0 :=
    ⟨⟨(w 0).toNat - 1, hJw⟩, by show (((w 0).toNat - 1 : ℕ) : ℤ) + 1 = w 0; omega⟩
  have ha : v a.succ = 1 := by
    rw [hv2 a (by rw [abs_of_pos hv0]; exact ha_def), Int.sign_eq_one_of_pos hv0]
  have hb : w b.succ = 1 := by
    rw [hw2 b (by rw [abs_of_pos hw0]; exact hb_def), Int.sign_eq_one_of_pos hw0]
  have e1 := h 0 a.succ
  have e2 := h 0 b.succ
  rw [ha] at e1
  rw [hb] at e2
  have hwa : 0 < w a.succ := by
    by_contra hneg
    push Not at hneg
    nlinarith
  have hprod : v b.succ * w a.succ = 1 := by
    have h4 : v 0 * (v b.succ * w a.succ - 1) = 0 := by linear_combination (v b.succ) * e1 - e2
    rcases mul_eq_zero.mp h4 with h0 | h0
    · omega
    · linarith
  have hwa1 : w a.succ = 1 := Int.eq_one_of_mul_eq_one_left hwa.le hprod
  have hvw0 : w 0 = v 0 := by rw [hwa1] at e1; linarith
  funext i
  have e3 := h 0 i
  rw [hvw0] at e3
  have h5 : v 0 * (w i - v i) = 0 := by linear_combination e3
  rcases mul_eq_zero.mp h5 with h0 | h0
  · omega
  · linarith

end Aux3Aux

open Aux3Aux Finset Filter Topology

theorem profileStatement_holds (h3 : Lemma3Statement) (hS : SawStatement)
    (hF : FejerStatement) (hD : FourierDecayStatement) : ProfileStatement := by
  obtain ⟨C, c, hC, hc, T₀, hT₀⟩ := h3
  refine ⟨C + 1, c, by linarith, hc, max T₀ 3, fun T hT => ?_⟩
  obtain ⟨J, b, hbJ, hbsmooth, hbsupp, hbeven, hbconj, hb0, hfb0, hsum, htsum, hmass, hW, hQ,
    hvar⟩ := hT₀ T (le_trans (le_max_left _ _) hT)
  have hT3 : 3 ≤ T := le_trans (le_max_right _ _) hT
  have hpos : 0 < Real.log T / T ^ 3 :=
    div_pos (Real.log_pos (by linarith)) (by positivity)
  have hbcs : ∀ l, HasCompactSupport (b l) := fun l => hasCompactSupport_of_supp _ _ (hbsupp l)
  have hbcont : ∀ l, Continuous (b l) := fun l => (hbsmooth l).continuous
  have hMint : ∀ l, Integrable (fun x => ‖b l x‖ ^ 2) := fun l =>
    ((hbcont l).norm.pow 2).integrable_of_hasCompactSupport
      (hasCompactSupport_of_supp _ (T ^ 2) (fun x hx => by simp [hbsupp l x hx]))
  have hb0int : Integrable (fun x => (b 0 x).re) :=
    (Complex.continuous_re.comp (hbcont 0)).integrable_of_hasCompactSupport
      (hasCompactSupport_of_supp _ (T ^ 2) (fun x hx => by simp [hbsupp 0 x hx]))
  have hE : Tendsto (fun R : ℕ => ∑ l ∈ Finset.Icc (-(J : ℤ)) J,
      (1 - AR J R l) * ∫ x, ‖b l x‖ ^ 2) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.Icc (-(J : ℤ)) J) (fun l _ =>
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_AR hS J l)).mul_const
        (∫ x, ‖b l x‖ ^ 2))
    simpa using this
  obtain ⟨R, hR⟩ := (hE.eventually (gt_mem_nhds hpos)).exists
  choose K hK0 hK using fun l => hD (b l) (hbsmooth l) (hbcs l)
  have hcoef0 := coef_zero hS J R
  refine ⟨J, Sset J R, fun v x => coef J R v * b (v 0) x, ∑ l ∈ Finset.Icc (-(J : ℤ)) J, K l,
    ?_, ?_, ?_, ?_, ?_⟩
  · refine
      { zero_mem := zero_mem_Sset J R
        neg_mem := fun v hv => neg_mem_Sset hv
        label_ne := ?_
        nonprop := fun v hv w hw hv0 hw0 h => nonprop_aux v w hv hw hv0 hw0 h
        zero_off := ?_
        smooth := fun v => contDiff_const.mul (hbsmooth (v 0))
        supp := ?_
        even := ?_
        conj := ?_
        decay := ?_
        b0 := ?_
        fourier_b0 := ?_
        range := ?_
        pos := ?_ }
    · intro v hv hne h0
      apply hne
      unfold Sset at hv
      rw [Finset.mem_filter] at hv
      have hz := hv.2.1 h0
      funext i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact h0
      · exact hz j
    · intro v hv
      funext x
      exact coef_mul_eq_zero hS (fun l => b l x) (fun l hl => by
        show b l x = 0
        rw [hbJ l hl]; rfl) hv
    · intro v x hx
      show coef J R v * b (v 0) x = 0
      rw [hbsupp _ x hx, mul_zero]
    · intro v x
      show coef J R v * b (v 0) (-x) = coef J R v * b (v 0) x
      rw [hbeven]
    · intro v x
      show coef J R (-v) * b ((-v) 0) x = starRingEnd ℂ (coef J R v * b (v 0) x)
      rw [coef_neg hS, Pi.neg_apply, hbconj, map_mul]
    · intro v y
      show ‖𝓕 (fun x => coef J R v * b (v 0) x) y‖ ≤ _
      rw [fourier_const_mul, norm_mul]
      have h1 := norm_coef_le hS J R v
      have h2 : ‖𝓕 (b (v 0)) y‖ ≤ (∑ l ∈ Finset.Icc (-(J : ℤ)) J, K l) / (1 + y ^ 2) := by
        by_cases hl : v 0 ∈ Finset.Icc (-(J : ℤ)) J
        · calc ‖𝓕 (b (v 0)) y‖ ≤ K (v 0) / (1 + y ^ 2) := hK _ y
            _ ≤ _ := by
              gcongr
              exact Finset.single_le_sum (fun l _ => hK0 l) hl
        · have hz : b (v 0) = 0 := hbJ _ (by rw [Finset.mem_Icc] at hl; rw [lt_abs]; omega)
          rw [hz]
          have h0 : 𝓕 (0 : ℝ → ℂ) y = 0 := by rw [fourier_eq_ee]; simp
          rw [h0, norm_zero]
          exact div_nonneg (Finset.sum_nonneg (fun l _ => hK0 l)) (by positivity)
      calc ‖coef J R v‖ * ‖𝓕 (b (v 0)) y‖ ≤ 1 * ‖𝓕 (b (v 0)) y‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact h2
    · intro x
      simp only [hcoef0, one_mul, Pi.zero_apply]
      exact hb0 x
    · intro y
      simp only [hcoef0, one_mul, Pi.zero_apply]
      exact hfb0 y
    · intro θ x
      show P1 (trigEval (Sset J R) (fun v => coef J R v * (fun l => b l x) (v 0)) θ)
      rw [trigEval_expand hS J R (fun l => b l x) θ]
      exact mulPres_prod _ _ (fun j _ => mulPres_Dfun_P1 hS hF R _ _ _) (fun l => b l x)
        (fun s => hW s x) (θ 0)
    · intro θ y
      have hfun : (fun v : Fin (J + 1) → ℤ => mult (2 * Real.pi * v 0 / T) *
          𝓕 (fun x => coef J R v * b (v 0) x) y) =
          fun v => coef J R v * (fun l : ℤ => mult (2 * Real.pi * l / T) * 𝓕 (b l) y) (v 0) := by
        funext v
        rw [fourier_const_mul]; ring
      show P2 (trigEval (Sset J R) (fun v : Fin (J + 1) → ℤ => mult (2 * Real.pi * v 0 / T) *
          𝓕 (fun x => coef J R v * b (v 0) x) y) θ)
      rw [hfun, trigEval_expand hS J R (fun l : ℤ => mult (2 * Real.pi * l / T) * 𝓕 (b l) y) θ]
      exact mulPres_prod _ _ (fun j _ => mulPres_Dfun_P2 hS hF R _ _ _) _
        (fun s => hQ s y) (θ 0)
  · simpa [hcoef0] using hsum
  · have h6 : C * Real.log T / T ≤ (C + 1) * Real.log T / T := by
      have : 0 < Real.log T / T := div_pos (Real.log_pos (by linarith)) (by linarith)
      rw [mul_div_assoc, mul_div_assoc]; nlinarith
    simpa [hcoef0] using htsum.trans h6
  · simpa [hcoef0] using hmass
  · have hpt : (fun x => (coef J R 0 * b ((0 : Fin (J + 1) → ℤ) 0) x).re -
        ∑ v ∈ Sset J R, ‖coef J R v * b (v 0) x‖ ^ 2) =
        fun x => ((b 0 x).re - ∑ l ∈ Finset.Icc (-(J : ℤ)) J, ‖b l x‖ ^ 2) +
          ∑ l ∈ Finset.Icc (-(J : ℤ)) J, (1 - AR J R l) * ‖b l x‖ ^ 2 := by
      funext x
      rw [sum_normsq hS J R (fun l => b l x), hcoef0, one_mul, Pi.zero_apply]
      simp only [sub_mul, one_mul, Finset.sum_sub_distrib]
      ring
    show ∫ x, ((coef J R 0 * b ((0 : Fin (J + 1) → ℤ) 0) x).re -
        ∑ v ∈ Sset J R, ‖coef J R v * b (v 0) x‖ ^ 2) ≤ _
    rw [hpt, integral_add, integral_finsetSum]
    · simp_rw [integral_const_mul]
      have h5 : (C + 1) * Real.log T / T ^ 3 = C * Real.log T / T ^ 3 + Real.log T / T ^ 3 := by
        ring
      rw [h5]
      linarith [hvar, hR]
    · intro l _
      exact (hMint l).const_mul _
    · exact hb0int.sub (integrable_finsetSum _ (fun l _ => hMint l))
    · exact integrable_finsetSum _ (fun l _ => (hMint l).const_mul _)

end ChowlaOpus
