module

public import ChowlaOpus.Statements

@[expose] public section

/-!
# The kernel character mod `p²`

For an odd prime `p` we construct the Fermat-quotient character
`χ(u) = e((1 - u^(p-1)) / p²)` on `(ZMod (p²))ˣ`. Since `u^(p-1) ≡ 1 (mod p)`, the product
`(u^(p-1) - 1)(v^(p-1) - 1)` vanishes in `ZMod (p²)`, which makes `χ` multiplicative, and
`(1 + pt)^(p-1) = 1 - pt` in `ZMod (p²)` gives `χ(1 + pt) = e(t/p)`.
-/

open scoped FourierTransform ContDiff
open Real MeasureTheory

namespace ChowlaOpus.KCharAux

lemma one_add_pow {R : Type*} [CommRing R] (x : R) (hx : x ^ 2 = 0) (n : ℕ) :
    (1 + x) ^ n = 1 + (n : R) * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination (n : R) * hx

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in
lemma p_sq_eq_zero : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

lemma exists_mul_of_unit (u : (ZMod (p ^ 2))ˣ) :
    ∃ y : ℕ, (u : ZMod (p ^ 2)) ^ (p - 1) - 1 = (p : ZMod (p ^ 2)) * y := by
  set w : ZMod (p ^ 2) := (u : ZMod (p ^ 2)) ^ (p - 1) - 1 with hw
  have hdvd : p ∣ p ^ 2 := dvd_pow_self p two_ne_zero
  have hu : ((ZMod.castHom hdvd (ZMod p)) (u : ZMod (p ^ 2))) ≠ 0 :=
    ((u.isUnit.map (ZMod.castHom hdvd (ZMod p)))).ne_zero
  have h0 : ZMod.castHom hdvd (ZMod p) w = 0 := by
    rw [hw, map_sub, map_pow, map_one, ZMod.pow_card_sub_one_eq_one hu, sub_self]
  have h1 : ((w.val : ℕ) : ZMod p) = 0 := by
    rw [← h0, ZMod.castHom_apply, ZMod.cast_eq_val]
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨y, ?_⟩
  rw [← ZMod.natCast_zmod_val w, hy]
  push_cast; ring

lemma prod_eq_zero (u v : (ZMod (p ^ 2))ˣ) :
    ((u : ZMod (p ^ 2)) ^ (p - 1) - 1) * ((v : ZMod (p ^ 2)) ^ (p - 1) - 1) = 0 := by
  obtain ⟨a, ha⟩ := exists_mul_of_unit p u
  obtain ⟨b, hb⟩ := exists_mul_of_unit p v
  rw [ha, hb]
  linear_combination ((a : ZMod (p ^ 2)) * b) * p_sq_eq_zero p

/-- `u ↦ e((1 - u^(p-1)) / p²)` as a homomorphism of unit groups. -/
noncomputable def unitHom : (ZMod (p ^ 2))ˣ →* ℂˣ where
  toFun u := Units.mk0 (ZMod.stdAddChar (1 - (u : ZMod (p ^ 2)) ^ (p - 1)))
    (by rw [ZMod.stdAddChar_apply]; exact Circle.coe_ne_zero _)
  map_one' := by ext; simp
  map_mul' u v := by
    ext
    simp only [Units.val_mul, Units.val_mk0, mul_pow, ← AddChar.map_add_eq_mul]
    congr 1
    linear_combination -(prod_eq_zero p u v)

/-- The kernel character mod `p²`. -/
noncomputable def chi : MulChar (ZMod (p ^ 2)) ℂ := MulChar.ofUnitHom (unitHom p)

lemma chi_unit (u : (ZMod (p ^ 2))ˣ) :
    chi p (u : ZMod (p ^ 2)) = ZMod.stdAddChar (1 - (u : ZMod (p ^ 2)) ^ (p - 1)) := by
  rw [chi, MulChar.ofUnitHom_coe]
  rfl

lemma chi_one_add (t : ℤ) :
    chi p (((1 + (p : ℤ) * t : ℤ)) : ZMod (p ^ 2)) = ee ((t : ℝ) / p) := by
  set x : ZMod (p ^ 2) := (p : ZMod (p ^ 2)) * (t : ZMod (p ^ 2)) with hx
  have hx2 : x ^ 2 = 0 := by
    rw [hx, mul_pow, p_sq_eq_zero, zero_mul]
  have hcast : (((1 + (p : ℤ) * t : ℤ)) : ZMod (p ^ 2)) = 1 + x := by
    rw [hx]; push_cast; ring
  let u : (ZMod (p ^ 2))ˣ :=
    { val := 1 + x, inv := 1 - x,
      val_inv := by linear_combination -hx2,
      inv_val := by linear_combination -hx2 }
  have hu : (u : ZMod (p ^ 2)) = 1 + x := rfl
  rw [hcast, ← hu, chi_unit, hu, one_add_pow x hx2]
  have hp1 : 1 ≤ p := hp.out.one_le
  have h1 : 1 - (1 + ((p - 1 : ℕ) : ZMod (p ^ 2)) * x) = (((p : ℤ) * t : ℤ) : ZMod (p ^ 2)) := by
    rw [Nat.cast_sub hp1, hx]
    push_cast
    linear_combination -(t : ZMod (p ^ 2)) * p_sq_eq_zero p
  rw [h1, ZMod.stdAddChar_coe, ee]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  congr 1
  push_cast
  field_simp

lemma chi_neg_one (hp2 : p ≠ 2) : chi p (-1 : ZMod (p ^ 2)) = 1 := by
  have h : ((-1 : (ZMod (p ^ 2))ˣ) : ZMod (p ^ 2)) = -1 := by simp
  rw [← h, chi_unit, h]
  have hev : Even (p - 1) := hp.out.even_sub_one hp2
  rw [hev.neg_one_pow, sub_self, AddChar.map_zero_eq_one]

end ChowlaOpus.KCharAux

namespace ChowlaOpus

theorem kernelCharStatement_holds : KernelCharStatement := by
  intro p hp hp2
  have : Fact p.Prime := ⟨hp⟩
  exact ⟨KCharAux.chi p, KCharAux.chi_neg_one p hp2, KCharAux.chi_one_add p⟩

end ChowlaOpus
