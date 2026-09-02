/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Rigidity of surjective `ℤᵐ⁰`-valued valuations

Equivalent valuations differ, in general, by an order isomorphism of their value groups. When
the value group is `ℤᵐ⁰ = WithZero (Multiplicative ℤ)` and both valuations are surjective there
is no room left for such an isomorphism: `WithZero.exp (-1)` is the largest element of `ℤᵐ⁰`
below `1`, so both valuations take it at the same elements, and every other value is then
determined multiplicatively.

This rigidity is what makes a *normalized* valuation canonical: a surjective `ℤᵐ⁰`-valued
representative of a valuation class is unique, so any construction of one — however many
arbitrary choices it makes internally — produces the same valuation.

## Main results

* `Valuation.IsEquiv.eq_of_surjective`: two equivalent surjective valuations `K → ℤᵐ⁰` on a
  division ring `K` are equal.
-/

public section

open WithZero

namespace Valuation

variable {K : Type*} [DivisionRing K] {v w : Valuation K ℤᵐ⁰}

/-- If `v` and `w` are equivalent and `v` is surjective, then `v` takes the value `exp (-1)`
wherever `w` does: no value of `v` fits strictly between `exp (-1)` and `1`. -/
private theorem eq_exp_neg_one_of_isEquiv (h : v.IsEquiv w) (hv : Function.Surjective v) {a : K}
    (ha : w a = exp (-1)) : v a = exp (-1) := by
  have hva : v a ≠ 0 := by simp [h.eq_zero, ha]
  obtain ⟨m, hm⟩ : ∃ m : ℤ, v a = exp m := ⟨log (v a), (exp_log hva).symm⟩
  have hm0 : m < 0 := by
    have : v a < 1 := by simp [h.lt_one_iff_lt_one, ha]
    simpa [hm] using this
  by_contra hne
  rw [hm] at hne
  simp only [exp_inj] at hne
  obtain ⟨b, hb⟩ := hv (exp (-1))
  have hwb : w a < w b := h.lt_iff_lt.mp (by rw [hm, hb]; simpa using lt_of_le_of_ne (by omega) hne)
  obtain ⟨n, hn⟩ : ∃ n : ℤ, w b = exp n := by
    refine ⟨log (w b), (exp_log ?_).symm⟩
    simp [← h.eq_zero, hb]
  have hn0 : n < 0 := by
    have : w b < 1 := by simp [← h.lt_one_iff_lt_one, hb]
    simpa [hn] using this
  rw [ha, hn, exp_lt_exp] at hwb
  omega

/-- Two equivalent surjective valuations with values in `ℤᵐ⁰` are equal.

`ℤᵐ⁰` admits no nontrivial order-preserving multiplicative automorphism, so a surjective
valuation into it is determined by its equivalence class. -/
theorem IsEquiv.eq_of_surjective (h : v.IsEquiv w) (hv : Function.Surjective v)
    (hw : Function.Surjective w) : v = w := by
  obtain ⟨a, ha⟩ := hw (exp (-1))
  have hva : v a = exp (-1) := eq_exp_neg_one_of_isEquiv h hv ha
  ext x
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hwx : w x ≠ 0 := by simpa using hx0
  obtain ⟨m, hwm⟩ : ∃ m : ℤ, w x = exp m := ⟨log (w x), (exp_log hwx).symm⟩
  have hw1 : w (x * a ^ m) = 1 := by
    rw [map_mul, map_zpow₀, ha, hwm, ← exp_zsmul, ← exp_add]
    simp
  have hv1 : v (x * a ^ m) = 1 := h.eq_one_iff_eq_one.mpr hw1
  have haz : v (a ^ m) = w (a ^ m) := by rw [map_zpow₀, map_zpow₀, ha, hva]
  refine mul_right_cancel₀ (b := v (a ^ m)) (by simp [map_zpow₀, hva]) ?_
  rw [← map_mul, hv1, haz, ← map_mul, hw1]

end Valuation
