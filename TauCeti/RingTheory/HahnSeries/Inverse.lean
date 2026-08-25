/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Summable

/-!
# `leadingCoeff` of inverses and quotients of Hahn series

Over a field of coefficients a nonzero Hahn series is invertible, and `HahnSeries.leadingCoeff` is
multiplicative (`HahnSeries.leadingCoeff_mul`). This file records what that gives for inversion and
division, which Mathlib states for products only.

There is deliberately no `orderTop` counterpart here. The other invariant already has one, and a
better one: `HahnSeries.addVal` is an `AddValuation` whose value is `orderTop`
(`HahnSeries.addVal_apply`), so `AddValuation.map_inv` and `AddValuation.map_div` give
`s⁻¹.orderTop = -s.orderTop` and `(s / t).orderTop = s.orderTop - t.orderTop` directly — and
without any nonzero hypothesis, since `-⊤ = ⊤` in the value group.

## Main results

* `HahnSeries.leadingCoeff_inv`: `s⁻¹.leadingCoeff = s.leadingCoeff⁻¹`.
* `HahnSeries.leadingCoeff_div`: `(s / t).leadingCoeff = s.leadingCoeff / t.leadingCoeff`.

Both hold with no nonzero hypothesis, since inversion and division by zero return zero on both
sides, and both are `@[simp]`.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/HahnSeriesAux.lean`, declarations `leadingCoeff_inv` and `leadingCoeff_div`. That file's
two further declarations, `orderTop_inv_eq_neg` and `orderTop_div`, are **not** ported: they are
the `addVal` consequences described above, which the source predates.
-/

public section

namespace HahnSeries

variable {Γ : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
variable {R : Type*} [Field R] {s t : HahnSeries Γ R}

/-- The leading coefficient of the inverse of a Hahn series over a field is the inverse of its
leading coefficient. No nonzero hypothesis is needed: at `s = 0` both sides are `0`. -/
@[simp]
theorem leadingCoeff_inv : s⁻¹.leadingCoeff = s.leadingCoeff⁻¹ := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  have hmul : (s * s⁻¹).leadingCoeff = s.leadingCoeff * s⁻¹.leadingCoeff := leadingCoeff_mul s s⁻¹
  rw [mul_inv_cancel₀ hs, leadingCoeff_one] at hmul
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm, ← hmul])

/-- The leading coefficient of a quotient of Hahn series over a field is the quotient of the
leading coefficients, with no nonzero hypothesis: at `t = 0` both sides are `0`. -/
@[simp]
theorem leadingCoeff_div : (s / t).leadingCoeff = s.leadingCoeff / t.leadingCoeff := by
  rw [div_eq_mul_inv, leadingCoeff_mul, leadingCoeff_inv, div_eq_mul_inv]

end HahnSeries
