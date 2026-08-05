/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Totally complex number fields from a negative square

A number field containing an element whose square is a negative rational is totally complex: a real
embedding would send that element to a real square root of a negative number.

## Main results

* `TauCeti.NumberField.isTotallyComplex_of_sq_ratCast_of_neg`.
-/

public section

open NumberField NumberField.InfinitePlace

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **A field with a negative square is totally complex.** If some `x : K` has `x² = r` for a
negative rational `r`, then every infinite place of `K` is complex. -/
theorem isTotallyComplex_of_sq_ratCast_of_neg {x : K} {r : ℚ} (hx2 : x ^ 2 = algebraMap ℚ K r)
    (hr : r < 0) : IsTotallyComplex K := by
  -- A real embedding would carry `x` to a real square root of `r < 0`, which is impossible.
  rw [isTotallyComplex_iff]
  intro w
  rw [isComplex_iff]
  intro hφ
  have hφsq : (embedding w) x ^ 2 = (r : ℂ) := by
    rw [← map_pow, hx2]; simp [map_ratCast]
  have hψsq : (hφ.embedding x) ^ 2 = (r : ℝ) := by
    have h : (((hφ.embedding x) ^ 2 : ℝ) : ℂ) = (r : ℂ) := by
      push_cast [hφ.coe_embedding_apply]; rw [hφsq]
    exact_mod_cast h
  have hrR : (r : ℝ) < 0 := by exact_mod_cast hr
  nlinarith [sq_nonneg (hφ.embedding x), hψsq, hrR]

end TauCeti.NumberField
