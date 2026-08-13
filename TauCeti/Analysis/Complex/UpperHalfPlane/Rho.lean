/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# The elliptic points `i`, `ρ` and `ρ + 1` on the fundamental domain boundary

Mathlib gives `ρ` its square (`UpperHalfPlane.ρ_sq`) and its norm (`UpperHalfPlane.norm_ρ`).
This file adds how `ρ` behaves under the inversion `z ↦ -1/z`, which is what the two `ρ`-corners
of the standard fundamental domain need: the inversion swaps them, carrying `ρ` to `ρ + 1` and
back.

Both identities fall straight out of `ρ_sq : (ρ : ℂ) ^ 2 = -ρ - 1`, once the relevant denominator
is known to be nonzero — and `ρ + 1 ≠ 0` is itself read off from `-1 / ρ = ρ + 1`.

The file also collects the elementary values every consumer of the fundamental domain's boundary
needs for its three elliptic points — the corners `ρ`, `ρ + 1` and the arc midpoint `i`: the
real part of `ρ`, the pairwise distinctness of the three points, and their common unit modulus.

## Main results

* `UpperHalfPlane.neg_one_div_ρ`: the inversion carries `ρ` to `ρ + 1`.
* `UpperHalfPlane.neg_one_div_ρ_add_one`: the inversion carries `ρ + 1` to `ρ`.
* `UpperHalfPlane.re_ρ`, `UpperHalfPlane.norm_eq_one_of_mem_ellipticPoints` and the pairwise
  distinctness of `i`, `ρ`, `ρ + 1`.
-/

public section

open Complex

namespace UpperHalfPlane

/-- The inversion carries `ρ` to `ρ + 1`. -/
@[simp]
lemma neg_one_div_ρ : -1 / (ρ : ℂ) = (ρ : ℂ) + 1 := by
  rw [div_eq_iff (ne_zero ρ)]
  linear_combination -ρ_sq

/-- The second `ρ`-corner has unit modulus, like `ρ` itself: the inversion carries one to the
other and preserves the norm. -/
@[simp]
lemma norm_ρ_add_one : ‖(ρ : ℂ) + 1‖ = 1 := by
  rw [← neg_one_div_ρ, norm_div]
  simp [norm_ρ]

/-- The inversion carries `ρ + 1` to `ρ`. -/
@[simp]
lemma neg_one_div_ρ_add_one : -1 / ((ρ : ℂ) + 1) = (ρ : ℂ) := by
  rw [← neg_one_div_ρ]
  field_simp

/-- The real part of the corner `ρ`. -/
@[simp]
lemma re_ρ : ρ.re = -(1 / 2) := by
  rw [← coe_re]
  norm_num [ρ]

/-- The elliptic points `i` and `ρ` are distinct. -/
@[simp]
lemma I_ne_ρ : (I : ℍ) ≠ ρ :=
  ne_of_apply_ne UpperHalfPlane.re (by norm_num)

/-- The elliptic points `i` and `ρ + 1` are distinct. -/
@[simp]
lemma I_ne_vadd_ρ : (I : ℍ) ≠ (1 : ℝ) +ᵥ ρ :=
  ne_of_apply_ne UpperHalfPlane.re (by norm_num)

/-- The elliptic points `ρ` and `ρ + 1` are distinct. -/
@[simp]
lemma ρ_ne_vadd_ρ : (ρ : ℍ) ≠ (1 : ℝ) +ᵥ ρ :=
  ne_of_apply_ne UpperHalfPlane.re (by norm_num)

/-- The three elliptic points on the boundary of the fundamental domain — the corners `ρ`,
`ρ + 1` and the arc midpoint `i` — all lie on the unit circle. -/
lemma norm_eq_one_of_mem_ellipticPoints {z : ℂ}
    (hz : z ∈ ({Complex.I, (ρ : ℂ), (ρ : ℂ) + 1} : Finset ℂ)) : ‖z‖ = 1 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl | rfl
  · exact Complex.norm_I
  · exact norm_ρ
  · exact norm_ρ_add_one

end UpperHalfPlane
