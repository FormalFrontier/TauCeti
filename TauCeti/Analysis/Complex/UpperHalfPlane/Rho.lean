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
real part of `ρ`, the pairwise distinctness of the three points, their common unit modulus, the
coercion identity for the translated corner, and the unit-circle/real-part characterizations
that classify a boundary point as one of the three.

## Main results

* `UpperHalfPlane.neg_one_div_ρ`: the inversion carries `ρ` to `ρ + 1`.
* `UpperHalfPlane.neg_one_div_ρ_add_one`: the inversion carries `ρ + 1` to `ρ`.
* `UpperHalfPlane.re_ρ`, `UpperHalfPlane.norm_eq_one_of_mem_ellipticPoints` and the pairwise
  distinctness of `i`, `ρ`, `ρ + 1`.
* `UpperHalfPlane.coe_vadd_one_ρ`: the translated corner `(1 : ℝ) +ᵥ ρ` is `ρ + 1` in `ℂ`.
* `UpperHalfPlane.eq_I_of_re_eq_zero`, `UpperHalfPlane.eq_ρ_of_re_eq_neg_half`,
  `UpperHalfPlane.eq_vadd_one_ρ_of_re_eq_half`: a unit-circle point of `ℍ` with real part
  `0`, `-1/2`, `1/2` is `i`, `ρ`, `ρ + 1` respectively.
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

-- Not `@[simp]`: the simpNF linter rewrites the stated LHS through the unconditional simp
-- lemmas `coe_vadd` and `Complex.ofReal_one` to `1 + (ρ : ℂ)`, and restating at that normal
-- form would leave a bare commutativity instance. The lemma is the `rw`-oriented bridge to
-- the `ρ + 1` spelling the corner API uses throughout.
/-- The second corner `ρ + 1` as a point of `ℍ`, computed into `ℂ`. -/
lemma coe_vadd_one_ρ : (((1 : ℝ) +ᵥ ρ : ℍ) : ℂ) = (ρ : ℂ) + 1 := by
  rw [coe_vadd]
  push_cast
  ring

/-- A point of the unit circle with real part `0` is the elliptic point `i`. -/
lemma eq_I_of_re_eq_zero {p : ℍ} (hnorm : ‖(p : ℂ)‖ = 1) (hre : (p : ℂ).re = 0) :
    p = I := by
  have h1 : p.re = I.re := by rw [← coe_re, hre, I_re]
  have h2 : ‖(p : ℂ)‖ = ‖(I : ℂ)‖ := by rw [hnorm, coe_I, Complex.norm_I]
  exact eq_of_re_of_norm h1 h2

/-- A point of the unit circle with real part `-1/2` is the corner `ρ`. -/
lemma eq_ρ_of_re_eq_neg_half {p : ℍ} (hnorm : ‖(p : ℂ)‖ = 1) (hre : (p : ℂ).re = -(1 / 2)) :
    p = ρ := by
  have h1 : p.re = ρ.re := by rw [← coe_re, hre, re_ρ]
  have h2 : ‖(p : ℂ)‖ = ‖(ρ : ℂ)‖ := by rw [hnorm, norm_ρ]
  exact eq_of_re_of_norm h1 h2

/-- A point of the unit circle with real part `1/2` is the corner `ρ + 1`. -/
lemma eq_vadd_one_ρ_of_re_eq_half {p : ℍ} (hnorm : ‖(p : ℂ)‖ = 1) (hre : (p : ℂ).re = 1 / 2) :
    p = (1 : ℝ) +ᵥ ρ := by
  have h1 : p.re = ((1 : ℝ) +ᵥ ρ).re := by rw [← coe_re, hre, vadd_re, re_ρ]; norm_num
  have h2 : ‖(p : ℂ)‖ = ‖(((1 : ℝ) +ᵥ ρ : ℍ) : ℂ)‖ := by
    rw [hnorm, coe_vadd_one_ρ, norm_ρ_add_one]
  exact eq_of_re_of_norm h1 h2

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
