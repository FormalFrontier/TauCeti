/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Conjugation.Basic

/-!
# Integral Hilbert 90 for quadratic conjugation

This file proves Hilbert's Theorem 90 for quadratic conjugation in the integral form needed for
ideal-class descent. Mathlib provides `groupCohomology.exists_div_of_norm_eq_one`; for a quadratic
extension the elementary construction here gives an element of `𝓞 K` rather than merely of `K`.

## Main result

* `NumberField.exists_ne_zero_mul_eq_mul_ringOfIntegersQuadraticConj`: if nonzero `x : 𝓞 K` and
  `y : 𝓞 K` have equal products with their conjugates, there is nonzero `ε : 𝓞 K` satisfying
  `x ε = y σε`.
-/

public section

open Polynomial NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **Hilbert's Theorem 90 for quadratic conjugation.** Let `σ` be the quadratic conjugation of a
quadratic number field and let `x y : 𝓞 K` with `x ≠ 0` have equal norms, `x σx = y σy`. Then there
is a nonzero `ε : 𝓞 K` with `x ε = y σε`; equivalently `y / x = ε / σε` is a "coboundary". The
construction is explicit: `ε = σx (x + y)` works unless `x + y = 0`, and then `ε = σx θ x` does. -/
theorem exists_ne_zero_mul_eq_mul_ringOfIntegersQuadraticConj
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) {x y : 𝓞 K}
    (hx : x ≠ 0)
    (hnorm : x * ringOfIntegersQuadraticConj hmin hgen x =
      y * ringOfIntegersQuadraticConj hmin hgen y) :
    ∃ ε : 𝓞 K, ε ≠ 0 ∧ x * ε = y * ringOfIntegersQuadraticConj hmin hgen ε := by
  set σ := ringOfIntegersQuadraticConj hmin hgen
  have hinv : ∀ z : 𝓞 K, σ (σ z) = z := ringOfIntegersQuadraticConj_involutive hmin hgen
  have hgenσ : σ θ = -θ := ringOfIntegersQuadraticConj_gen hmin hgen
  have hσx : σ x ≠ 0 := fun h0 => hx (by simpa [hinv] using congrArg σ h0)
  have hθ : (θ : 𝓞 K) ≠ 0 := fun h0 => coe_gen_ne_zero hmin (by rw [h0]; simp)
  by_cases hxy : x + y = 0
  · refine ⟨σ x * θ * x, by simp [hσx, hθ, hx], ?_⟩
    simp only [map_mul, hinv, hgenσ]
    linear_combination (θ * x * σ x) * hxy
  · refine ⟨σ x * (x + y), by simp [hσx, hxy], ?_⟩
    simp only [map_mul, map_add, hinv]
    linear_combination x * hnorm

end NumberField
