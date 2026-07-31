/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The exponential of a Banach algebra as a unit

The exponential of an element of a complete normed real algebra is invertible, with inverse the
exponential of its negation. This file packages that fact as a units-valued map
`TauCeti.expUnit : R → Rˣ` and records its one-parameter subgroup law along every real line
through the algebra.

This is the Banach-algebra model for the exponential map of a Lie group. The later abstract
construction should recover `expUnit` when specialized to the Lie group `Rˣ`.

## Main definitions

* `TauCeti.expUnit`: `NormedSpace.exp x`, regarded as a unit of the algebra.

## Main results

* `TauCeti.expUnit_coe`: coercing `expUnit x` back to the algebra gives `NormedSpace.exp x`.
* `TauCeti.expUnit_add_of_commute`: the exponential addition law as an equality of units.
* `TauCeti.expUnit_zero`, `TauCeti.expUnit_neg`: the identity and inverse laws.
* `TauCeti.exp_add_smul`: `t ↦ exp (t • x)` satisfies the one-parameter subgroup law.
* `TauCeti.expUnit_add_smul`: the same law as an equality in the group of units.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The matrix and circle shadows".
-/

public section

namespace TauCeti

open NormedSpace

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

private theorem isUnit_exp_real (x : R) : IsUnit (exp x) :=
  isUnit_exp_of_mem_ball (𝕂 := ℝ)
    ((expSeries_radius_eq_top ℝ R).symm ▸ edist_lt_top _ _)

/-- The exponential of an element of a complete normed real algebra, regarded as a unit.

Its inverse is represented by `NormedSpace.exp (-x)`, as witnessed by
`NormedSpace.isUnit_exp_of_mem_ball`. -/
noncomputable def expUnit (x : R) : Rˣ :=
  (isUnit_exp_real x).unit

/-- Coercing `expUnit x` to the algebra recovers `NormedSpace.exp x`. -/
@[simp]
theorem expUnit_coe (x : R) : (expUnit x : R) = exp x :=
  (isUnit_exp_real x).unit_spec

/-- The exponential addition law for commuting elements, lifted to the group of units. -/
theorem expUnit_add_of_commute {x y : R} (hxy : Commute x y) :
    expUnit (x + y) = expUnit x * expUnit y := by
  apply Units.ext
  simpa only [expUnit_coe, Units.val_mul] using
    exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hxy
      ((expSeries_radius_eq_top ℝ R).symm ▸ edist_lt_top _ _)
      ((expSeries_radius_eq_top ℝ R).symm ▸ edist_lt_top _ _)

/-- The exponential of zero is the identity unit. -/
@[simp]
theorem expUnit_zero : expUnit (0 : R) = 1 := by
  apply Units.ext
  simp

/-- The exponential of a negation is the inverse unit. -/
@[simp]
theorem expUnit_neg (x : R) : expUnit (-x) = (expUnit x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← expUnit_add_of_commute ((Commute.refl x).neg_left)]
  simp

/-- Along a fixed direction `x`, the Banach-algebra exponential is a one-parameter subgroup. -/
@[simp]
theorem exp_add_smul (x : R) (s t : ℝ) :
    exp ((s + t) • x) = exp (s • x) * exp (t • x) := by
  rw [add_smul]
  exact exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (((Commute.refl x).smul_left s).smul_right t)
    ((expSeries_radius_eq_top ℝ R).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ R).symm ▸ edist_lt_top _ _)

/-- The one-parameter subgroup law lifted from the algebra to its group of units. -/
@[simp]
theorem expUnit_add_smul (x : R) (s t : ℝ) :
    expUnit ((s + t) • x) = expUnit (s • x) * expUnit (t • x) := by
  rw [add_smul]
  exact expUnit_add_of_commute (((Commute.refl x).smul_left s).smul_right t)

end TauCeti
