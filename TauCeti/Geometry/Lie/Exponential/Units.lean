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
`TauCeti.expUnits : R → Rˣ` and records its one-parameter subgroup law along every real line
through the algebra.

This is the Banach-algebra model for the exponential map of a Lie group. The later abstract
construction should recover `expUnits` when specialized to the Lie group `Rˣ`.

## Main definitions

* `TauCeti.expUnits`: `NormedSpace.exp x`, regarded as a unit of the algebra.

## Main results

* `TauCeti.expUnits_coe`: coercing `expUnits x` back to the algebra gives `NormedSpace.exp x`.
* `TauCeti.exp_add_smul`: `t ↦ exp (t • x)` satisfies the one-parameter subgroup law.
* `TauCeti.expUnits_add_smul`: the same law as an equality in the group of units.

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
noncomputable def expUnits (x : R) : Rˣ :=
  (isUnit_exp_real x).unit

/-- Coercing `expUnits x` to the algebra recovers `NormedSpace.exp x`. -/
@[simp]
theorem expUnits_coe (x : R) : (expUnits x : R) = exp x :=
  (isUnit_exp_real x).unit_spec

/-- Along a fixed direction `x`, the Banach-algebra exponential is a one-parameter subgroup. -/
theorem exp_add_smul (x : R) (s t : ℝ) :
    exp ((s + t) • x) = exp (s • x) * exp (t • x) := by
  rw [add_smul]
  exact exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (((Commute.refl x).smul_left s).smul_right t)
    ((expSeries_radius_eq_top ℝ R).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ R).symm ▸ edist_lt_top _ _)

/-- The one-parameter subgroup law lifted from the algebra to its group of units. -/
theorem expUnits_add_smul (x : R) (s t : ℝ) :
    expUnits ((s + t) • x) = expUnits (s • x) * expUnits (t • x) := by
  apply Units.ext
  simpa only [expUnits_coe, Units.val_mul] using exp_add_smul x s t

end TauCeti
