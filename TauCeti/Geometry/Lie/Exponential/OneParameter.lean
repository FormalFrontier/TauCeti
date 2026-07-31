/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import TauCeti.Geometry.Lie.Exponential.Units

/-!
# One-parameter subgroups from the Banach algebra exponential

For an element `x` of a complete normed real algebra, `TauCeti.expUnitHom` bundles
`t ↦ expUnit (t • x)` as a continuous one-parameter subgroup. This file proves that its
underlying curve is smooth.

This is the concrete Banach-algebra model for the one-parameter subgroups associated to a future
abstract Lie-group exponential map.

## Main results

* `TauCeti.contDiff_exp_smul`: the algebra-valued exponential curve is smooth.
* `TauCeti.contMDiff_expUnit_smul`: the corresponding units-valued curve is smooth.
* `TauCeti.contMDiff_expUnitHom`: the bundled subgroup's underlying curve is smooth.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "One-parameter subgroups" and "The matrix and circle shadows".
-/

public section

namespace TauCeti

open scoped ContDiff Manifold

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

attribute [local instance] normedAlgebraRatOfReal

/-- The algebra-valued exponential curve `t ↦ exp (t • x)` is smooth. -/
theorem contDiff_exp_smul (x : R) :
    ContDiff ℝ ∞ (fun t : ℝ => NormedSpace.exp (t • x)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have h : AnalyticAt ℝ (fun s : ℝ => s • x) t := by fun_prop
  change ContDiffAt ℝ ∞ (NormedSpace.exp ∘ fun s : ℝ => s • x) t
  exact (AnalyticAt.comp (f := fun s : ℝ => s • x)
    (NormedSpace.exp_analytic (𝕂 := ℝ) (t • x)) h).contDiffAt

/-- The units-valued exponential curve `t ↦ expUnit (t • x)` is smooth. -/
theorem contMDiff_expUnit_smul (x : R) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, R) ∞ (fun t : ℝ => expUnit (t • x)) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  rw [show Units.val ∘ (fun t : ℝ => expUnit (t • x)) =
      fun t : ℝ => NormedSpace.exp (t • x) by
    funext t
    exact expUnit_coe (t • x)]
  exact (contDiff_exp_smul x).contMDiff

/-- The curve underlying `expUnitHom x` is smooth. -/
theorem contMDiff_expUnitHom (x : R) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, R) ∞
      (fun t : ℝ => expUnitHom x (Multiplicative.ofAdd t)) := by
  simpa only [expUnitHom_apply] using contMDiff_expUnit_smul x

end TauCeti
