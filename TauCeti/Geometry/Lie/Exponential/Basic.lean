/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.IntegralCurve
public import TauCeti.Geometry.Lie.Tangent.LeftInvariantDerivation

/-!
# The exponential map of a Lie group

This file defines the tangent-space exponential of a real Lie group modeled on a complete normed
space by evaluating the canonical invariant one-parameter subgroup at time one. For a
finite-dimensional smooth Lie group, it transports this construction across the canonical
equivalence between left-invariant derivations and tangent vectors at the identity to obtain the
roadmap-facing Lie-group exponential.

## Main results

* `mulInvariantExp`: the time-one value of the invariant curve attached to a tangent vector.
* `mulInvariantExp_smul`: scaling a tangent vector is evaluation at the corresponding time.
* `mulInvariantOneParameterSubgroup_eq_mulInvariantExp_smul`: the bundled subgroup is the
  exponential along a line.
* `mulInvariantExp_add_smul`: the exponential along a fixed line is a one-parameter subgroup.
* `mulInvariantExp_zero`, `mulInvariantExp_neg`: the identity and inverse laws.
* `lieExp`: the exponential map on Mathlib's Lie algebra of left-invariant derivations.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The exponential map".
-/

public section

open Function Manifold VectorField
open scoped ContDiff Manifold

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]

/-- The tangent-space exponential obtained by evaluating the canonical invariant curve at time
one. This is the tangent-vector precursor of the roadmap's derivation-based `lieExp`. -/
noncomputable def mulInvariantExp [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) : G :=
  mulInvariantOneParameterSubgroup v (Multiplicative.ofAdd 1)

/-- The tangent-space exponential is the canonical invariant integral curve evaluated at time
one. -/
theorem mulInvariantExp_eq_mulInvariantIntegralCurve [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) :
    mulInvariantExp v = mulInvariantIntegralCurve v 1 1 := by
  rw [mulInvariantExp, mulInvariantOneParameterSubgroup_apply]

/-- Scaling a tangent vector corresponds to evaluating its invariant integral curve at the scale
factor. -/
theorem mulInvariantExp_smul [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (t : ℝ) :
    mulInvariantExp (t • v) = mulInvariantIntegralCurve v 1 t := by
  rw [mulInvariantExp_eq_mulInvariantIntegralCurve, mulInvariantIntegralCurve_smul, one_mul]

/-- The canonical one-parameter subgroup is the tangent-space exponential along its generating
line. -/
theorem mulInvariantOneParameterSubgroup_eq_mulInvariantExp_smul [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (t : ℝ) :
    mulInvariantOneParameterSubgroup v (Multiplicative.ofAdd t) = mulInvariantExp (t • v) := by
  rw [mulInvariantOneParameterSubgroup_apply, mulInvariantExp_smul]

/-- The exponential along a line satisfies the one-parameter subgroup law. -/
@[simp]
theorem mulInvariantExp_add_smul [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) (s t : ℝ) :
    mulInvariantExp ((s + t) • v) = mulInvariantExp (s • v) * mulInvariantExp (t • v) := by
  rw [mulInvariantExp_smul, mulInvariantExp_smul, mulInvariantExp_smul,
    mulInvariantIntegralCurve_add]

/-- The tangent-space exponential sends zero to the group identity. -/
@[simp]
theorem mulInvariantExp_zero [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] : mulInvariantExp (0 : GroupLieAlgebra I G) = 1 := by
  simpa using mulInvariantExp_smul (0 : GroupLieAlgebra I G) 0

/-- The tangent-space exponential sends negation to inversion. -/
@[simp]
theorem mulInvariantExp_neg [CompleteSpace E]
    [LieGroup I (minSmoothness ℝ 3) G] [IsManifold I 1 G] [T2Space G]
    [BoundarylessManifold I G] (v : GroupLieAlgebra I G) :
    mulInvariantExp (-v) = (mulInvariantExp v)⁻¹ := by
  calc
    mulInvariantExp (-v) =
        mulInvariantOneParameterSubgroup v (Multiplicative.ofAdd (-1)) := by
      rw [mulInvariantOneParameterSubgroup_eq_mulInvariantExp_smul]
      simp
    _ = mulInvariantOneParameterSubgroup v (Multiplicative.ofAdd 1)⁻¹ := by simp
    _ = (mulInvariantOneParameterSubgroup v (Multiplicative.ofAdd 1))⁻¹ := by
      rw [map_inv]
    _ = (mulInvariantExp v)⁻¹ := by
      rw [mulInvariantOneParameterSubgroup_eq_mulInvariantExp_smul, one_smul]

section LieAlgebra

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G] [IsManifold I 1 G] [T2Space G]
  [BoundarylessManifold I G]

local instance lieGroupMinSmoothness : LieGroup I (minSmoothness ℝ 3) G := by
  simpa using (inferInstance : LieGroup I (3 : ℕ∞ω) G)

/-- The exponential map of a finite-dimensional smooth real Lie group, obtained by evaluating at
time one the invariant integral curve whose tangent vector corresponds to a left-invariant
derivation. -/
noncomputable def lieExp (X : LeftInvariantDerivation I G) : G :=
  mulInvariantExp
    (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
      BoundarylessManifold.isInteriorPoint X)

/-- The derivation-based exponential is the tangent-space exponential transported through the
canonical equivalence at the identity. -/
theorem lieExp_eq_mulInvariantExp (X : LeftInvariantDerivation I G) :
    lieExp X =
      mulInvariantExp
        (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint X) :=
  by rw [lieExp]

end LieAlgebra
