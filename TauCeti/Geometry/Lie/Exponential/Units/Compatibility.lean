/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Exponential.Basic
public import TauCeti.Geometry.Lie.Exponential.OneParameter

/-!
# Compatibility of the abstract and Banach-algebra exponentials

The abstract Lie-group exponential recovers the Banach-algebra exponential on the Lie group `Rˣ`.
Under the canonical identification of its tangent Lie algebra with `R`, the generated abstract
one-parameter subgroup is `TauCeti.expUnitHom`, and its time-one value is `TauCeti.expUnit`.

## Main results

* `hasDerivAt_mulInvariantOneParameterSubgroup_val_zero`: the abstract invariant subgroup has the
  expected velocity in the units chart.
* `mulInvariantOneParameterSubgroup_eq_expUnitHom`: the tangent-space construction and the
  Banach-algebra subgroup coincide without a finite-dimensionality assumption.
* `oneParameterSubgroup_eq_expUnitHom`: the abstract and Banach-algebra subgroups coincide.
* `lieExp_eq_expUnit`: the abstract and Banach-algebra exponentials coincide.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The matrix and circle shadows".
-/

public section

open Manifold
open scoped ContDiff Manifold

noncomputable section

section Complete

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-- The preferred chart of the units manifold at one is the inclusion into the ambient algebra. -/
theorem extChartAt_units_one_apply (u : Rˣ) :
    extChartAt 𝓘(ℝ, R) (1 : Rˣ) u = (u : R) := by
  simp only [extChartAt_coe, Function.comp_apply, Units.chartAt_apply,
    modelWithCornersSelf_coe, id]

/-- The canonical invariant one-parameter subgroup on `Rˣ` with tangent vector `x` has initial
velocity `x` after embedding the units in `R`. -/
theorem hasDerivAt_mulInvariantOneParameterSubgroup_val_zero (x : R) :
    HasDerivAt
      (fun t : ℝ =>
        (mulInvariantOneParameterSubgroup
          (I := 𝓘(ℝ, R)) (G := Rˣ) (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ)
          (Multiplicative.ofAdd t) : R)) x 0 := by
  let v : GroupLieAlgebra 𝓘(ℝ, R) Rˣ := x
  have hfun :
      (fun t : ℝ =>
        (mulInvariantOneParameterSubgroup v (Multiplicative.ofAdd t) : R)) =
        fun t : ℝ =>
          (mulInvariantIntegralCurve (I := 𝓘(ℝ, R)) (G := Rˣ) v (1 : Rˣ) t : R) := by
    funext t
    exact congrArg Units.val
      (mulInvariantOneParameterSubgroup_apply (I := 𝓘(ℝ, R)) (G := Rˣ) v t)
  have h := (isMIntegralCurve_mulInvariantIntegralCurve (I := 𝓘(ℝ, R)) (G := Rˣ)
    v (1 : Rˣ)).isMIntegralCurveAt 0
  have hd := h.eventually_hasDerivAt.self_of_nhds
  have hzero : mulInvariantIntegralCurve (I := 𝓘(ℝ, R)) (G := Rˣ) v 1 0 = 1 :=
    mulInvariantIntegralCurve_zero v 1
  rw [hzero] at hd
  have hone : (1 : Rˣ) ∈ (extChartAt 𝓘(ℝ, R) (1 : Rˣ)).source :=
    mem_of_mem_nhds (extChartAt_source_mem_nhds (I := 𝓘(ℝ, R)) (1 : Rˣ))
  rw [mulInvariantVectorField_one] at hd
  dsimp only [v] at hd
  rw [tangentCoordChange_self hone] at hd
  have hchart :
      (extChartAt 𝓘(ℝ, R) (1 : Rˣ)) ∘
          mulInvariantIntegralCurve (I := 𝓘(ℝ, R)) (G := Rˣ) v 1 =
        fun t => (mulInvariantIntegralCurve
          (I := 𝓘(ℝ, R)) (G := Rˣ) v 1 t : R) := by
    funext t
    exact extChartAt_units_one_apply _
  rw [hchart] at hd
  rw [hfun]
  exact hd

/-- Under the canonical identification of the tangent Lie algebra of `Rˣ` with `R`, the canonical
invariant one-parameter subgroup is the Banach-algebra exponential subgroup. -/
@[simp]
theorem mulInvariantOneParameterSubgroup_eq_expUnitHom (x : R) :
    mulInvariantOneParameterSubgroup
      (I := 𝓘(ℝ, R)) (G := Rˣ) (x : GroupLieAlgebra 𝓘(ℝ, R) Rˣ) =
      TauCeti.expUnitHom x := by
  apply TauCeti.continuousMonoidHom_eq_expUnitHom_of_hasDerivAt _ x
  exact hasDerivAt_mulInvariantOneParameterSubgroup_val_zero x

end Complete

section FiniteDimensional

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [FiniteDimensional ℝ R]

noncomputable local instance finiteDimensionalCompleteSpace : CompleteSpace R :=
  FiniteDimensional.complete ℝ R

attribute [local instance] TauCeti.normedAlgebraRatOfReal

/-- The canonical identification of the Lie algebra of `Rˣ` with the ambient real algebra. -/
@[expose]
noncomputable def unitsLieAlgebraEquiv :
    LeftInvariantDerivation 𝓘(ℝ, R) Rˣ ≃ₗ[ℝ] R :=
  leftInvariantDerivationEquivGroupLieAlgebra (I := 𝓘(ℝ, R)) (G := Rˣ)
    BoundarylessManifold.isInteriorPoint

/-- The canonical identification with the ambient algebra is evaluation at the identity, followed
by the standard identification of the tangent space of `Rˣ` with `R`. -/
@[simp]
theorem unitsLieAlgebraEquiv_apply (X : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :
    unitsLieAlgebraEquiv X =
      leftInvariantDerivationEquivGroupLieAlgebra (I := 𝓘(ℝ, R)) (G := Rˣ)
        BoundarylessManifold.isInteriorPoint X :=
  rfl

/-- The abstract one-parameter subgroup of a derivation on `Rˣ` is the Banach-algebra exponential
subgroup generated by its tangent vector at the identity. -/
@[simp]
theorem oneParameterSubgroup_eq_expUnitHom (X : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :
    oneParameterSubgroup X =
      TauCeti.expUnitHom (R := R) (unitsLieAlgebraEquiv X) := by
  rw [oneParameterSubgroup_eq_mulInvariantOneParameterSubgroup]
  exact mulInvariantOneParameterSubgroup_eq_expUnitHom (unitsLieAlgebraEquiv X)

/-- The abstract Lie-group exponential of a derivation on `Rˣ` is the Banach-algebra exponential
of its tangent vector at the identity, packaged as a unit. -/
@[simp]
theorem lieExp_eq_expUnit (X : LeftInvariantDerivation 𝓘(ℝ, R) Rˣ) :
    lieExp X = TauCeti.expUnit (R := R) (unitsLieAlgebraEquiv X) := by
  have h := congrArg (fun φ : ContinuousMonoidHom (Multiplicative ℝ) Rˣ =>
    φ (Multiplicative.ofAdd 1)) (oneParameterSubgroup_eq_expUnitHom X)
  simpa only [oneParameterSubgroup_apply, one_smul, TauCeti.expUnitHom_apply] using h

end FiniteDimensional
