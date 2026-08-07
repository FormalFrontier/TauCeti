/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.Tangent.LieEquiv

/-!
# The adjoint action on left-invariant derivations

The tangent adjoint action is transported across the canonical Lie equivalence between the tangent
space at the identity and left-invariant derivations. The result is the roadmap-facing group adjoint
`Ad` on Mathlib's Lie algebra `LeftInvariantDerivation I G`.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main definitions

* `TauCeti.Lie.Ad`: the group adjoint as an automorphism of left-invariant derivations.

## Main results

* `TauCeti.Lie.Ad_mul`: the group adjoint respects multiplication.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The group adjoint".
-/

public section

noncomputable section

namespace TauCeti.Lie

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothnessThree

/-- The group adjoint on left-invariant derivations, obtained by transporting the differential of
conjugation across evaluation at the identity. -/
def Ad (g : G) : LeftInvariantDerivation I G ≃ₗ⁅ℝ⁆ LeftInvariantDerivation I G :=
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint
  (e.trans (tangentAd (I := I) g)).trans e.symm

@[simp]
theorem Ad_apply (g : G) (D : LeftInvariantDerivation I G) :
    Ad (I := I) g D =
      (leftInvariantDerivationLieEquivGroupLieAlgebra
          (I := I) (G := G) BoundarylessManifold.isInteriorPoint).symm
        (tangentAd (I := I) g
          (leftInvariantDerivationLieEquivGroupLieAlgebra
            (I := I) (G := G) BoundarylessManifold.isInteriorPoint D)) :=
  (rfl)

@[simp]
theorem Ad_one : Ad (I := I) (1 : G) = LieEquiv.refl := by
  apply LieEquiv.ext
  intro D
  rw [Ad_apply, tangentAd_one, LieEquiv.refl_apply]
  exact (leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := I) (G := G) BoundarylessManifold.isInteriorPoint).symm_apply_apply D

theorem Ad_mul (g h : G) :
    Ad (I := I) (g * h) = (Ad (I := I) h).trans (Ad (I := I) g) := by
  apply LieEquiv.ext
  intro D
  rw [Ad_apply, tangentAd_mul, LieEquiv.trans_apply, LieEquiv.trans_apply,
    Ad_apply, Ad_apply, LieEquiv.apply_symm_apply]

@[simp]
theorem Ad_inv (g : G) : Ad (I := I) g⁻¹ = (Ad (I := I) g).symm := by
  apply LieEquiv.ext
  intro D
  apply (Ad (I := I) g).injective
  change Ad (I := I) g (Ad (I := I) g⁻¹ D) =
    Ad (I := I) g ((Ad (I := I) g).symm D)
  rw [LieEquiv.apply_symm_apply]
  have h := congrArg
    (fun e : LeftInvariantDerivation I G ≃ₗ⁅ℝ⁆ LeftInvariantDerivation I G ↦ e D)
    (Ad_mul (I := I) g g⁻¹)
  simpa only [mul_inv_cancel, Ad_one, LieEquiv.refl_apply, LieEquiv.trans_apply] using h.symm

end TauCeti.Lie
