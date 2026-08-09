/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Basic
public import TauCeti.Geometry.Lie.Interior
public import TauCeti.Geometry.Lie.Tangent.LieEquiv

/-!
# The adjoint action on left-invariant derivations

The tangent adjoint action is transported across the canonical Lie equivalence between the tangent
space at the identity and left-invariant derivations. The result is the roadmap-facing group adjoint
`Ad` on Mathlib's Lie algebra `LeftInvariantDerivation I G`.

The canonical derivation–tangent equivalence uses Hausdorffness to identify point derivations with
tangent vectors through global smooth functions. This imposes no extra public hypothesis on `Ad`
or its group laws: a charted space over the normed model is `T1`, and a `T1` topological group is
Hausdorff. No boundaryless manifold assumption is needed, because a Lie group's identity is
automatically an interior point.

This advances Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main definitions

* `TauCeti.Lie.Ad`: the group adjoint as an automorphism of left-invariant derivations.

## Main results

* `TauCeti.Lie.Ad_one`: the identity acts trivially.
* `TauCeti.Lie.Ad_mul`: the group adjoint respects multiplication.
* `TauCeti.Lie.Ad_inv`: inversion corresponds to the inverse automorphism.

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
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothnessThree

/-- The group adjoint on left-invariant derivations, obtained by transporting the differential of
conjugation across evaluation at the identity. -/
def Ad (g : G) : LeftInvariantDerivation I G ≃ₗ⁅ℝ⁆ LeftInvariantDerivation I G :=
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := I) (G := G) (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  (e.trans (tangentAd (I := I) g)).trans e.symm

/-- Applying the derivation adjoint is applying the tangent adjoint through the canonical Lie
equivalence. -/
theorem Ad_apply (g : G) (D : LeftInvariantDerivation I G) :
    Ad (I := I) g D =
      (leftInvariantDerivationLieEquivGroupLieAlgebra
          (I := I) (G := G)
          (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))).symm
        (tangentAd (I := I) g
          (leftInvariantDerivationLieEquivGroupLieAlgebra
            (I := I) (G := G)
            (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)) D)) :=
  (rfl)

/-- Evaluation at the identity intertwines the derivation and tangent adjoint actions. -/
@[simp high]
theorem leftInvariantDerivationLieEquivGroupLieAlgebra_Ad
    (g : G) (D : LeftInvariantDerivation I G) :
    leftInvariantDerivationLieEquivGroupLieAlgebra
        (I := I) (G := G)
        (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
        (Ad (I := I) g D) =
      tangentAd (I := I) g
        (leftInvariantDerivationLieEquivGroupLieAlgebra
          (I := I) (G := G)
          (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G)) D) := by
  rw [Ad_apply, LieEquiv.apply_symm_apply]

/-- The identity element acts trivially on left-invariant derivations. -/
@[simp]
theorem Ad_one : Ad (I := I) (1 : G) = LieEquiv.refl := by
  apply LieEquiv.ext
  intro D
  rw [Ad_apply, tangentAd_one, LieEquiv.refl_apply]
  exact (leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := I) (G := G)
    (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))).symm_apply_apply D

/-- A product acts by the composite of the two derivation adjoint automorphisms. -/
@[simp]
theorem Ad_mul (g h : G) :
    Ad (I := I) (g * h) = (Ad (I := I) h).trans (Ad (I := I) g) := by
  apply LieEquiv.ext
  intro D
  rw [Ad_apply, tangentAd_mul, LieEquiv.trans_apply, LieEquiv.trans_apply,
    Ad_apply, Ad_apply, LieEquiv.apply_symm_apply]

/-- The adjoint of an inverse is the inverse adjoint automorphism. -/
@[simp]
theorem Ad_inv (g : G) : Ad (I := I) g⁻¹ = (Ad (I := I) g).symm := by
  let e := leftInvariantDerivationLieEquivGroupLieAlgebra
    (I := I) (G := G) (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  -- Expose the transported action so `tangentAd_inv` rewrites its middle equivalence; the inverse
  -- of the resulting composite is then definitionally the composite on the right.
  change (e.trans (tangentAd (I := I) g⁻¹)).trans e.symm =
    ((e.trans (tangentAd (I := I) g)).trans e.symm).symm
  rw [tangentAd_inv]
  rfl

end TauCeti.Lie
