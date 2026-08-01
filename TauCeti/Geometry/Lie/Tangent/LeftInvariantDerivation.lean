/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LeftInvariantDerivation

/-!
# Evaluation of left-invariant derivations

A left-invariant derivation on a Lie group is determined by its value at any point. In particular,
evaluation at the identity is injective. This is the injective half of the identification between
the Lie algebra of left-invariant derivations and the tangent Lie algebra at the identity.

## Main results

* `LeftInvariantDerivation.evalAt_injective`: evaluation at any point is injective.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The Lie algebra and the tangent space at `1`".
-/

public section

open scoped ContDiff Manifold

namespace LeftInvariantDerivation

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

/-- A left-invariant derivation is determined by its value at any point. -/
theorem evalAt_injective (g₀ : G) :
    Function.Injective (evalAt (I := I) g₀) := by
  intro X Y hXY
  have hOne : evalAt (I := I) (1 : G) X = evalAt (I := I) (1 : G) Y := by
    have hInv : evalAt (I := I) (g₀⁻¹ * g₀) X = evalAt (I := I) (g₀⁻¹ * g₀) Y := by
      rw [evalAt_mul, evalAt_mul, hXY]
    rw [inv_mul_cancel] at hInv
    exact hInv
  ext f g
  have hEval : evalAt (I := I) g X = evalAt (I := I) g Y := by
    calc
      evalAt (I := I) g X =
          𝒅ₕ (smoothLeftMul_one I g) (evalAt (I := I) (1 : G) X) :=
        (left_invariant (I := I) (g := g) (X := X)).symm
      _ = 𝒅ₕ (smoothLeftMul_one I g) (evalAt (I := I) (1 : G) Y) :=
        congrArg (𝒅ₕ (smoothLeftMul_one I g)) hOne
      _ = evalAt (I := I) g Y := left_invariant (I := I) (g := g) (X := Y)
  exact congrArg (fun D => D f) hEval

end LeftInvariantDerivation
