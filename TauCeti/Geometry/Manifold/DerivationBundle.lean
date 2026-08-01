/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.DerivationBundle
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Tangent vectors as point derivations

A tangent vector acts on smooth scalar-valued functions by directional differentiation. This gives
a canonical linear map from the ordinary tangent space to the algebraic point derivations.

## Main results

* `tangentToPointDerivation`: the point derivation associated to a tangent vector.
* `tangentToPointDerivation_mfderiv`: this association commutes with differentials.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The Lie algebra and the tangent space at `1`".
-/

public section

open scoped ContDiff Derivation Manifold

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A tangent vector acts on smooth functions by directional differentiation.

This definition is exposed because the exported characteristic equation
`tangentToPointDerivation_apply` must unfold it under the module system. -/
@[expose]
def tangentToPointDerivation (x : M) : TangentSpace I x →ₗ[𝕜] PointDerivation I x where
  toFun v :=
    Derivation.mk'
      { toFun := fun f => mvfderiv I f x v
        map_add' := fun f g => by
          change mvfderiv I (⇑f + ⇑g) x v = _
          exact congr($(mvfderiv_add
            (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
            (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt) v)
        map_smul' := fun c f => by
          have hc : MDiffAt (fun _ : M => c) x := mdifferentiableAt_const
          change mvfderiv I ((fun _ : M => c) • ⇑f) x v = c • mvfderiv I f x v
          have h := congr($(mvfderiv_smul hc
            (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt) v)
          calc
            _ = (c • mvfderiv I f x +
                (mvfderiv I (fun _ : M => c) x).smulRight (f x)) v := h
            _ = _ := by simp [mvfderiv_const] }
      fun f g => by
        change mvfderiv I (⇑f * ⇑g) x v =
          f x * mvfderiv I g x v + g x * mvfderiv I f x v
        exact congr($(mvfderiv_mul
          (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
          (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt) v)
  map_add' v w := by
    ext f
    change mvfderiv I f x (v + w) = _
    exact (mvfderiv I f x).map_add v w
  map_smul' c v := by
    ext f
    change mvfderiv I f x (c • v) = _
    exact (mvfderiv I f x).map_smul c v

/-- The point derivation associated to a tangent vector evaluates a smooth function by its
directional derivative. -/
@[simp]
theorem tangentToPointDerivation_apply (x : M) (v : TangentSpace I x)
    (f : C^∞⟮I, M; 𝕜⟯) : tangentToPointDerivation x v f = mvfderiv I f x v :=
  rfl

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- Sending tangent vectors to point derivations commutes with the differential of a smooth map. -/
theorem tangentToPointDerivation_mfderiv (f : C^∞⟮I, M; I', M'⟯) (x : M)
    (v : TangentSpace I x) :
    tangentToPointDerivation (f x) (mfderiv I I' f x v) =
      𝒅 f x (tangentToPointDerivation x v) := by
  ext g
  change mvfderiv I' g (f x) (mfderiv I I' f x v) =
    tangentToPointDerivation x v (g.comp f)
  rw [tangentToPointDerivation_apply]
  exact (mfderiv_comp_apply x
    (g.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (f.contMDiff.mdifferentiable (by simp)).mdifferentiableAt v).symm
