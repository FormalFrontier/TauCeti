/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# Smooth maps from product model spaces

Mathlib equips a product of model vector spaces both with the product of their self-models and
with the self-model of the product. This file provides the `C^n` bridge between those
definitionally distinct presentations.

This supplies reusable two-parameter calculus infrastructure for Deliverable A, Layer 1 of
`TauCetiRoadmap/RepresentationTheory/LieGroups/README.md`.

## Main result

* `contMDiff_prod_modelWithCornersSelf_iff`: a map from a product of model vector spaces is `C^n`
  for the product of the self-models if and only if it is `C^n` for the self-model of the product.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The infinitesimal adjoint".
-/

public section

open scoped Manifold

variable {𝕜 E₁ E₂ E' H' M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace M] [ChartedSpace H' M]
  {n : WithTop ℕ∞} {f : E₁ × E₂ → M}

/-- A map from a product of model vector spaces is `C^n` for the product of the self-models if and
only if it is `C^n` for the self-model of the product. -/
theorem contMDiff_prod_modelWithCornersSelf_iff :
    ContMDiff (𝓘(𝕜, E₁).prod 𝓘(𝕜, E₂)) I' n f ↔
      ContMDiff 𝓘(𝕜, E₁ × E₂) I' n f := by
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
