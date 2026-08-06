/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Diffeomorphism.Group

/-!
# Smooth conjugation in a Lie group

This file packages conjugation by an element of a Lie group as a smooth self-diffeomorphism. The
resulting map from the group to its group of smooth self-diffeomorphisms is a group homomorphism.
Differentiating each conjugation diffeomorphism at the identity yields the group adjoint action
developed in subsequent files.

## Main definitions

* `TauCeti.Lie.conjDiffeomorph`: conjugation by `g` as a smooth diffeomorphism.
* `TauCeti.Lie.conj`: the conjugation homomorphism into smooth self-diffeomorphisms.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 1, "The group adjoint".
-/

public section

namespace TauCeti.Lie

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {n : ℕ∞ω} [LieGroup I n G]

/-- Conjugation by `g`, sending `x` to `g * x * g⁻¹`, as a smooth self-diffeomorphism. -/
def conjDiffeomorph (g : G) : G ≃ₘ^n⟮I, I⟯ G where
  toEquiv := (MulAut.conj g).toEquiv
  contMDiff_toFun := (contMDiff_const.mul contMDiff_id).mul contMDiff_const.inv
  contMDiff_invFun := (contMDiff_const.mul contMDiff_id).mul contMDiff_const

@[simp]
theorem conjDiffeomorph_apply (g x : G) :
    conjDiffeomorph (I := I) (n := n) g x = g * x * g⁻¹ :=
  (rfl)

@[simp]
theorem conjDiffeomorph_symm_apply (g x : G) :
    (conjDiffeomorph (I := I) (n := n) g).symm x = g⁻¹ * x * g :=
  (rfl)

/-- Smooth conjugation is a group homomorphism from `G` to its group of smooth
self-diffeomorphisms. -/
def conj : G →* TauCeti.Diff I G n where
  toFun := conjDiffeomorph
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp only [TauCeti.Diffeomorph.mul_apply, conjDiffeomorph_apply]
    group

@[simp]
theorem conj_apply (g : G) :
    conj (I := I) (n := n) g = conjDiffeomorph (I := I) (n := n) g :=
  (rfl)

end TauCeti.Lie
