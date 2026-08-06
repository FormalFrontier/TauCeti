/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import TauCeti.Geometry.Diffeomorphism.Group

/-!
# Smooth conjugation in a Lie group

This file packages conjugation by an element of a Lie group as a smooth self-diffeomorphism.  The
resulting map from the group to its group of smooth self-diffeomorphisms is a group homomorphism.
Its differential at the identity is the group adjoint action developed in subsequent files.

## Main definitions

* `TauCeti.Lie.conjugationDiffeomorph`: conjugation by `g` as a smooth diffeomorphism.
* `TauCeti.Lie.conjugation`: the conjugation homomorphism into smooth self-diffeomorphisms.
-/

public section

namespace TauCeti.Lie

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

/-- Conjugation by `g`, sending `x` to `g * x * g⁻¹`, as a smooth self-diffeomorphism. -/
@[expose]
def conjugationDiffeomorph (g : G) : G ≃ₘ⟮I, I⟯ G where
  toEquiv := (MulAut.conj g).toEquiv
  contMDiff_toFun := (contMDiff_const.mul contMDiff_id).mul contMDiff_const.inv
  contMDiff_invFun := (contMDiff_const.mul contMDiff_id).mul contMDiff_const

@[simp]
theorem conjugationDiffeomorph_apply (g x : G) :
    conjugationDiffeomorph (I := I) g x = g * x * g⁻¹ :=
  rfl

@[simp]
theorem conjugationDiffeomorph_one (g : G) :
    conjugationDiffeomorph (I := I) g (1 : G) = 1 := by
  simp

@[simp]
theorem conjugationDiffeomorph_symm_apply (g x : G) :
    (conjugationDiffeomorph (I := I) g).symm x = g⁻¹ * x * g :=
  rfl

/-- Smooth conjugation is a group homomorphism from `G` to its group of smooth
self-diffeomorphisms. -/
@[expose]
def conjugation : G →* TauCeti.Diff I G ∞ where
  toFun := conjugationDiffeomorph
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp only [TauCeti.Diffeomorph.mul_apply, conjugationDiffeomorph_apply]
    group

@[simp]
theorem conjugation_apply (g : G) :
    conjugation (I := I) g = conjugationDiffeomorph (I := I) g :=
  rfl

end TauCeti.Lie
