/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
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
  {G : Type*} [topG : TopologicalSpace G] [chartsG : ChartedSpace H G] [Group G]
  {n : ℕ∞ω} [LieGroup I n G]

/-- The conjugation-action copy of a Lie group carries the original topology. -/
instance instTopologicalSpaceConjAct : TopologicalSpace (ConjAct G) := topG

/-- The conjugation-action copy of a Lie group carries the original manifold charts. -/
instance instChartedSpaceConjAct : ChartedSpace H (ConjAct G) := chartsG

/-- **Conjugation is jointly `C^n`.** The map `(g, x) ↦ g * x * g⁻¹` on a Lie group is `C^n` as a
map out of the product manifold; this is the manifold counterpart of
`IsTopologicalGroup.continuous_conj_prod`. -/
theorem contMDiff_conj_prod :
    ContMDiff (I.prod I) I n (fun p : G × G ↦ p.1 * p.2 * p.1⁻¹) :=
  (contMDiff_fst.mul contMDiff_snd).mul contMDiff_fst.inv

/-- Conjugation is a smooth action of the conjugation-action copy of a Lie group on the group. -/
instance instContMDiffSMulConjAct : ContMDiffSMul I I n (ConjAct G) G where
  contMDiff_smul := by
    -- The topology and charts above are definitionally those of `G`, while `ConjAct`'s scalar
    -- action is definitionally conjugation. Unfolding both exposes the standard smooth operations.
    change CMDiff n (fun p : G × G ↦ p.1 * p.2 * p.1⁻¹)
    exact contMDiff_conj_prod

/-- Conjugation by `g`, sending `x` to `g * x * g⁻¹`, as a smooth self-diffeomorphism. -/
def conjDiffeomorph (g : G) : G ≃ₘ^n⟮I, I⟯ G :=
  Diffeomorph.smul I I n (ConjAct.toConjAct g)

@[simp]
theorem conjDiffeomorph_apply (g x : G) :
    conjDiffeomorph (I := I) (n := n) g x = g * x * g⁻¹ :=
  ConjAct.toConjAct_smul g x

@[simp]
theorem conjDiffeomorph_symm_apply (g x : G) :
    (conjDiffeomorph (I := I) (n := n) g).symm x = g⁻¹ * x * g :=
  ConjAct.toConjAct_inv_smul g x

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
