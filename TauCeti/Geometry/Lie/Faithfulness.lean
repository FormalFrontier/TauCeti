/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Functor
import TauCeti.Topology.Algebra.Group.Preconnected
import TauCeti.Geometry.Lie.Exponential.LocalInverse

/-!
# Faithfulness of the Lie functor on preconnected groups

A smooth homomorphism out of a preconnected finite-dimensional real Lie group is determined by its
induced Lie-algebra homomorphism. Naturality of the Lie-group exponential first gives equality on
the exponential image. The local inverse to the exponential promotes this to equality near the
identity, and the equality locus is then an open and closed subgroup of the preconnected source.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 3, "Injectivity on connected groups".

## Main results

* `lieMap_injective`: a smooth homomorphism out of a preconnected Lie group is determined by its Lie
  map.
-/

public section

noncomputable section

open Filter
open scoped ContDiff Topology

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {G' : Type*} [TopologicalSpace G'] [ChartedSpace H' G'] [Group G']

/-- The Lie map is injective on smooth homomorphisms out of a preconnected Lie group. -/
@[grind inj]
theorem lieMap_injective
    [LieGroup I ∞ G] [LieGroup I' ∞ G'] [PreconnectedSpace G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] :
    Function.Injective
      (lieMap : ContMDiffMonoidMorphism I I' ∞ G G' →
        LeftInvariantDerivation I G →ₗ⁅ℝ⁆ LeftInvariantDerivation I' G') := by
  intro φ ψ h
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  have hnear : φ =ᶠ[𝓝 (1 : G)] ψ :=
    (eventually_lieExp_lieLog (I := I) (G := G)).mono fun g hg => by
      rw [← hg, map_lieExp, map_lieExp, h]
  apply DFunLike.coe_injective
  exact congrArg (fun f : G →* G' => (f : G → G'))
    (MonoidHom.eq_of_eventuallyEq_one hnear)
