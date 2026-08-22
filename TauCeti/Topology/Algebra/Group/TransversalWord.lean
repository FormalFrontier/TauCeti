/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.GroupTheory.TransversalWord

/-!
# Continuity of the transversal word

For a subgroup `U` of a group `G` and a map `t : G ⧸ U → G`, the transversal word
`ℓᵗ_u(γ) = (t u)⁻¹ * γ * t (γ⁻¹ • u)` of `TauCeti.lWord` is a purely group-theoretic construction.
This file adds the one statement about it that needs a topology: if `G` is a topological group and
`U` is *open*, then `γ ↦ ℓᵗ_u(γ)` is continuous (`TauCeti.continuous_lWord`). Of the three factors,
`(t u)⁻¹` is constant and `γ ↦ γ` is the continuous identity; the only one whose continuity is not
immediate is `γ ↦ t (γ⁻¹ • u)`, and openness of `U` makes `G ⧸ U` discrete, so that factor is
locally constant and no continuity is required of `t` itself.

This is the continuity clause of the transversal calculus of the Layer 6 milestone of the
human-authored roadmap at `TauCetiRoadmap/ProfiniteCohomology/README.md`. It lives here, rather
than with the calculus in `TauCeti/GroupTheory/TransversalWord.lean`, so that the group theory does
not depend on the topological-group hierarchy.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousMul G] [ContinuousInv G]
  (U : Subgroup G) (t : G ⧸ U → G)

/-- For an *open* subgroup `U` the transversal word `γ ↦ ℓᵗ_u(γ)` is continuous, for any map `t`
at all: the quotient `G ⧸ U` is discrete, so `γ ↦ t (γ⁻¹ • u)` is locally constant. -/
theorem continuous_lWord (hU : IsOpen (U : Set G)) (u : G ⧸ U) : Continuous (lWord U t u) := by
  have : DiscreteTopology (G ⧸ U) := QuotientGroup.discreteTopology hU
  have h : lWord U t u = fun γ : G => (t u)⁻¹ * γ * t (γ⁻¹ • u) := funext (lWord_def U t u)
  rw [h]
  exact (continuous_const.mul continuous_id).mul
    (continuous_of_discreteTopology.comp (continuous_inv.smul continuous_const))

end TauCeti
