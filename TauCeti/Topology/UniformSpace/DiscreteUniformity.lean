/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.UniformSpace.DiscreteUniformity
public import Mathlib.Topology.Algebra.IsUniformGroup.Defs

/-!
# Discrete topological groups have the discrete uniformity

A complement to Mathlib's `DiscreteUniformity`: a uniform additive group whose topology is
discrete has the discrete uniformity, since its uniformity is the comap of the (discrete)
neighbourhood filter of zero.

## Main results

* `DiscreteUniformity.of_discreteTopology` : a uniform additive group with discrete topology
  has the discrete uniformity. Stated as a theorem, not an instance: together with Mathlib's
  `DiscreteUniformity → DiscreteTopology` instance it would form a resolution cycle. It lives
  in the root `DiscreteUniformity` namespace it extends, following this repository's
  convention for lemmas about external types.
-/

public section

namespace DiscreteUniformity

open Filter

/-- A uniform additive group whose topology is discrete has the discrete uniformity.

A theorem rather than an instance: Mathlib's `DiscreteUniformity → DiscreteTopology`
instance points the other way, and registering both directions would loop. -/
theorem of_discreteTopology {G : Type*} [AddGroup G] [UniformSpace G]
    [IsUniformAddGroup G] [DiscreteTopology G] : DiscreteUniformity G := by
  rw [discreteUniformity_iff_setRelId_mem_uniformity, uniformity_eq_comap_nhds_zero G]
  refine Filter.mem_comap.mpr ⟨{0}, (isOpen_discrete _).mem_nhds rfl, fun p hp ↦ ?_⟩
  simpa [SetRel.id, sub_eq_zero, eq_comm] using hp

end DiscreteUniformity
