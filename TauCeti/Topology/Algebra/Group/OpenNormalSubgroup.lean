/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Constructions of open normal subgroups

Two bundled constructions of `OpenNormalSubgroup` that Mathlib provides for `OpenSubgroup`
but not for its normal variant: the preimage under a continuous group homomorphism, and the
trivial subgroup of a group with the discrete topology. Both are stated for an arbitrary
topological space structure on a group; no continuity of the group operations is required.

## Main definitions

* `OpenNormalSubgroup.comap`: the preimage of an open normal subgroup under a continuous
  group homomorphism.
* `TauCeti.openNormalSubgroupBot`: the trivial subgroup of a group with the discrete
  topology, as an open normal subgroup.
-/

public section

namespace OpenNormalSubgroup

variable {G H : Type*} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]

/-- The preimage of an open normal subgroup under a continuous group homomorphism. -/
def comap (U : OpenNormalSubgroup H) (f : G →* H) (hf : Continuous f) :
    OpenNormalSubgroup G where
  toOpenSubgroup := U.toOpenSubgroup.comap f hf
  isNormal' := U.isNormal'.comap f

/-- The underlying subgroup of the preimage of an open normal subgroup. -/
@[simp]
theorem toSubgroup_comap (U : OpenNormalSubgroup H) (f : G →* H)
    (hf : Continuous f) : (comap U f hf).toSubgroup = U.toSubgroup.comap f :=
  (rfl)

end OpenNormalSubgroup

namespace TauCeti

/-- The trivial subgroup of a group with the discrete topology, as an open normal subgroup. -/
def openNormalSubgroupBot (G : Type*) [Group G] [TopologicalSpace G] [DiscreteTopology G] :
    OpenNormalSubgroup G where
  toOpenSubgroup := ⟨⊥, isOpen_discrete _⟩
  isNormal' := inferInstance

/-- The underlying subgroup of `openNormalSubgroupBot` is `⊥`. -/
@[simp]
theorem openNormalSubgroupBot_toSubgroup (G : Type*) [Group G] [TopologicalSpace G]
    [DiscreteTopology G] : (openNormalSubgroupBot G).toSubgroup = ⊥ :=
  (rfl)

end TauCeti
