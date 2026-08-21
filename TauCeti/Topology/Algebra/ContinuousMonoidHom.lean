/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The inclusion of a subgroup and the projection onto a quotient, as continuous homomorphisms

Mathlib's `Subgroup.subtype` and `QuotientGroup.mk'` are bare `MonoidHom`s, and its coercion
`ContinuousMonoidHom.toContinuousMonoidHom` applies only to bundled types that already carry a
`ContinuousMapClass` instance, so neither map is available as a `ContinuousMonoidHom`. This file
packages the two, for a topological group and the subspace and quotient topologies.
-/

public section

namespace TauCeti

namespace ContinuousMonoidHom

variable {G : Type*} [Group G] [TopologicalSpace G]

-- Both definitions below are exposed: downstream, `TopRep.res` objects taken along them have to
-- be definitionally the ones taken along the bare `Subgroup.subtype` and `QuotientGroup.mk'`.
/-- The inclusion of a subgroup, carrying the subspace topology, as a continuous homomorphism. -/
@[expose] def subgroupSubtype (S : Subgroup G) : S →ₜ* G where
  __ := S.subtype
  continuous_toFun := continuous_subtype_val

@[simp]
theorem coe_subgroupSubtype (S : Subgroup G) : (subgroupSubtype S : S →* G) = S.subtype :=
  (rfl)

/-- The projection onto the quotient by a normal subgroup, carrying the quotient topology, as a
continuous homomorphism. -/
@[expose] def quotientMk (N : Subgroup G) [N.Normal] : G →ₜ* G ⧸ N where
  __ := QuotientGroup.mk' N
  continuous_toFun := continuous_quot_mk

@[simp]
theorem coe_quotientMk (N : Subgroup G) [N.Normal] :
    (quotientMk N : G →* G ⧸ N) = QuotientGroup.mk' N :=
  (rfl)

end ContinuousMonoidHom

end TauCeti
