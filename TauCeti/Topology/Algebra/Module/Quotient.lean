/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Quotients of a discrete topological module

The quotient of a discrete topological module by a submodule is discrete: the quotient map is a
quotient map of topological spaces, so every subset of the quotient has open preimage and is
therefore open.

This is the `Submodule.Quotient` counterpart of Mathlib's `QuotientAddGroup.discreteTopology`,
which is stated for the quotient of a topological additive group by an *open* subgroup; in a
discrete module every submodule is open.
-/

public section

namespace TauCeti

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [ContinuousAdd M] [DiscreteTopology M]

/-- The quotient of a discrete topological module by a submodule is discrete. -/
instance Submodule.Quotient.discreteTopology (p : Submodule R M) : DiscreteTopology (M ⧸ p) :=
  discreteTopology_iff_forall_isOpen.2 fun _ ↦
    p.isOpenQuotientMap_mkQ.isQuotientMap.isOpen_preimage.mp (isOpen_discrete _)

end TauCeti
