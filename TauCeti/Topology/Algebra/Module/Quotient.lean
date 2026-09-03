/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Quotients of a discrete topological module

The quotient of a discrete topological module by a submodule is discrete, since in a discrete
module every submodule is open.

Mathlib's `QuotientAddGroup.discreteTopology` is the statement for the quotient of a topological
additive group by an *open* subgroup, and supplies the whole proof; because it is a theorem
rather than an instance (Mathlib notes that `IsOpen` would have to be a class for that), instance
search cannot use it, so this file records the discrete case for `M ⧸ p` as an instance. This is
the same bridge from `QuotientAddGroup` to `Submodule.Quotient` that Mathlib's own
`Submodule.topologicalAddGroup_quotient` and `Submodule.t3_quotient_of_isClosed` provide.
-/

public section

namespace Submodule.Quotient

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [ContinuousAdd M] [DiscreteTopology M]

/-- The quotient of a discrete topological module by a submodule is discrete. -/
instance discreteTopology (p : Submodule R M) : DiscreteTopology (M ⧸ p) :=
  QuotientAddGroup.discreteTopology (N := p.toAddSubgroup) (isOpen_discrete _)

end Submodule.Quotient
