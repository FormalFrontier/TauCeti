/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The dimension of an internal direct sum

A finite-dimensional vector space that is the internal direct sum of a finite family of subspaces
has the sum of their dimensions, `TauCeti.finrank_eq_sum_finrank_of_isInternal`.

Mathlib has `Module.finrank_directSum` for the *external* direct sum `⨁ i, M i` and
`DirectSum.IsInternal` for an internal decomposition, but not the dimension count that combining
them gives; the bridge is the canonical isomorphism
`LinearEquiv.ofBijective (DirectSum.coeLinearMap V)` an internal decomposition provides.
-/

public section

namespace TauCeti

open scoped DirectSum

/-- **The dimensions of the summands of an internal direct sum add up.** -/
theorem finrank_eq_sum_finrank_of_isInternal {K M ι : Type*} [DivisionRing K] [AddCommGroup M]
    [Module K M] [Module.Finite K M] [Fintype ι] [DecidableEq ι] {V : ι → Submodule K M}
    (h : DirectSum.IsInternal V) :
    Module.finrank K M = ∑ i, Module.finrank K (V i) := by
  rw [← (LinearEquiv.ofBijective (DirectSum.coeLinearMap V) h).finrank_eq,
    Module.finrank_directSum]

end TauCeti
