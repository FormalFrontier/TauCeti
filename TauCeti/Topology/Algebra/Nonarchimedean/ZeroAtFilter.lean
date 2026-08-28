/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
public import TauCeti.Topology.Algebra.Nonarchimedean.OpenAddSubgroupBasis

/-!
# Cofinite convergence in a nonarchimedean group is a finiteness condition

In a nonarchimedean additive group the open subgroups form a basis of neighbourhoods of zero, so
a family converges to zero along the cofinite filter exactly when each open subgroup omits only
finitely many of its members.

The `→` direction is available in any topological additive group: an open subgroup is a
neighbourhood of zero, so cofinitely many members lie in it. It is nonarchimedeanness that gives
the converse, and with it the upgrade from a *consequence* of convergence to a *criterion* for it.

Nothing here looks at the index type, so it is arbitrary.

## Main results

* `NonarchimedeanAddGroup.zeroAtFilter_cofinite_iff_finite_notMem`
-/

public section

open Filter Topology

namespace NonarchimedeanAddGroup

variable {ι : Type*} {G : Type*} [AddGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]

/-- **Cofinite convergence, as a finiteness condition on open subgroups.** A family tends to `0`
along the cofinite filter exactly when, for every open additive subgroup `W`, all but finitely
many of its members lie in `W`.

Both directions are the single fact that the open subgroups are a basis of `𝓝 0`
(`NonarchimedeanAddGroup.nhds_zero_hasBasis_openAddSubgroup`), read through
`Filter.HasBasis.tendsto_right_iff`: convergence along a filter is membership of each basic
neighbourhood eventually, and `Filter.eventually_cofinite` turns "eventually along `cofinite`"
into the finiteness of the exceptional set. -/
theorem zeroAtFilter_cofinite_iff_finite_notMem {f : ι → G} :
    ZeroAtFilter cofinite f ↔ ∀ W : OpenAddSubgroup G, {n | f n ∉ (W : Set G)}.Finite := by
  simp only [ZeroAtFilter, (nhds_zero_hasBasis_openAddSubgroup G).tendsto_right_iff, true_implies,
    Filter.eventually_cofinite]

end NonarchimedeanAddGroup
