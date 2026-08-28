/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Compactness.Compact

/-!
# Compact topological groups

Generic facts about compact topological groups, phrased for the unbundled classes
`[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]`; no total
disconnectedness hypothesis is involved, so the results apply in particular to profinite
groups.

## Main results

* `Subgroup.isOpen_iff_isClosed_and_finiteIndex`: in a compact group a subgroup is open
  exactly when it is closed of finite index.
-/

public section

namespace TauCeti

/-- In a compact group, a subgroup is open exactly when it is closed of finite index. -/
theorem _root_.Subgroup.isOpen_iff_isClosed_and_finiteIndex {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] (H : Subgroup G) :
    IsOpen (H : Set G) ↔ IsClosed (H : Set G) ∧ H.FiniteIndex := by
  constructor
  · intro hH
    have hHclosed : IsClosed (H : Set G) := Subgroup.isClosed_of_isOpen _ hH
    have hHdisc : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology hH
    have hHfin : Finite (G ⧸ H) := finite_of_compact_of_discrete
    exact ⟨hHclosed, @Subgroup.finiteIndex_of_finite_quotient _ _ _ hHfin⟩
  · rintro ⟨hHclosed, hHfi⟩
    exact @Subgroup.isOpen_of_isClosed_of_finiteIndex _ _ _ _ _ hHfi hHclosed

end TauCeti
