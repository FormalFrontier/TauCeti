/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# The open subgroups of a nonarchimedean group are a basis of the neighbourhoods of zero

`NonarchimedeanAddGroup` is stated as an existence property — every neighbourhood of zero contains
an open subgroup — and the filter-basis form is what consumers actually use. This module records
that form once.

It is deliberately separate from
`TauCeti/Topology/Algebra/Nonarchimedean/FirstCountable.lean`, where this statement previously
lived as a `have` inside `NonarchimedeanAddGroup.exists_antitone_basis_openAddSubgroup`: that
theorem additionally assumes `(𝓝 0).IsCountablyGenerated`, which it needs only to extract an
antitone *sequence* from the basis. The basis itself needs no countability, so hiding it inside a
first-countability result put a countability hypothesis on a statement that does not use one.

## Main results

* `NonarchimedeanAddGroup.nhds_zero_hasBasis_openAddSubgroup`
-/

public section

open Filter Topology

namespace NonarchimedeanAddGroup

variable (G : Type*) [AddGroup G] [TopologicalSpace G] [NonarchimedeanAddGroup G]

/-- **The open additive subgroups form a basis of `𝓝 0`.** One direction is the defining property
of `NonarchimedeanAddGroup`; the other is that an open subgroup is a neighbourhood of zero, since
it is open and contains zero. -/
theorem nhds_zero_hasBasis_openAddSubgroup :
    (𝓝 (0 : G)).HasBasis (fun _ : OpenAddSubgroup G ↦ True) fun V ↦ (V : Set G) := by
  refine Filter.hasBasis_iff.mpr fun S ↦ ⟨fun hS ↦ ?_, ?_⟩
  · obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean S hS
    exact ⟨V, trivial, hV⟩
  · rintro ⟨V, -, hV⟩
    exact Filter.mem_of_superset (V.isOpen.mem_nhds V.zero_mem) hV

end NonarchimedeanAddGroup
