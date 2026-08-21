/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# A first-countable nonarchimedean group has a decreasing basis of open subgroups

Henkel's open mapping theorem runs a successive-approximation argument down a *sequence* of
neighbourhoods of zero, each one absorbing the previous error. Two properties of that sequence are
used and neither comes for free: its terms must be **subgroups**, so that a sum of errors drawn
from one term stays inside it, and it must be **decreasing**, so that the tail of the construction
stays inside the neighbourhood it started in.

Nonarchimedean gives the first, countable generation of `𝓝 0` the second, and this file combines
them. Neither hypothesis alone suffices — a
nonarchimedean group has open subgroups arbitrarily close to zero but possibly uncountably many
with no cofinal sequence among them, and a first-countable group has a decreasing countable basis
whose terms need not be subgroups.

## Main results

* `NonarchimedeanAddGroup.exists_antitone_basis_openAddSubgroup`: the neighbourhoods of zero
  admit an antitone basis consisting of open subgroups, indexed by `ℕ`.

## References

* L. Henkel, *An Open Mapping Theorem for rings which have a zero sequence of units*,
  [arXiv:1407.5647](https://arxiv.org/abs/1407.5647), whose approximation argument needs such a
  sequence.
-/

public section

open Filter Topology

namespace NonarchimedeanAddGroup

variable {G : Type*} [AddGroup G] [TopologicalSpace G]

/-- **A first-countable nonarchimedean additive group has an antitone basis of open subgroups at
zero.**

Both hypotheses are used, and only where stated: nonarchimedean makes the open subgroups a basis
of `𝓝 0` at all, and countable generation of `𝓝 0` is what extracts an antitone *sequence* from
that basis.

Countable generation of `𝓝 0` and `FirstCountableTopology G` are in fact equivalent under these
hypotheses, since `NonarchimedeanAddGroup` extends `IsTopologicalAddGroup`:
`TauCeti.SeparatelyContinuousAdd.toFirstCountableTopology` gives one direction and
`FirstCountableTopology.nhds_generated_countable` the other. The `𝓝 0` form is stated because it
is the one the proof consumes. -/
theorem exists_antitone_basis_openAddSubgroup [(𝓝 (0 : G)).IsCountablyGenerated]
    [NonarchimedeanAddGroup G] :
    ∃ V : ℕ → OpenAddSubgroup G, (𝓝 (0 : G)).HasAntitoneBasis fun n ↦ (V n : Set G) := by
  have hb : (𝓝 (0 : G)).HasBasis (fun _ : OpenAddSubgroup G ↦ True) fun V ↦ (V : Set G) := by
    refine Filter.hasBasis_iff.mpr fun S ↦ ⟨fun hS ↦ ?_, ?_⟩
    · obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean S hS
      exact ⟨V, trivial, hV⟩
    · rintro ⟨V, -, hV⟩
      exact Filter.mem_of_superset (V.isOpen.mem_nhds V.zero_mem) hV
  obtain ⟨V, -, hV⟩ := hb.exists_antitone_subbasis
  exact ⟨V, hV⟩

end NonarchimedeanAddGroup

end
