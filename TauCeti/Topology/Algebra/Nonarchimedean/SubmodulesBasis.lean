/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-!
# The neighbourhood basis of a submodules basis, and when two of them agree

Mathlib's `SubmodulesBasis B` turns a family `B : ι → Submodule R M` into a topology on `M`,
`SubmodulesBasis.topology`, by routing the family through
`SubmodulesBasis.toModuleFilterBasis`. That route leaves the neighbourhoods of `0` indexed by
*sets* `U` carrying a proof `∃ i, U = B i` rather than by `ι`. This file adds the `ι`-indexed
form, which Mathlib already has one level down for subgroups as
`RingSubgroupsBasis.hasBasis_nhds_zero`, and the comparison lemma it makes routine: two
submodule bases on the same module that are mutually cofinal induce the same topology.

Neither statement mentions anything beyond `SubmodulesBasis`, so both live in that namespace
rather than in a `TauCeti` one.

## Main results

* `SubmodulesBasis.hasBasis_nhds_zero`: the family is itself a neighbourhood basis at `0` for
  the topology it induces — a set is a neighbourhood of `0` exactly when it contains some
  `B i`.
* `SubmodulesBasis.topology_eq`: mutually cofinal submodule bases induce the same topology.

## References

* Mathlib's `Mathlib/Topology/Algebra/Nonarchimedean/Bases.lean`, whose
  `RingSubgroupsBasis.hasBasis_nhds_zero` the first result mirrors.
-/

public section

namespace SubmodulesBasis

variable {ι ι' R M : Type*} [CommRing R] [TopologicalSpace R] [AddCommGroup M] [Module R M]
  {B : ι → Submodule R M} {B' : ι' → Submodule R M}

/-- **The family is a neighbourhood basis at `0`**, indexed by `ι`: a set is a neighbourhood of
`0` for the induced topology exactly when it contains some `B i`.

Mathlib reaches the same filter only through `SubmodulesBasis.toModuleFilterBasis`, whose basis
is indexed by the sets `U` with `∃ i, U = B i`; this is the `ι`-indexed form, mirroring
`RingSubgroupsBasis.hasBasis_nhds_zero`. -/
theorem hasBasis_nhds_zero [Nonempty ι] (hB : SubmodulesBasis B) :
    (@nhds M hB.topology 0).HasBasis (fun _ : ι ↦ True) fun i ↦ (B i : Set M) :=
  hB.toModuleFilterBasis.toAddGroupFilterBasis.nhds_zero_hasBasis.to_hasBasis
    (by rintro _ ⟨i, rfl⟩; exact ⟨i, trivial, subset_rfl⟩)
    (fun i _ ↦ ⟨B i, ⟨i, rfl⟩, subset_rfl⟩)

/-- **Mutually cofinal submodule bases induce the same topology.** If every `B i` contains some
`B' j` and every `B' j` contains some `B i`, the two families are neighbourhood bases at `0` for
the same filter, and both topologies are additive group topologies, so they agree everywhere.

No relation between the two index types is needed, and neither family need be antitone: cofinality
in both directions is the whole hypothesis. -/
theorem topology_eq [Nonempty ι] [Nonempty ι'] (hB : SubmodulesBasis B) (hB' : SubmodulesBasis B')
    (h : ∀ i, ∃ j, B' j ≤ B i) (h' : ∀ j, ∃ i, B i ≤ B' j) : hB.topology = hB'.topology :=
  IsTopologicalAddGroup.ext inferInstance inferInstance <|
    hB.hasBasis_nhds_zero.ext hB'.hasBasis_nhds_zero
      (fun i _ ↦ (h i).imp fun _ hj ↦ ⟨trivial, SetLike.coe_subset_coe.mpr hj⟩)
      fun j _ ↦ (h' j).imp fun _ hi ↦ ⟨trivial, SetLike.coe_subset_coe.mpr hi⟩

end SubmodulesBasis
