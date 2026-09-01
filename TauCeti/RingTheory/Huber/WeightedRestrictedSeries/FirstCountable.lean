/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.RingTheory.Huber.WeightedRestrictedSeries.Basic
public import TauCeti.Topology.Algebra.Group.FirstCountable
public import TauCeti.Topology.Algebra.Nonarchimedean.FirstCountable

/-!
# First countability of the weighted restricted series ring

`TauCeti.Huber.weightedRestrictedSubring` carries the topology whose neighbourhoods of zero are
the `U⟨X⟩` for `U` an open additive subgroup of the coefficient ring `A`
(`TauCeti.Huber.hasBasis_nhds_zero_weightedTopology`). That basis is indexed by *all* of
`OpenAddSubgroup A`, so it is not countable as it stands; what makes `𝓝 0` countably generated is
that a countable *cofinal* subfamily suffices, and a nonarchimedean `A` whose own `𝓝 0` is
countably generated supplies one.

This matters because `FirstCountableTopology` is the class Mathlib's own instances are keyed on —
notably the completeness of a quotient by a subgroup (Bourbaki IX.3.1 Proposition 4), which the
theory of rational localisations consumes. With the instance below in scope,
`FirstCountableTopology (weightedRestrictedSubring T hT)` is found by typeclass resolution alone,
through `TauCeti.SeparatelyContinuousAdd.toFirstCountableTopology`; no separate declaration is
needed and none is given.

The hypothesis `[(𝓝 (0 : A)).IsCountablyGenerated]` is not restrictive in the intended
application: a Huber ring satisfies it, by
`TauCeti.Huber.IsHuberRing.isCountablyGenerated_nhds_zero`.

## Main results

* `TauCeti.Huber.isCountablyGenerated_nhds_zero_weightedRestrictedSubring`.
-/

public section

open scoped Topology

namespace TauCeti.Huber

variable {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- **Countable generation of `𝓝 0` passes to `A⟨X⟩_T`.** The `U⟨X⟩` for `U` ranging over a
countable antitone basis of `𝓝 (0 : A)` by open additive subgroups are cofinal among the
`U⟨X⟩` for arbitrary `U`, since `TauCeti.Huber.weightedNhd` is monotone. -/
instance isCountablyGenerated_nhds_zero_weightedRestrictedSubring
    [(𝓝 (0 : A)).IsCountablyGenerated] {T : Fin k → Set A} {hT : IsWeightFamily T} :
    (𝓝 (0 : weightedRestrictedSubring T hT)).IsCountablyGenerated := by
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.exists_antitone_basis_openAddSubgroup (G := A)
  refine Filter.HasBasis.isCountablyGenerated (ι := ℕ)
    ((hasBasis_nhds_zero_weightedTopology hT).to_hasBasis
      (p' := fun _ : ℕ ↦ True)
      (s' := fun n ↦ (weightedNhd T hT (V n).toAddSubgroup :
        Set (weightedRestrictedSubring T hT))) ?_ ?_)
  · intro U _
    obtain ⟨n, -, hn⟩ := hV.toHasBasis.mem_iff.mp (U.isOpen.mem_nhds U.zero_mem)
    exact ⟨n, trivial, weightedNhd_mono hn⟩
  · intro n _
    exact ⟨V n, trivial, le_rfl⟩

end TauCeti.Huber
