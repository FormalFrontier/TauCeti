/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.RecoveredSubgroup
public import TauCeti.Topology.Covering.Factorization
import TauCeti.Topology.IsLocalHomeomorph

/-!
# The Galois correspondence is a correspondence of towers of covers

Pointed connected covers of `(X, x)` are classified by the subgroup of `π₁(X, x)` they recover,
and `TauCeti.IsCoveringMap.exists_continuousMap_comp_eq_iff_range_le` already says that a map of
pointed covers exists exactly when the recovered subgroups are nested. What that statement leaves
open is what kind of map it is. This file upgrades it: when the target cover is locally connected,
the map is itself a covering map, so a nesting of subgroups is realized by an intermediate
covering and not merely by a continuous comparison.

The upgrade is `IsCoveringMap.of_comp_eq`, which needs nothing about the subgroups: any
continuous map between two covering spaces of the same base is a covering map when its target is
locally connected.

Specializing to the covers built from subgroups turns the classification into an order statement.
For `H, K ≤ π₁(X, x₀)` the cover `UniversalCover x₀ / H` covers `UniversalCover x₀ / K`
compatibly with basepoints exactly when `H ≤ K`, because those covers recover `H` and `K`. The
universal cover itself sits above all nonempty covers after choosing points in a common fibre.
This is recorded separately because it needs no subgroup: the universal lifting property produces
the comparison map, and the upgrade above makes that map a covering map.

## Main declarations

* `IsCoveringMap.exists_isCoveringMap_comp_eq_iff_range_le`: **a pointed cover covers another,
  by a covering map over the base, exactly when the recovered subgroups are nested.**
* `TauCeti.UniversalCover.exists_isCoveringMap_comp_eq_proj`: **the universal cover covers a
  nonempty covering space of `X` after choosing points in a common fibre.**
* `TauCeti.UniversalCover.exists_isCoveringMap_subgroupQuotientProj_comp_eq_iff_le`: **the cover
  attached to `H` covers the cover attached to `K` exactly when `H ≤ K`.**

## References

This work consumes the based-path universal cover adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292), the lifting
criterion in Mathlib's `Topology/Homotopy/Lifting.lean` due to Junyan Xu, and the covers attached
to subgroups already built here. The mathematics is Hatcher, *Algebraic Topology*, Section 1.3.
-/

public section
noncomputable section

namespace TauCeti

open _root_.FundamentalGroup

variable {E F X : Type*} [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace X]
  {p : E → X} {q : F → X} {x : X} {e₀ : E} {f₀ : F}

/-- **A pointed cover covers another one, by a covering map over `X`, exactly when the subgroup it
recovers is contained in the subgroup the other recovers.**

This strengthens `TauCeti.IsCoveringMap.exists_continuousMap_comp_eq_iff_range_le`, which produces
only a continuous map: when the target is locally connected, a map of covers is automatically a
covering map, by `IsCoveringMap.of_comp_eq`. -/
theorem _root_.IsCoveringMap.exists_isCoveringMap_comp_eq_iff_range_le [LocallyConnectedSpace F]
    [PathConnectedSpace E] [LocallyPathConnectedSpace E] (hp : IsCoveringMap p)
    (hq : IsCoveringMap q) (hpe : p e₀ = x) (hqf : q f₀ = x) :
    (∃ g : C(E, F), IsCoveringMap g ∧ g e₀ = f₀ ∧ q ∘ g = p) ↔
      (mapOfEq ⟨p, hp.continuous⟩ hpe).range ≤ (mapOfEq ⟨q, hq.continuous⟩ hqf).range := by
  refine ⟨fun hg => ?_, fun hle => ?_⟩
  · obtain ⟨g, -, hg₀, hgc⟩ := hg
    exact (TauCeti.IsCoveringMap.exists_continuousMap_comp_eq_iff_range_le hp.continuous hq hpe
      hqf).mp ⟨g, hg₀, hgc⟩
  · obtain ⟨g, ⟨hg₀, hgc⟩, -⟩ :=
      TauCeti.IsCoveringMap.existsUnique_continuousMap_comp_eq_of_range_le hp.continuous hq hpe
        hqf hle
    exact ⟨g, hp.of_comp_eq hq g.continuous hgc, hg₀, hgc⟩

namespace UniversalCover

variable [LocallyPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]

/-- **The universal cover covers any nonempty covering space of `X` after choosing points in a
common fibre**, by a covering map over `X` matching those points.

The comparison map itself is the universal lifting property of the universal cover; what is added
here is that it is a covering map. -/
theorem exists_isCoveringMap_comp_eq_proj (x₀ : X) {F : Type*} [TopologicalSpace F] {q : F → X}
    (hq : IsCoveringMap q) (e₀ : UniversalCover x₀) (f₀ : F) (he : q f₀ = proj e₀) :
    ∃ g : C(UniversalCover x₀, F), IsCoveringMap g ∧ g e₀ = f₀ ∧ q ∘ g = proj := by
  have := (isCoveringMap x₀).isLocalHomeomorph.locallyPathConnectedSpace
  have := hq.isLocalHomeomorph.locallyPathConnectedSpace
  obtain ⟨g, ⟨hg₀, hgc⟩, -⟩ :=
    hq.existsUnique_continuousMap_lifts ⟨proj, continuous_proj x₀⟩ e₀ f₀ he
  exact ⟨g, (isCoveringMap x₀).of_comp_eq hq g.continuous hgc, hg₀, hgc⟩

/-- **The cover attached to `H ≤ π₁(X, x₀)` covers the cover attached to `K` exactly when
`H ≤ K`.** The comparison is a covering map over `X` matching the two distinguished points.

This is the order-preserving half of the Galois correspondence between subgroups of `π₁(X, x₀)`
and pointed connected covers of `(X, x₀)`. -/
theorem exists_isCoveringMap_subgroupQuotientProj_comp_eq_iff_le (x₀ : X)
    (H K : Subgroup (FundamentalGroup X x₀)) :
    (∃ g : C(SubgroupQuotient x₀ H, SubgroupQuotient x₀ K), IsCoveringMap g ∧
        g (SubgroupQuotient.basepoint x₀ H) = SubgroupQuotient.basepoint x₀ K ∧
        subgroupQuotientProj x₀ K ∘ g = subgroupQuotientProj x₀ H) ↔ H ≤ K := by
  have := locallyPathConnectedSpace_subgroupQuotient x₀ H
  have := locallyPathConnectedSpace_subgroupQuotient x₀ K
  rw [IsCoveringMap.exists_isCoveringMap_comp_eq_iff_range_le
    (isCoveringMap_subgroupQuotientProj x₀ H) (isCoveringMap_subgroupQuotientProj x₀ K)
    (subgroupQuotientProj_basepoint x₀ H) (subgroupQuotientProj_basepoint x₀ K),
    range_mapOfEq_subgroupQuotientProj, range_mapOfEq_subgroupQuotientProj]

end UniversalCover

end TauCeti
