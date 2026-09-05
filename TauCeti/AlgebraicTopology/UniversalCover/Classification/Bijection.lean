/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.RecoveredSubgroup
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Regular
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Unpointed
import TauCeti.Topology.IsLocalHomeomorph

/-!
# Subgroups parametrise the pointed connected covers bijectively

Two halves of the correspondence between subgroups of `π₁(X, x₀)` and pointed connected covers
of `(X, x₀)` are already available. The comparison theorem
`TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_iff_range_eq` says a pointed connected cover is
determined by the subgroup it recovers, and `TauCeti.UniversalCover.subgroupQuotientProj`
together with `TauCeti.UniversalCover.range_mapOfEq_subgroupQuotientProj` builds, for every
subgroup `H`, a pointed cover recovering `H`. What neither states is that *every* pointed
connected cover arises this way.

This file supplies that statement and reads the correspondence off it:

* a pointed connected cover of `(X, x₀)` is isomorphic over `X`, by a homeomorphism matching the
  chosen lift with the distinguished point, to `UniversalCover x₀ / H` for the subgroup `H` it
  recovers, and `H` is the *only* subgroup with that property;
* the covers attached to `H` and to `K` are isomorphic as pointed covers exactly when `H = K`,
  and as unpointed covers exactly when `H` and `K` are conjugate.

Together with the order statement
`TauCeti.UniversalCover.exists_isCoveringMap_subgroupQuotientProj_comp_eq_iff_le`, which says
the cover attached to `H` covers the cover attached to `K` precisely when `H ≤ K`, this is the
Galois correspondence between subgroups of `π₁(X, x₀)` and connected covers of `X`. The
regular-cover criterion is read off in the same way: the cover attached to `H` is regular
exactly when `H` is normal.

The standing hypotheses are those of the whole construction — `X` path-connected, locally
path-connected and semilocally simply connected — because the universal cover is what the
subgroup quotients are built from.

## Main declarations

* `TauCeti.UniversalCover.exists_homeomorph_subgroupQuotient_of_range_eq`: **a pointed connected
  cover is the quotient of the universal cover by the subgroup it recovers.**
* `TauCeti.UniversalCover.existsUnique_subgroup_homeomorph_subgroupQuotient`: **the recovering
  subgroup is the unique parameter that realises a given pointed connected cover**, so subgroups
  of `π₁(X, x₀)` parametrise pointed connected covers bijectively.
* `TauCeti.UniversalCover.exists_homeomorph_subgroupQuotient_comp_eq_iff_eq`: two subgroup
  quotients are isomorphic as *pointed* covers exactly when the subgroups are equal.
* `TauCeti.UniversalCover.exists_homeomorph_subgroupQuotient_comp_eq_iff_exists_eq_map_conj`: they
  are isomorphic as *unpointed* covers exactly when the subgroups are conjugate.
* `TauCeti.UniversalCover.isRegular_subgroupQuotientProj_iff_normal`: the cover attached to `H`
  is regular exactly when `H` is normal.

## References

The mathematics is Hatcher, *Algebraic Topology*, Theorem 1.38 and the classification corollary
that follows it. The construction consumed here is the based-path universal cover adapted from
Kim Morrison's [mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292),
and the lifting criterion underlying the comparison theorems is Junyan Xu's, in
`Mathlib/Topology/Homotopy/Lifting.lean`.
-/

public section

namespace TauCeti.UniversalCover

open _root_.FundamentalGroup

variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] [LocallyPathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X)

/-- **A pointed connected cover is the quotient of the universal cover by the subgroup it
recovers.** If a covering map `p` with path-connected total space and a lift `e₀` of `x₀` recover
`H ≤ π₁(X, x₀)`, then `E` is homeomorphic to `UniversalCover x₀ / H` over `X`, by a
homeomorphism carrying `e₀` to the distinguished point.

This is the surjectivity of the subgroup parametrisation. -/
theorem exists_homeomorph_subgroupQuotient_of_range_eq {E : Type*} [TopologicalSpace E]
    [PathConnectedSpace E] {p : E → X} (hp : IsCoveringMap p)
    {e₀ : E} (hpe : p e₀ = x₀) (H : Subgroup (FundamentalGroup X x₀))
    (hH : (mapOfEq ⟨p, hp.continuous⟩ hpe).range = H) :
    ∃ h : E ≃ₜ SubgroupQuotient x₀ H, h e₀ = SubgroupQuotient.basepoint x₀ H ∧
      subgroupQuotientProj x₀ H ∘ h = p := by
  have := hp.isLocalHomeomorph.locallyPathConnectedSpace
  have := locallyPathConnectedSpace_subgroupQuotient x₀ H
  exact TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_of_range_eq hp
    (isCoveringMap_subgroupQuotientProj x₀ H) hpe (subgroupQuotientProj_basepoint x₀ H)
    (hH.trans (range_mapOfEq_subgroupQuotientProj x₀ H).symm)

/-- **Every pointed connected cover of `(X, x₀)` is realised by exactly one subgroup of
`π₁(X, x₀)`.** The subgroups of `π₁(X, x₀)` therefore parametrise the pointed connected covers
of `(X, x₀)` bijectively, up to isomorphism over `X` respecting the chosen lifts. -/
theorem existsUnique_subgroup_homeomorph_subgroupQuotient {E : Type*} [TopologicalSpace E]
    [PathConnectedSpace E] {p : E → X} (hp : IsCoveringMap p)
    {e₀ : E} (hpe : p e₀ = x₀) :
    ∃! H : Subgroup (FundamentalGroup X x₀), ∃ h : E ≃ₜ SubgroupQuotient x₀ H,
      h e₀ = SubgroupQuotient.basepoint x₀ H ∧ subgroupQuotientProj x₀ H ∘ h = p := by
  have := hp.isLocalHomeomorph.locallyPathConnectedSpace
  refine ⟨(mapOfEq ⟨p, hp.continuous⟩ hpe).range,
    exists_homeomorph_subgroupQuotient_of_range_eq x₀ hp hpe _ rfl, fun H hH => ?_⟩
  have := locallyPathConnectedSpace_subgroupQuotient x₀ H
  rw [← range_mapOfEq_subgroupQuotientProj x₀ H]
  exact ((TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_iff_range_eq hp
    (isCoveringMap_subgroupQuotientProj x₀ H) hpe (subgroupQuotientProj_basepoint x₀ H)).mp hH).symm

/-- **The covers attached to two subgroups are isomorphic as pointed covers exactly when the
subgroups are equal.** This is the injectivity of the subgroup parametrisation. -/
theorem exists_homeomorph_subgroupQuotient_comp_eq_iff_eq
    (H K : Subgroup (FundamentalGroup X x₀)) :
    (∃ h : SubgroupQuotient x₀ H ≃ₜ SubgroupQuotient x₀ K,
        h (SubgroupQuotient.basepoint x₀ H) = SubgroupQuotient.basepoint x₀ K ∧
          subgroupQuotientProj x₀ K ∘ h = subgroupQuotientProj x₀ H) ↔ H = K := by
  have := locallyPathConnectedSpace_subgroupQuotient x₀ H
  have := locallyPathConnectedSpace_subgroupQuotient x₀ K
  rw [TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_iff_range_eq
    (isCoveringMap_subgroupQuotientProj x₀ H) (isCoveringMap_subgroupQuotientProj x₀ K)
    (subgroupQuotientProj_basepoint x₀ H) (subgroupQuotientProj_basepoint x₀ K),
    range_mapOfEq_subgroupQuotientProj, range_mapOfEq_subgroupQuotientProj]

/-- **The covers attached to two subgroups are isomorphic as unpointed covers exactly when the
subgroups are conjugate.** Forgetting the distinguished points therefore turns the subgroup
parametrisation into a bijection between conjugacy classes of subgroups of `π₁(X, x₀)` and
isomorphism classes of connected covers of `X`. -/
theorem exists_homeomorph_subgroupQuotient_comp_eq_iff_exists_eq_map_conj
    (H K : Subgroup (FundamentalGroup X x₀)) :
    (∃ h : SubgroupQuotient x₀ H ≃ₜ SubgroupQuotient x₀ K,
        subgroupQuotientProj x₀ K ∘ h = subgroupQuotientProj x₀ H) ↔
      ∃ γ : FundamentalGroup X x₀, K = H.map (MulAut.conj γ).toMonoidHom := by
  have := locallyPathConnectedSpace_subgroupQuotient x₀ H
  have := locallyPathConnectedSpace_subgroupQuotient x₀ K
  rw [TauCeti.IsCoveringMap.exists_homeomorph_comp_eq_iff_exists_range_eq_map_conj
    (isCoveringMap_subgroupQuotientProj x₀ H) (isCoveringMap_subgroupQuotientProj x₀ K)
    (subgroupQuotientProj_basepoint x₀ H) (subgroupQuotientProj_basepoint x₀ K)]
  simp only [range_mapOfEq_subgroupQuotientProj]

/-- **The cover attached to `H` is a regular cover exactly when `H` is normal.** -/
@[simp]
theorem isRegular_subgroupQuotientProj_iff_normal (H : Subgroup (FundamentalGroup X x₀)) :
    Deck.IsRegular (subgroupQuotientProj x₀ H) ↔ H.Normal := by
  have := locallyPathConnectedSpace_subgroupQuotient x₀ H
  refine Iff.trans (TauCeti.IsCoveringMap.isRegular_iff_normal_range
    (isCoveringMap_subgroupQuotientProj x₀ H)
    ⟨SubgroupQuotient.basepoint x₀ H,
      Set.mem_singleton_iff.mpr (subgroupQuotientProj_basepoint x₀ H)⟩) ?_
  rw [range_mapOfEq_subgroupQuotientProj]

end TauCeti.UniversalCover
