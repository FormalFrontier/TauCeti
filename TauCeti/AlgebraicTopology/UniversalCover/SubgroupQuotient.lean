/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Action

/-!
# Quotients of the universal cover by subgroups

For a subgroup `H` of the fundamental group of `X`, this file defines the orbit quotient
`UniversalCover x₀ / H`. It equips that quotient with its canonical map from the universal
cover and proves that this map is a quotient covering map. The quotient is path connected,
and the class of the constant path supplies its distinguished point.

This is the first construction step in the subgroup-to-cover direction of the classification
of covering spaces. A later file can descend `UniversalCover.proj` to this quotient, prove that
the descended map to `X` is a covering map, and identify the subgroup it recovers.

## Main declarations

* `TauCeti.UniversalCover.SubgroupQuotient`: the orbit quotient by a subgroup of the
  fundamental group.
* `TauCeti.UniversalCover.SubgroupQuotient.basepoint`: the class of the constant based path.
* `TauCeti.UniversalCover.subgroupQuotientMap`: the quotient map.
* `TauCeti.UniversalCover.isQuotientCoveringMap_subgroupQuotientMap`: the quotient map is a
  quotient covering map, and hence a covering map.
* `TauCeti.UniversalCover.subgroupQuotientProj`: the endpoint projection descended to the
  subgroup quotient.

## References

This advances `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2, item 7: construct the pointed
connected cover associated to `H ≤ π₁(X, x₀)`. It reuses the fundamental-group action adapted
from Kim Morrison's work in [mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292)
and Mathlib's quotient-covering-map interface due to Junyan Xu.
-/

public section
noncomputable section

open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] (x₀ : X)

namespace TauCeti.UniversalCover

/-- The orbit quotient of the universal cover by a subgroup of the fundamental group. -/
abbrev SubgroupQuotient (H : Subgroup (FundamentalGroup X x₀)) :=
  MulAction.orbitRel.Quotient H (UniversalCover x₀)

namespace SubgroupQuotient

/-- The distinguished point in the subgroup quotient, represented by the constant path at the
basepoint. -/
def basepoint (H : Subgroup (FundamentalGroup X x₀)) : SubgroupQuotient x₀ H :=
  Quotient.mk'' (mk x₀ (Path.Homotopic.Quotient.refl x₀))

end SubgroupQuotient

/-- The canonical map from the universal cover to its orbit quotient by `H`. -/
def subgroupQuotientMap (H : Subgroup (FundamentalGroup X x₀)) :
    UniversalCover x₀ → SubgroupQuotient x₀ H :=
  Quotient.mk''

/-- The subgroup quotient map sends the constant-path point to the distinguished point. -/
@[simp]
theorem subgroupQuotientMap_basepoint (H : Subgroup (FundamentalGroup X x₀)) :
    subgroupQuotientMap x₀ H (mk x₀ (Path.Homotopic.Quotient.refl x₀)) =
      SubgroupQuotient.basepoint x₀ H :=
  (rfl)

/-- The quotient map by any subgroup of the fundamental group is a quotient covering map. -/
theorem isQuotientCoveringMap_subgroupQuotientMap
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (H : Subgroup (FundamentalGroup X x₀)) :
    IsQuotientCoveringMap (subgroupQuotientMap x₀ H) H where
  __ := isQuotientMap_quotient_mk'
  continuous_const_smul g := continuous_const_smul g.1
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint e := by
    obtain ⟨U, heU, hU⟩ := (isQuotientCoveringMap (x₀ := x₀)).disjoint e
    exact ⟨U, heU, fun g hg => Subtype.ext (hU g hg)⟩

/-- The quotient map by any subgroup of the fundamental group is a covering map. -/
theorem isCoveringMap_subgroupQuotientMap
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (H : Subgroup (FundamentalGroup X x₀)) :
    IsCoveringMap (subgroupQuotientMap x₀ H) :=
  (isQuotientCoveringMap_subgroupQuotientMap x₀ H).isCoveringMap

/-- The endpoint projection descended to the subgroup quotient. -/
def subgroupQuotientProj (H : Subgroup (FundamentalGroup X x₀)) :
    SubgroupQuotient x₀ H → X :=
  Quotient.lift proj fun _ _ h => by
    change MulAction.orbitRel H (UniversalCover x₀) _ _ at h
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨g, rfl⟩ := h
    exact proj_smul g.1 _

/-- The descended endpoint projection evaluates on an orbit representative as `proj`. -/
@[simp]
theorem subgroupQuotientProj_mk (H : Subgroup (FundamentalGroup X x₀))
    (e : UniversalCover x₀) :
    subgroupQuotientProj x₀ H (Quotient.mk'' e) = proj e :=
  (rfl)

/-- The endpoint projection factors through the quotient by every subgroup. -/
theorem subgroupQuotientProj_comp_subgroupQuotientMap
    (H : Subgroup (FundamentalGroup X x₀)) :
    subgroupQuotientProj x₀ H ∘ subgroupQuotientMap x₀ H = proj := by
  ext e
  exact subgroupQuotientProj_mk x₀ H e

/-- The distinguished point of the subgroup quotient lies over the basepoint. -/
@[simp]
theorem subgroupQuotientProj_basepoint (H : Subgroup (FundamentalGroup X x₀)) :
    subgroupQuotientProj x₀ H (SubgroupQuotient.basepoint x₀ H) = x₀ :=
  (rfl)

/-- The descended endpoint projection is continuous. -/
theorem continuous_subgroupQuotientProj
    [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (H : Subgroup (FundamentalGroup X x₀)) :
    Continuous (subgroupQuotientProj x₀ H) :=
  (isCoveringMap x₀).continuous.quotient_lift fun _ _ h => by
    change MulAction.orbitRel H (UniversalCover x₀) _ _ at h
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨g, rfl⟩ := h
    exact proj_smul g.1 _

/-- The descended endpoint projection is surjective when the base is path connected. -/
theorem subgroupQuotientProj_surjective [PathConnectedSpace X]
    (H : Subgroup (FundamentalGroup X x₀)) :
    Function.Surjective (subgroupQuotientProj x₀ H) := by
  intro x
  obtain ⟨e, rfl⟩ := proj_surjective (x₀ := x₀) x
  exact ⟨Quotient.mk'' e, subgroupQuotientProj_mk x₀ H e⟩

end TauCeti.UniversalCover
