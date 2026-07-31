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
cover and proves that this map is a quotient covering map. The class of the constant path
supplies its distinguished point.

This is the first construction step in the subgroup-to-cover direction of the classification
of covering spaces. This file descends `UniversalCover.proj` to the quotient; a later file will
prove that the descended map is a covering map and identify the subgroup it recovers.

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
open Topology

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

/-- The distinguished point is the quotient class of the constant path at the basepoint. -/
@[simp]
theorem basepoint_eq_mk (H : Subgroup (FundamentalGroup X x₀)) :
    basepoint x₀ H = Quotient.mk'' (mk x₀ (Path.Homotopic.Quotient.refl x₀)) :=
  (rfl)

end SubgroupQuotient

/-- The canonical map from the universal cover to its orbit quotient by `H`. -/
def subgroupQuotientMap (H : Subgroup (FundamentalGroup X x₀)) :
    UniversalCover x₀ → SubgroupQuotient x₀ H :=
  @Quotient.mk' _ (MulAction.orbitRel H (UniversalCover x₀))

/-- The subgroup quotient map sends a representative to its quotient class. -/
@[simp]
theorem subgroupQuotientMap_apply (H : Subgroup (FundamentalGroup X x₀))
    (e : UniversalCover x₀) :
    subgroupQuotientMap x₀ H e = Quotient.mk'' e :=
  (rfl)

/-- Two points have the same image in the subgroup quotient exactly when they lie in the same
`H`-orbit. -/
theorem subgroupQuotientMap_eq_iff (H : Subgroup (FundamentalGroup X x₀))
    {e₁ e₂ : UniversalCover x₀} :
    subgroupQuotientMap x₀ H e₁ = subgroupQuotientMap x₀ H e₂ ↔
      e₁ ∈ MulAction.orbit H e₂ := by
  rw [subgroupQuotientMap_apply, subgroupQuotientMap_apply, Quotient.eq'',
    MulAction.orbitRel_apply]

/-- The fundamental-group action is locally disjoint without a global connectedness assumption. -/
private theorem fundamentalGroup_disjoint [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (e : UniversalCover x₀) :
    ∃ U ∈ 𝓝 e, ∀ g : FundamentalGroup X x₀,
      ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  rcases e with ⟨x, q⟩
  induction q using Quotient.inductionOn with
  | h p =>
    obtain ⟨U, hU_open, hxU, -, hU_slsc⟩ :=
      exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial x
    let V := sheet (x₀ := x₀) U hxU (Path.Homotopic.Quotient.mk p)
    have heV : UniversalCover.mk x (Path.Homotopic.Quotient.mk p) ∈ V :=
      by simpa only [V, ofBasedPath_ofPath] using mem_sheet_self (x₀ := x₀) hxU p
    refine ⟨V, (isOpen_sheet U hU_open hxU _).mem_nhds heV, fun g hg ↦ ?_⟩
    obtain ⟨z, ⟨u, huV, rfl⟩, hguV⟩ := hg
    have hgu : g • u = u :=
      (proj_injOn_sheet hU_slsc hxU (Path.Homotopic.Quotient.mk p)) hguV huV (proj_smul g u)
    exact IsCancelSMul.right_cancel g 1 u (hgu.trans (one_smul _ u).symm)

/-- The quotient map by any subgroup of the fundamental group is a quotient covering map. -/
theorem isQuotientCoveringMap_subgroupQuotientMap
    [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (H : Subgroup (FundamentalGroup X x₀)) :
    IsQuotientCoveringMap (subgroupQuotientMap x₀ H) H where
  __ := isQuotientMap_quotient_mk'
  continuous_const_smul g := continuous_const_smul g.1
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint e := by
    obtain ⟨U, heU, hU⟩ := fundamentalGroup_disjoint x₀ e
    exact ⟨U, heU, fun g hg => Subtype.ext (hU g hg)⟩

/-- The endpoint projection is invariant under the orbit relation defining the subgroup quotient. -/
private theorem proj_eq_of_orbitRel (H : Subgroup (FundamentalGroup X x₀))
    {e₁ e₂ : UniversalCover x₀} (h : MulAction.orbitRel H (UniversalCover x₀) e₁ e₂) :
    proj e₁ = proj e₂ := by
  rw [MulAction.orbitRel_apply] at h
  obtain ⟨g, rfl⟩ := h
  exact proj_smul g.1 _

/-- The endpoint projection descended to the subgroup quotient. -/
def subgroupQuotientProj (H : Subgroup (FundamentalGroup X x₀)) :
    SubgroupQuotient x₀ H → X :=
  Quotient.lift proj fun _ _ h => proj_eq_of_orbitRel x₀ H h

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
theorem subgroupQuotientProj_basepoint (H : Subgroup (FundamentalGroup X x₀)) :
    subgroupQuotientProj x₀ H (SubgroupQuotient.basepoint x₀ H) = x₀ :=
  subgroupQuotientProj_mk x₀ H _

/-- The descended endpoint projection is continuous. -/
theorem continuous_subgroupQuotientProj
    (H : Subgroup (FundamentalGroup X x₀)) :
    Continuous (subgroupQuotientProj x₀ H) := by
  rw [isQuotientMap_quotient_mk'.continuous_iff]
  have h := subgroupQuotientProj_comp_subgroupQuotientMap x₀ H
  simp only [subgroupQuotientMap] at h
  rw [h]
  exact continuous_proj x₀

/-- The descended endpoint projection is surjective when the base is path connected. -/
theorem subgroupQuotientProj_surjective [PathConnectedSpace X]
    (H : Subgroup (FundamentalGroup X x₀)) :
    Function.Surjective (subgroupQuotientProj x₀ H) := by
  unfold subgroupQuotientProj
  exact Quotient.lift_surjective proj _ (proj_surjective (x₀ := x₀))

end TauCeti.UniversalCover
