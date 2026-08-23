/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.SubgroupQuotient
public import TauCeti.Topology.Covering.Category
public import TauCeti.Topology.Covering.Quotient
import TauCeti.Topology.Homotopy.Monodromy.Functoriality

/-!
# The covering associated to a subgroup

For a subgroup `H ≤ π₁(X, x₀)`, `UniversalCover.SubgroupQuotient x₀ H` is already defined as
the orbit quotient of the universal cover by `H`, and `UniversalCover.subgroupQuotientProj`
is its descended endpoint projection. This file proves that the descended projection is a
covering map.

The two inputs are that `UniversalCover.proj` and `UniversalCover.subgroupQuotientMap` are
quotient covering maps, for `π₁(X, x₀)` and for `H` respectively, and that the first factors
through the second. `TauCeti.IsQuotientCoveringMap.isCoveringMap_of_comp` turns exactly that
data into a covering map: the sheets of the descended projection over the image of a locally
disjoint set `U` are the images of the translates of `U`. Nothing about good neighbourhoods of
the base, their path-connectedness, or the transport of a sheet of `proj` along the
fundamental-group action enters here, because the general statement uses only the disjointness
built into `IsQuotientCoveringMap`.

The conclusion is not inherited formally from the two quotient maps being covering maps: the
deck group of `UniversalCover x₀ / H` over `X` is the normalizer quotient `N(H) / H`, which is
transitive on the fibres only for normal `H`, so the descended projection is generally not
itself a quotient covering map for any group.

## Main declarations

* `TauCeti.UniversalCover.isCoveringMap_subgroupQuotientProj`: the cover associated to
  `H ≤ π₁(X, x₀)` is a covering space of `X`.
* `TauCeti.UniversalCover.subgroupCover`: the same cover, bundled as a connected covering space.
* `TauCeti.UniversalCover.subgroupCoverBasepointFiber`: its distinguished fibre point.

## References

This completes the existence half in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
item 7: construct the pointed connected cover `UniversalCover x₀ / H`. It uses the universal
cover adapted from Kim Morrison's
[mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292) and Mathlib's
quotient-covering-map interface due to Junyan Xu.
-/

public section
noncomputable section

variable {X : Type*} [TopologicalSpace X]

namespace TauCeti.UniversalCover

open CategoryTheory Topology

/-- The endpoint projection on the quotient of the universal cover by `H` is a covering map. -/
theorem isCoveringMap_subgroupQuotientProj [LocallyPathConnectedSpace X]
    [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (x₀ : X) (H : Subgroup (FundamentalGroup X x₀)) :
    IsCoveringMap (subgroupQuotientProj x₀ H) :=
  IsQuotientCoveringMap.isCoveringMap_of_comp (isQuotientCoveringMap (x₀ := x₀))
    (isQuotientCoveringMap_subgroupQuotientMap x₀ H)
    (subgroupQuotientProj_comp_subgroupQuotientMap x₀ H)

/-- The connected covering space associated to a subgroup `H ≤ π₁(X, x₀)`, obtained by
quotienting the universal cover by `H`. -/
def subgroupCover [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) (H : Subgroup (FundamentalGroup X x₀)) :
    ConnectedCoveringSpace (TopCat.of X) :=
  ConnectedCoveringSpace.mk
    (TopCat.ofHom
      ⟨subgroupQuotientProj x₀ H, continuous_subgroupQuotientProj x₀ H⟩)
    (isCoveringMap_subgroupQuotientProj x₀ H)

/-- The total space of the cover associated to `H` is the quotient of the universal cover by
`H`. -/
@[simp]
theorem subgroupCover_coe [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) (H : Subgroup (FundamentalGroup X x₀)) :
    (subgroupCover x₀ H : TopCat) = TopCat.of (SubgroupQuotient x₀ H) := by
  rw [subgroupCover]
  exact ConnectedCoveringSpace.mk_coe _ _

/-- The projection of the cover associated to `H` is the descended endpoint projection. -/
@[simp]
theorem subgroupCover_proj [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) (H : Subgroup (FundamentalGroup X x₀)) :
    (subgroupCover x₀ H).proj =
      eqToHom (subgroupCover_coe x₀ H) ≫
        TopCat.ofHom
          ⟨subgroupQuotientProj x₀ H, continuous_subgroupQuotientProj x₀ H⟩ := by
  simpa only [subgroupCover] using
    ConnectedCoveringSpace.mk_proj
      (TopCat.ofHom
        ⟨subgroupQuotientProj x₀ H, continuous_subgroupQuotientProj x₀ H⟩)
      (isCoveringMap_subgroupQuotientProj x₀ H)

/-- The characteristic equality of total spaces for `subgroupCover`, viewed as a
homeomorphism. -/
def subgroupCoverTotalSpaceHomeomorph [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) (H : Subgroup (FundamentalGroup X x₀)) :
    (subgroupCover x₀ H : TopCat) ≃ₜ SubgroupQuotient x₀ H :=
  TopCat.homeoOfIso (eqToIso (subgroupCover_coe x₀ H))

/-- The characteristic total-space homeomorphism commutes with the two projections. -/
theorem subgroupQuotientProj_subgroupCoverTotalSpaceHomeomorph
    [LocallyPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (x₀ : X) (H : Subgroup (FundamentalGroup X x₀)) (e : (subgroupCover x₀ H : TopCat)) :
    subgroupQuotientProj x₀ H (subgroupCoverTotalSpaceHomeomorph x₀ H e) =
      (subgroupCover x₀ H).proj e := by
  have h := DFunLike.congr_fun (congrArg TopCat.Hom.hom (subgroupCover_proj x₀ H)) e
  exact h.symm

/-- Transport from the fibre of the bundled subgroup cover to the fibre of its quotient
projection. -/
def subgroupCoverFiberEquivSubgroupQuotient [LocallyPathConnectedSpace X]
    [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (x₀ : X)
    (H : Subgroup (FundamentalGroup X x₀)) :
    ⇑(subgroupCover x₀ H).proj ⁻¹' {x₀} ≃ subgroupQuotientProj x₀ H ⁻¹' {x₀} :=
  ((subgroupCoverTotalSpaceHomeomorph x₀ H).subtype fun e => by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [subgroupQuotientProj_subgroupCoverTotalSpaceHomeomorph x₀ H e]).toEquiv

/-- On underlying points, fibre transport applies the characteristic homeomorphism. -/
@[simp]
private theorem subgroupCoverFiberEquivSubgroupQuotient_apply_coe [LocallyPathConnectedSpace X]
    [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (x₀ : X)
    (H : Subgroup (FundamentalGroup X x₀)) (e : ⇑(subgroupCover x₀ H).proj ⁻¹' {x₀}) :
    (subgroupCoverFiberEquivSubgroupQuotient x₀ H e : SubgroupQuotient x₀ H) =
      subgroupCoverTotalSpaceHomeomorph x₀ H e :=
  rfl

/-- Fibre transport commutes with monodromy. -/
@[simp]
theorem subgroupCoverFiberEquivSubgroupQuotient_apply_monodromy
    [LocallyPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (x₀ : X) (H : Subgroup (FundamentalGroup X x₀)) (g : FundamentalGroup X x₀)
    (e : ⇑(subgroupCover x₀ H).proj ⁻¹' {x₀}) :
    subgroupCoverFiberEquivSubgroupQuotient x₀ H
        ((subgroupCover x₀ H).isCoveringMap_proj.monodromy g e) =
      (isCoveringMap_subgroupQuotientProj x₀ H).monodromy g
        (subgroupCoverFiberEquivSubgroupQuotient x₀ H e) := by
  have hmonodromy := TauCeti.IsCoveringMap.fiberMap_monodromy
    (subgroupCover x₀ H).isCoveringMap_proj
    (isCoveringMap_subgroupQuotientProj x₀ H)
    (subgroupCoverTotalSpaceHomeomorph x₀ H)
    (funext (subgroupQuotientProj_subgroupCoverTotalSpaceHomeomorph x₀ H)) g e
  have hfiberMap (e' : ⇑(subgroupCover x₀ H).proj ⁻¹' {x₀}) :
      TauCeti.IsCoveringMap.fiberMap (subgroupCoverTotalSpaceHomeomorph x₀ H)
          (funext (subgroupQuotientProj_subgroupCoverTotalSpaceHomeomorph x₀ H)) x₀ e' =
        subgroupCoverFiberEquivSubgroupQuotient x₀ H e' := by
    apply Subtype.ext
    rw [TauCeti.IsCoveringMap.fiberMap_apply_coe]
    exact (subgroupCoverFiberEquivSubgroupQuotient_apply_coe x₀ H e').symm
  simpa only [hfiberMap] using hmonodromy

/-- The distinguished point in the fibre over `x₀` of the cover associated to `H`. -/
def subgroupCoverBasepointFiber [LocallyPathConnectedSpace X] [PathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] (x₀ : X) (H : Subgroup (FundamentalGroup X x₀)) :
    ⇑(subgroupCover x₀ H).proj ⁻¹' {x₀} :=
  (subgroupCoverFiberEquivSubgroupQuotient x₀ H).symm
    (SubgroupQuotient.basepointFiber x₀ H)

/-- Fibre transport identifies the bundled distinguished point with the quotient distinguished
point. -/
@[simp]
theorem subgroupCoverFiberEquivSubgroupQuotient_apply_basepoint
    [LocallyPathConnectedSpace X] [PathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
    (x₀ : X) (H : Subgroup (FundamentalGroup X x₀)) :
    subgroupCoverFiberEquivSubgroupQuotient x₀ H (subgroupCoverBasepointFiber x₀ H) =
      SubgroupQuotient.basepointFiber x₀ H :=
  Equiv.apply_symm_apply _ _

end TauCeti.UniversalCover
