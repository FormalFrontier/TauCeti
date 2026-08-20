/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Covering
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.RecoveredSubgroup

/-!
# Aspherical spaces through the universal cover and its subgroup quotients

Under the standing hypotheses of this development — `X` path-connected, locally
path-connected and semilocally simply connected — every homotopy group of `X` in a dimension
at least two is a homotopy group of the universal cover. Asphericity of `X` is therefore a
property of the universal cover alone: `X` is aspherical exactly when the higher homotopy
groups of `UniversalCover x₀` vanish. Since the universal cover is simply connected, that
condition says precisely that it is weakly contractible.

This turns the Galois correspondence of Stage 2 into a statement about Eilenberg--Mac Lane
spaces. Every subgroup `H ≤ π₁(X, x₀)` is realised by the connected cover
`UniversalCover x₀ / H`, whose fundamental group is `Hᵐᵒᵖ`, hence isomorphic to `H`; when `X` is a
`K(G, 1)` that cover is aspherical too, so it is a `K(H, 1)`. In particular every subgroup of
the fundamental group of a `K(G, 1)` is isomorphic to the fundamental group of a `K(H, 1)`
realised as a covering space of `X`.

The general covering-space input is
`IsCoveringMap.isAspherical_totalSpace`; the only work here is to supply the
universal cover and the covers attached to subgroups as instances of it, with their
distinguished basepoints.

This advances `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13, "`K(G, 1)`
spaces", by tying that item to the Stage 2 classification: the covers produced by item 7 of
that stage are Eilenberg--Mac Lane spaces whenever the base is.

## Main declarations

* `TauCeti.UniversalCover.isAspherical_iff`: **a space is aspherical exactly when the higher
  homotopy groups of its universal cover vanish**.
* `TauCeti.UniversalCover.isEilenbergMacLaneSpaceOne`: the resulting `K(G, 1)` recognition
  principle.
* `TauCeti.UniversalCover.isAspherical_subgroupQuotient` and
  `TauCeti.UniversalCover.isEilenbergMacLaneSpaceOne_subgroupQuotient`: **the cover attached
  to `H ≤ π₁(X, x₀)` over a `K(G, 1)` is a `K(H, 1)`**.

## References

The cover attached to a subgroup and its fundamental group come from
`TauCeti.AlgebraicTopology.UniversalCover.Classification.Existence` and
`…Classification.RecoveredSubgroup`, which adapt Kim Morrison's universal-cover construction
in [mathlib4#38292](https://github.com/leanprover-community/mathlib4/pull/38292) and use
Junyan Xu's quotient-covering API in `Mathlib/Topology/Homotopy/Lifting.lean`. Compare
Section 1.B of [hatcher02]; no external formalization is copied or adapted here.
-/

public section

open scoped Topology Topology.Homotopy

namespace TauCeti.UniversalCover

variable {X : Type*} [TopologicalSpace X] [LocallyPathConnectedSpace X] [PathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X] (x₀ : X)

/-- **A space is aspherical exactly when the higher homotopy groups of its universal cover
vanish.**

Together with simple connectedness of the universal cover, the right-hand side says that the
universal cover is weakly contractible. -/
theorem isAspherical_iff :
    IsAspherical X x₀ ↔
      ∀ n : ℕ,
        Subsingleton (π_ (n + 2) (UniversalCover x₀) (basepointLift x₀ : UniversalCover x₀)) :=
  ⟨fun h n ↦ ((isCoveringMap x₀).subsingleton_homotopyGroup_iff
      (proj_basepointLift x₀) n).mpr (h.subsingleton_homotopyGroup n),
    fun h ↦
      (isCoveringMap x₀).isAspherical_of_subsingleton_homotopyGroup proj_surjective
        (proj_basepointLift x₀) h⟩

/-- **A space whose universal cover has vanishing higher homotopy groups is a `K(G, 1)`**, for
any group `G` isomorphic to its fundamental group. -/
theorem isEilenbergMacLaneSpaceOne {G : Type*} [Group G] (e : FundamentalGroup X x₀ ≃* G)
    (h : ∀ n : ℕ,
      Subsingleton (π_ (n + 2) (UniversalCover x₀) (basepointLift x₀ : UniversalCover x₀))) :
    IsEilenbergMacLaneSpaceOne G X x₀ :=
  IsEilenbergMacLaneSpaceOne.mk ((isAspherical_iff x₀).mpr h) ⟨e⟩

variable (H : Subgroup (FundamentalGroup X x₀))

/-- The cover of an aspherical space attached to a subgroup of its fundamental group is
aspherical. -/
theorem isAspherical_subgroupQuotient (h : IsAspherical X x₀) :
    IsAspherical (SubgroupQuotient x₀ H) (SubgroupQuotient.basepoint x₀ H) :=
  (isCoveringMap_subgroupQuotientProj x₀ H).isAspherical_totalSpace
    (subgroupQuotientProj_basepoint x₀ H) h

/-- **The cover attached to `H ≤ π₁(X, x₀)` over a `K(G, 1)` is a `K(H, 1)`.**

So every subgroup of the fundamental group of an aspherical space is isomorphic to the
fundamental group of an aspherical covering space of it. The `ᵐᵒᵖ` recorded by
`TauCeti.UniversalCover.SubgroupQuotient.fundamentalGroupEquiv` disappears along
`MulEquiv.inv'`. -/
theorem isEilenbergMacLaneSpaceOne_subgroupQuotient (h : IsAspherical X x₀) :
    IsEilenbergMacLaneSpaceOne H (SubgroupQuotient x₀ H) (SubgroupQuotient.basepoint x₀ H) :=
  IsEilenbergMacLaneSpaceOne.mk (isAspherical_subgroupQuotient x₀ H h)
    ⟨(SubgroupQuotient.fundamentalGroupEquiv x₀ H).trans (MulEquiv.inv' H).symm⟩

end TauCeti.UniversalCover

end
