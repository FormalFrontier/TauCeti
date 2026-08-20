/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.Opposite
public import Mathlib.Algebra.Group.Subgroup.Ker
public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.Topology.Homotopy.Covering
public import TauCeti.Topology.Homotopy.HomotopyGroup.Covering

/-!
# Asphericity and covering spaces

A covering map `p : E → X` is an isomorphism on homotopy groups in every dimension at least
two, so the higher homotopy of a cover and of its base are the same. Asphericity is therefore
inherited in both directions along a covering map, the only extra input being
path-connectedness of whichever space is not already known to be path-connected.

This file records that transfer and the two `K(G, 1)` recognition principles it yields.

* Downwards: the base of a *surjective* covering map with aspherical total space is aspherical.
  Combined with the identification of the fundamental group of the base of a simply connected
  quotient covering map, a group acting freely and properly discontinuously on a simply
  connected space whose higher homotopy vanishes has an orbit space of type `K(G, 1)`.
  This is the standard way `K(G, 1)` spaces are produced.
* Upwards: a path-connected covering space of an aspherical space is aspherical. Its
  fundamental group is the subgroup of `π₁` of the base recovered by `p`, because a covering
  map is injective on fundamental groups, so a path-connected cover of a `K(G, 1)` is a
  `K(H, 1)` for that subgroup `H`.

Taking the total space simply connected in the upwards direction says that the universal cover
of an aspherical space is weakly contractible: all of its homotopy groups vanish, including
`π₁`, which is where simple connectedness enters. Nothing here asserts that such a cover is
contractible; that is a genuinely stronger statement, requiring a Whitehead-type theorem which
this development does not have.

The `ᵐᵒᵖ` in Mathlib's `IsQuotientCoveringMap.fundamentalGroupEquiv` is invisible in the
`K(G, 1)` statement below: being a `K(G, 1)` is invariant under `MulEquiv.inv'`, the
isomorphism `G ≃* Gᵐᵒᵖ` sending `g` to `op g⁻¹`.

This advances `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13, "`K(G, 1)`
spaces", by supplying the covering-space recognition principle for them; the concrete circle
and torus examples were proved directly.

## Main declarations

* `IsCoveringMap.subsingleton_homotopyGroup_iff`: a cover and its base have the same
  higher homotopy groups.
* `IsCoveringMap.isAspherical`: **the base of a surjective covering map with aspherical
  total space is aspherical**.
* `IsCoveringMap.isAspherical_totalSpace`: **a path-connected covering space of an
  aspherical space is aspherical**.
* `IsCoveringMap.subsingleton_homotopyGroup_of_isAspherical`: **the simply connected
  cover of an aspherical space is weakly contractible**.
* `IsCoveringMap.isEilenbergMacLaneSpaceOne_totalSpace`: a path-connected cover of a
  `K(G, 1)` is a `K(H, 1)` for the subgroup `H` it recovers.
* `IsQuotientCoveringMap.isEilenbergMacLaneSpaceOne`: **the orbit space of a free,
  properly discontinuous action of `G` on a simply connected space with vanishing higher
  homotopy is a `K(G, 1)`**.

## References

The isomorphism on higher homotopy groups is
`TauCeti.IsCoveringMap.homotopyGroupPiMulEquiv`; the injectivity of a covering map on
fundamental groups is `TauCeti.IsCoveringMap.mapOfEq_injective`. The identification of the
fundamental group of the base of a simply connected quotient covering map with the opposite
of the acting group is Junyan Xu's `IsQuotientCoveringMap.fundamentalGroupEquiv` in
`Mathlib/Topology/Homotopy/Lifting.lean`. Compare Proposition 4.1 and Section 1.B of
[hatcher02]; no external formalization is copied or adapted here.
-/

public section

open TauCeti
open scoped Topology Topology.Homotopy

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {e : E} {x : X}

namespace IsCoveringMap

/-- A covering map identifies the homotopy groups of its total space in dimensions at least two
with those of its base, so one is trivial exactly when the other is. -/
theorem subsingleton_homotopyGroup_iff (hp : IsCoveringMap p) (he : p e = x) (n : ℕ) :
    Subsingleton (π_ (n + 2) E e) ↔ Subsingleton (π_ (n + 2) X x) := by
  subst he
  exact (TauCeti.IsCoveringMap.homotopyGroupPiMulEquiv hp e n).toEquiv.subsingleton_congr

/-- **The base of a surjective covering map with aspherical total space is aspherical.** -/
theorem isAspherical (hp : IsCoveringMap p) (hp' : Function.Surjective p)
    (he : p e = x) (h : IsAspherical E e) : IsAspherical X x := by
  have := h.pathConnectedSpace
  exact IsAspherical.mk (hp'.pathConnectedSpace hp.continuous)
    fun n ↦ (hp.subsingleton_homotopyGroup_iff he n).mp (h.subsingleton_homotopyGroup n)

/-- **A path-connected covering space of an aspherical space is aspherical.** -/
theorem isAspherical_totalSpace (hp : IsCoveringMap p) [PathConnectedSpace E]
    (he : p e = x) (h : IsAspherical X x) : IsAspherical E e :=
  IsAspherical.mk inferInstance
    fun n ↦ (hp.subsingleton_homotopyGroup_iff he n).mpr (h.subsingleton_homotopyGroup n)

/-- **The simply connected cover of an aspherical space is weakly contractible**: every one of
its homotopy groups in a positive dimension is trivial.

In dimension one this is simple connectedness of the cover; in the higher dimensions it is the
asphericity of the base transported along the covering map. -/
theorem subsingleton_homotopyGroup_of_isAspherical (hp : IsCoveringMap p)
    [SimplyConnectedSpace E] (he : p e = x) (h : IsAspherical X x) (n : ℕ) :
    Subsingleton (π_ (n + 1) E e) := by
  cases n with
  | zero => exact HomotopyGroup.pi1EquivFundamentalGroup.subsingleton_congr.mpr inferInstance
  | succ m =>
    exact (hp.subsingleton_homotopyGroup_iff he m).mpr (h.subsingleton_homotopyGroup m)

/-- A base covered by a path-connected space whose higher homotopy groups all vanish is
aspherical. This is the recognition principle behind `K(G, 1)` spaces: the hypothesis is on the
cover, and no homotopy group of the base has to be computed directly. -/
theorem isAspherical_of_subsingleton_homotopyGroup (hp : IsCoveringMap p)
    (hp' : Function.Surjective p) [PathConnectedSpace E] (he : p e = x)
    (h : ∀ n : ℕ, Subsingleton (π_ (n + 2) E e)) : IsAspherical X x :=
  hp.isAspherical hp' he (IsAspherical.mk inferInstance h)

/-- **A path-connected covering space of a `K(G, 1)` is a `K(H, 1)`**, for `H` the subgroup of
the fundamental group of the base that the cover recovers.

The fundamental-group witness is `MulEquiv.ofInjective` applied to the injectivity of `p` on
fundamental groups; the recovered subgroup is by definition the range of that map. -/
theorem isEilenbergMacLaneSpaceOne_totalSpace (hp : IsCoveringMap p)
    [PathConnectedSpace E] (he : p e = x) (h : IsAspherical X x) :
    IsEilenbergMacLaneSpaceOne
      (FundamentalGroup.mapOfEq (⟨p, hp.continuous⟩ : C(E, X)) he).range E e :=
  IsEilenbergMacLaneSpaceOne.mk (hp.isAspherical_totalSpace he h)
    ⟨MonoidHom.ofInjective (TauCeti.IsCoveringMap.mapOfEq_injective hp he)⟩

end IsCoveringMap

namespace IsQuotientCoveringMap

variable {G : Type*} [Group G] [MulAction G E] {f : E → X}

/-- **The orbit space of a free, properly discontinuous action of `G` on a simply connected
space all of whose higher homotopy groups vanish is a `K(G, 1)`.**

The hypotheses are packaged as a quotient covering map, which is exactly freeness together
with the local disjointness making the orbit map a covering. The fundamental group of the
orbit space is the opposite group `Gᵐᵒᵖ`, which is isomorphic to `G` by `MulEquiv.inv'`. -/
theorem isEilenbergMacLaneSpaceOne (hf : IsQuotientCoveringMap f G)
    [SimplyConnectedSpace E] (he : f e = x)
    (h : ∀ n : ℕ, Subsingleton (π_ (n + 2) E e)) :
    IsEilenbergMacLaneSpaceOne G X x :=
  IsEilenbergMacLaneSpaceOne.mk
    (hf.isCoveringMap.isAspherical_of_subsingleton_homotopyGroup hf.surjective he h)
    ⟨(hf.fundamentalGroupEquiv (⟨e, he⟩ : f ⁻¹' {x})).trans (MulEquiv.inv' G).symm⟩

end IsQuotientCoveringMap

end
