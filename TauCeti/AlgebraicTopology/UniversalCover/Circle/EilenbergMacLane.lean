/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup
public import TauCeti.AlgebraicTopology.UniversalCover.Circle.HigherHomotopy

/-!
# Circles as Eilenberg--Mac Lane spaces

A real additive circle of nonzero period is a `K(ℤ, 1)`: it is path-connected, its
fundamental group is infinite cyclic, and all its higher homotopy groups vanish.

These results package the existing circle calculations into the Eilenberg--Mac Lane API. The
fundamental-group witness is `TauCeti.AddCircle.fundamentalGroupMulEquiv`, and higher homotopy
vanishing is supplied by `TauCeti.AddCircle.subsingleton_homotopyGroup`.

This realizes `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13,
"`K(G, 1)` spaces", for circles.

## Main declarations

* `TauCeti.AddCircle.isAspherical`: every real additive circle is aspherical.
* `TauCeti.AddCircle.isEilenbergMacLaneSpaceOne`: a nondegenerate real circle is a
  `K(ℤ, 1)`.
-/

public section

namespace TauCeti

open scoped Topology Topology.Homotopy

noncomputable section

namespace AddCircle

/-- Every real additive circle is aspherical. The nonzero-period hypothesis is needed only
for the later identification of its fundamental group with `ℤ`. -/
theorem isAspherical (p : ℝ) (x : AddCircle p) :
    TauCeti.IsAspherical (AddCircle p) x :=
  TauCeti.IsAspherical.mk inferInstance fun _ ↦ inferInstance

/-- A real additive circle with nonzero period is an Eilenberg--Mac Lane space of type
`K(ℤ, 1)`, with `ℤ` written multiplicatively to match the fundamental group. -/
theorem isEilenbergMacLaneSpaceOne (p : ℝ) (hp : p ≠ 0) (x : AddCircle p) :
    TauCeti.IsEilenbergMacLaneSpaceOne (Multiplicative ℤ) (AddCircle p) x := by
  obtain ⟨e, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact TauCeti.IsEilenbergMacLaneSpaceOne.mk
    (isAspherical p _) ⟨fundamentalGroupMulEquiv p hp ⟨e, rfl⟩⟩

end AddCircle

end

end TauCeti
