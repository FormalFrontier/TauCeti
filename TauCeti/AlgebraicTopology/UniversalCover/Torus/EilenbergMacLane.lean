/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.EilenbergMacLane

/-!
# Tori as Eilenberg--Mac Lane spaces

An arbitrary indexed product of real additive circles with nonzero periods is a
`K(Π i, ℤ, 1)`.

These results derive directly from the Eilenberg--Mac Lane product API and the circle
calculation in `TauCeti.AlgebraicTopology.UniversalCover.Circle.EilenbergMacLane`.

This realizes `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13,
"`K(G, 1)` spaces", for arbitrary products of circles.

## Main declarations

* `TauCeti.AddCircle.isAspherical_pi`: an indexed product of real circles is aspherical.
* `TauCeti.AddCircle.isEilenbergMacLaneSpaceOne_pi`: an indexed product of nondegenerate
  real circles is a `K(Π i, ℤ, 1)`.
-/

public section

namespace TauCeti

open scoped Topology Topology.Homotopy

noncomputable section

namespace AddCircle

variable {ι : Type*}

/-- Every indexed product of real additive circles is aspherical. -/
theorem isAspherical_pi (p : ι → ℝ) (x : ∀ i, AddCircle (p i)) :
    TauCeti.IsAspherical (∀ i, AddCircle (p i)) x :=
  TauCeti.IsAspherical.pi fun i ↦ isAspherical (p i) (x i)

/-- An indexed product of real additive circles with nonzero periods is an Eilenberg--Mac
Lane space of type `K(Π i, ℤ, 1)`. No finiteness assumption on the index type is needed. -/
theorem isEilenbergMacLaneSpaceOne_pi (p : ι → ℝ) (hp : ∀ i, p i ≠ 0) (x : ∀ i, AddCircle (p i)) :
    TauCeti.IsEilenbergMacLaneSpaceOne (∀ _ : ι, Multiplicative ℤ)
      (∀ i, AddCircle (p i)) x :=
  TauCeti.IsEilenbergMacLaneSpaceOne.pi fun i ↦
    isEilenbergMacLaneSpaceOne (p i) (hp i) (x i)

end AddCircle

end

end TauCeti
