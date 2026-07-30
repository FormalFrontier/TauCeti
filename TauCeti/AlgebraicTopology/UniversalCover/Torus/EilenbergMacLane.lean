/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.Torus.FundamentalGroup
public import TauCeti.AlgebraicTopology.UniversalCover.Torus.HigherHomotopy

/-!
# Circles and tori as Eilenberg--Mac Lane spaces

A real additive circle of nonzero period is a `K(ℤ, 1)`: it is path-connected, its
fundamental group is infinite cyclic, and all its higher homotopy groups vanish. More
generally, an arbitrary indexed product of such circles is a `K(Π i, ℤ, 1)`.

These results package the existing circle and torus calculations into the Eilenberg--Mac Lane
API. The fundamental-group witnesses are
`TauCeti.AddCircle.fundamentalGroupMulEquiv` and
`TauCeti.AddCircle.piFundamentalGroupMulEquiv`; higher homotopy vanishing is supplied by
`TauCeti.AddCircle.subsingleton_homotopyGroup` and
`TauCeti.AddCircle.subsingleton_homotopyGroup_pi`.

This realizes `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4, item 13,
"`K(G, 1)` spaces", for circles and arbitrary products of circles.

## Main declarations

* `TauCeti.AddCircle.isEilenbergMacLaneSpaceOne`: a nondegenerate real circle is a
  `K(ℤ, 1)`.
* `TauCeti.AddCircle.isEilenbergMacLaneSpaceOne_pi`: an indexed product of nondegenerate
  real circles is a `K(Π i, ℤ, 1)`.
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
  isAspherical_iff.mpr ⟨inferInstance, fun _ ↦ inferInstance⟩

/-- A real additive circle with nonzero period is an Eilenberg--Mac Lane space of type
`K(ℤ, 1)`, with `ℤ` written multiplicatively to match the fundamental group. -/
theorem isEilenbergMacLaneSpaceOne (p : ℝ) (hp : p ≠ 0) (x : AddCircle p) :
    TauCeti.IsEilenbergMacLaneSpaceOne (Multiplicative ℤ) (AddCircle p) x := by
  obtain ⟨e, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact isEilenbergMacLaneSpaceOne_iff.mpr
    ⟨isAspherical p _, ⟨fundamentalGroupMulEquiv p hp ⟨e, rfl⟩⟩⟩

variable {ι : Type*}

/-- Every indexed product of real additive circles is aspherical. -/
theorem isAspherical_pi (p : ι → ℝ) (x : ∀ i, AddCircle (p i)) :
    TauCeti.IsAspherical (∀ i, AddCircle (p i)) x :=
  isAspherical_iff.mpr ⟨inferInstance, fun _ ↦ inferInstance⟩

/-- An indexed product of real additive circles with nonzero periods is an Eilenberg--Mac
Lane space of type `K(Π i, ℤ, 1)`. No finiteness assumption on the index type is needed. -/
theorem isEilenbergMacLaneSpaceOne_pi (p : ι → ℝ) (hp : ∀ i, p i ≠ 0)
    (x : ∀ i, AddCircle (p i)) :
    TauCeti.IsEilenbergMacLaneSpaceOne (∀ _ : ι, Multiplicative ℤ)
      (∀ i, AddCircle (p i)) x := by
  choose e he using fun i ↦ QuotientAddGroup.mk_surjective (x i)
  let lift : ∀ i, ((↑) : ℝ → AddCircle (p i)) ⁻¹' {x i} :=
    fun i ↦ ⟨e i, by simpa using he i⟩
  exact isEilenbergMacLaneSpaceOne_iff.mpr
    ⟨isAspherical_pi p x, ⟨piFundamentalGroupMulEquiv hp lift⟩⟩

end AddCircle

end

end TauCeti
