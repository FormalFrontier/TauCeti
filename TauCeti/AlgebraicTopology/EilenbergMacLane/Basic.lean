/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import TauCeti.AlgebraicTopology.FundamentalGroup.Product
public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Homotopy.HomotopyGroup.Product

/-!
# Aspherical spaces and Eilenberg--Mac Lane spaces of type `K(G, 1)`

A based space is aspherical when it is path-connected and all of its homotopy groups in
dimensions at least two are trivial. An Eilenberg--Mac Lane space of type `K(G, 1)` is an
aspherical space whose fundamental group is isomorphic to `G`.

The definitions are properties rather than structures carrying chosen isomorphisms. Thus they
are invariant under changing an exhibited fundamental-group isomorphism, and do not retain
noncanonical data. This file records invariance under homeomorphism and under isomorphism of
the target group, as well as closure under binary and indexed products.

The product results reuse the existing product isomorphisms for fundamental and higher
homotopy groups.

This implements the general API for `TauCetiRoadmap/UniversalCovers/README.md`, Stage 4,
item 13, "`K(G, 1)` spaces". Concrete circle and torus examples are respectively in
`TauCeti.AlgebraicTopology.UniversalCover.Circle.EilenbergMacLane` and
`TauCeti.AlgebraicTopology.UniversalCover.Torus.EilenbergMacLane`.

## Main declarations

* `TauCeti.IsAspherical`: path-connectedness together with vanishing homotopy groups in
  dimensions at least two.
* `TauCeti.IsEilenbergMacLaneSpaceOne`: the property of being an Eilenberg--Mac Lane space
  of type `K(G, 1)`.
* `TauCeti.IsAspherical.of_homeomorph`,
  `TauCeti.IsEilenbergMacLaneSpaceOne.of_homeomorph`:
  invariance under pointed homeomorphisms.
* `TauCeti.IsAspherical.prod`, `TauCeti.IsAspherical.pi`,
  `TauCeti.IsEilenbergMacLaneSpaceOne.prod`, `TauCeti.IsEilenbergMacLaneSpaceOne.pi`:
  closure under products.
-/

public section

namespace TauCeti

open scoped Topology Topology.Homotopy

noncomputable section

universe u v w w'

/-- A based space is aspherical when it is path-connected and every homotopy group in
dimension at least two is trivial. -/
def IsAspherical (X : Type u) [TopologicalSpace X] (x : X) : Prop :=
  PathConnectedSpace X ∧ ∀ n : ℕ, Subsingleton (π_ (n + 2) X x)

/-- Characteristic restatement of asphericity. -/
theorem isAspherical_iff {X : Type u} [TopologicalSpace X] {x : X} :
    IsAspherical X x ↔
      PathConnectedSpace X ∧ ∀ n : ℕ, Subsingleton (π_ (n + 2) X x) :=
  Iff.rfl

namespace IsAspherical

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Construct asphericity from path-connectedness and the vanishing of all homotopy groups
in dimensions at least two. -/
protected theorem mk (hX : PathConnectedSpace X)
    (hπ : ∀ n : ℕ, Subsingleton (π_ (n + 2) X x)) : IsAspherical X x :=
  ⟨hX, hπ⟩

/-- An aspherical space is path-connected. -/
protected theorem pathConnectedSpace (h : IsAspherical X x) : PathConnectedSpace X :=
  h.1

/-- Every homotopy group of an aspherical space in dimension at least two is trivial. -/
protected theorem subsingleton_homotopyGroup (h : IsAspherical X x) (n : ℕ) :
    Subsingleton (π_ (n + 2) X x) :=
  h.2 n

/-- Asphericity is preserved by a pointed homeomorphism. -/
theorem of_homeomorph (hX : IsAspherical X x) (e : X ≃ₜ Y) (he : e x = y) :
    IsAspherical Y y := by
  letI : PathConnectedSpace X := hX.pathConnectedSpace
  refine ⟨e.surjective.pathConnectedSpace e.continuous, fun n ↦ ?_⟩
  letI : Subsingleton (π_ (n + 2) X x) := hX.subsingleton_homotopyGroup n
  exact
    (HomotopyGroup.homeomorphMulEquivOfEq (N := Fin (n + 2)) e he).toEquiv
      |>.subsingleton_congr.mp inferInstance

/-- The product of two aspherical spaces is aspherical. -/
theorem prod (hX : IsAspherical X x) (hY : IsAspherical Y y) :
    IsAspherical (X × Y) (x, y) := by
  letI : PathConnectedSpace X := hX.pathConnectedSpace
  letI : PathConnectedSpace Y := hY.pathConnectedSpace
  refine ⟨inferInstance, fun n ↦ ?_⟩
  letI : Subsingleton (π_ (n + 2) X x) := hX.subsingleton_homotopyGroup n
  letI : Subsingleton (π_ (n + 2) Y y) := hY.subsingleton_homotopyGroup n
  exact
    (HomotopyGroup.prodEquiv (N := Fin (n + 2)) x y).subsingleton_congr.mpr inferInstance

variable {ι : Type w} {Z : ι → Type u} [∀ i, TopologicalSpace (Z i)] {z : ∀ i, Z i}

/-- An indexed product of aspherical spaces is aspherical. -/
theorem pi (h : ∀ i, IsAspherical (Z i) (z i)) :
    IsAspherical (∀ i, Z i) z := by
  letI : ∀ i, PathConnectedSpace (Z i) := fun i ↦ (h i).pathConnectedSpace
  refine ⟨inferInstance, fun n ↦ ?_⟩
  letI : ∀ i, Subsingleton (π_ (n + 2) (Z i) (z i)) :=
    fun i ↦ (h i).subsingleton_homotopyGroup n
  exact inferInstance

end IsAspherical

/-- A based space is an Eilenberg--Mac Lane space of type `K(G, 1)` when it is aspherical
and its fundamental group is isomorphic to `G`. -/
def IsEilenbergMacLaneSpaceOne (G : Type u) [Group G]
    (X : Type v) [TopologicalSpace X] (x : X) : Prop :=
  IsAspherical X x ∧ Nonempty (FundamentalGroup X x ≃* G)

/-- Characteristic restatement of the `K(G, 1)` property. -/
theorem isEilenbergMacLaneSpaceOne_iff {G : Type u} [Group G]
    {X : Type v} [TopologicalSpace X] {x : X} :
    IsEilenbergMacLaneSpaceOne G X x ↔
      IsAspherical X x ∧ Nonempty (FundamentalGroup X x ≃* G) :=
  Iff.rfl

namespace IsEilenbergMacLaneSpaceOne

variable {G : Type u} {H : Type v} [Group G] [Group H]
  {X : Type w} {Y : Type w'} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Construct the `K(G, 1)` property from asphericity and an isomorphism between the
fundamental group and `G`. -/
protected theorem mk (hX : IsAspherical X x) (hπ : Nonempty (FundamentalGroup X x ≃* G)) :
    IsEilenbergMacLaneSpaceOne G X x :=
  ⟨hX, hπ⟩

/-- A `K(G, 1)` space is aspherical. -/
protected theorem isAspherical (h : IsEilenbergMacLaneSpaceOne G X x) :
    IsAspherical X x :=
  h.1

/-- The fundamental group of a `K(G, 1)` space is isomorphic to `G`. -/
protected theorem nonempty_fundamentalGroupMulEquiv (h : IsEilenbergMacLaneSpaceOne G X x) :
    Nonempty (FundamentalGroup X x ≃* G) :=
  h.2

/-- Transporting the target group along an isomorphism preserves the `K(G, 1)` property. -/
theorem of_mulEquiv (h : IsEilenbergMacLaneSpaceOne G X x) (e : G ≃* H) :
    IsEilenbergMacLaneSpaceOne H X x :=
  ⟨h.isAspherical, h.nonempty_fundamentalGroupMulEquiv.map fun f ↦ f.trans e⟩

/-- The `K(G, 1)` property is preserved by a pointed homeomorphism. -/
theorem of_homeomorph (h : IsEilenbergMacLaneSpaceOne G X x) (e : X ≃ₜ Y) (he : e x = y) :
    IsEilenbergMacLaneSpaceOne G Y y :=
  ⟨h.isAspherical.of_homeomorph e he,
    h.nonempty_fundamentalGroupMulEquiv.map fun f ↦
      (FundamentalGroup.homeomorphMulEquivOfEq e he).symm.trans f⟩

variable {G₁ : Type u} {G₂ : Type v} [Group G₁] [Group G₂]
  {X₁ : Type w} {X₂ : Type w'} [TopologicalSpace X₁] [TopologicalSpace X₂]
  {x₁ : X₁} {x₂ : X₂}

/-- The product of a `K(G₁, 1)` space and a `K(G₂, 1)` space is a
`K(G₁ × G₂, 1)` space. -/
theorem prod (h₁ : IsEilenbergMacLaneSpaceOne G₁ X₁ x₁) (h₂ : IsEilenbergMacLaneSpaceOne G₂ X₂ x₂) :
    IsEilenbergMacLaneSpaceOne (G₁ × G₂) (X₁ × X₂) (x₁, x₂) := by
  refine ⟨h₁.isAspherical.prod h₂.isAspherical, ?_⟩
  obtain ⟨e₁⟩ := h₁.nonempty_fundamentalGroupMulEquiv
  obtain ⟨e₂⟩ := h₂.nonempty_fundamentalGroupMulEquiv
  exact ⟨(FundamentalGroup.prodMulEquiv x₁ x₂).trans (e₁.prodCongr e₂)⟩

variable {ι : Type w} {G' : ι → Type u} {Z : ι → Type v}
  [∀ i, Group (G' i)] [∀ i, TopologicalSpace (Z i)] {z : ∀ i, Z i}

/-- An indexed product of `K(Gᵢ, 1)` spaces is a `K(Π i, Gᵢ, 1)` space. -/
theorem pi (h : ∀ i, IsEilenbergMacLaneSpaceOne (G' i) (Z i) (z i)) :
    IsEilenbergMacLaneSpaceOne (∀ i, G' i) (∀ i, Z i) z := by
  refine ⟨IsAspherical.pi fun i ↦ (h i).isAspherical, ?_⟩
  exact ⟨(FundamentalGroup.piMulEquiv z).trans
    (MulEquiv.piCongrRight fun i ↦ Classical.choice (h i).nonempty_fundamentalGroupMulEquiv)⟩

end IsEilenbergMacLaneSpaceOne

end

end TauCeti
