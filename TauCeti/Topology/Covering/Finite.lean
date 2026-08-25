/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.Category
public import TauCeti.Topology.Homotopy.Monodromy.Basic

/-!
# Finite covering spaces

A covering space is *finite* when all of its fibres are finite. This file records that condition
as a property of an object of `TopCat / X`, names the resulting full subcategory
`TauCeti.FiniteCoveringSpace X`, and gives it the same constructor API that
`TauCeti.CoveringSpace` and `TauCeti.ConnectedCoveringSpace` carry.

Finiteness of all fibres is one condition rather than infinitely many as soon as the base is path
connected: monodromy along a path is a bijection between the fibres over its endpoints, so the
fibres over any two points of a path component are in bijection. That is
`TauCeti.coveringFiberEquiv`, from `TauCeti.Topology.Homotopy.Monodromy.Basic`, and
`TauCeti.hasFiniteFibers_of_finite_fiber` is the resulting one-point criterion.

Finite covers are the covering-space side of the Galois-category picture: the fibre over a
basepoint is a finite set with an action of `π₁`, and it is only for finite covers that the fibre
functor lands in `FintypeCat`.

## Main declarations

* `TauCeti.Over.hasFiniteFibers` and `TauCeti.Over.hasFiniteFibers_iff`: the property of an
  object of `TopCat / X` that all fibres of its structure morphism are finite, and its
  membership lemma.
* `TauCeti.FiniteCoveringSpace`: finite covering spaces over `X`.
* `TauCeti.FiniteCoveringSpace.mk`, `proj`, `homMk`, `isoMk`, `forget`,
  `fullyFaithfulForget`, `isIso_iff_isHomeomorph_hom_left`: the constructor API.
* `TauCeti.hasFiniteFibers_of_finite_fiber`: over a path-connected base, one finite fibre makes
  all fibres finite.
-/

public section

universe u v

namespace TauCeti

open CategoryTheory

section Fibers

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- Over a path-connected base, a covering map with one finite fibre has all fibres finite. -/
theorem finite_fiber_of_finite_fiber [PathConnectedSpace X] (hp : IsCoveringMap p) {x₀ : X}
    (h : Finite ↥(p ⁻¹' {x₀})) (x : X) : Finite ↥(p ⁻¹' {x}) :=
  have := h
  Finite.of_equiv _
    (coveringFiberEquiv hp (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)))

end Fibers

namespace Over

/-- The property of an object of `TopCat / X` that all fibres of its structure morphism are
finite. -/
def hasFiniteFibers (X : TopCat.{u}) : ObjectProperty (CategoryTheory.Over X) :=
  fun p => ∀ x : X, Finite ↥(⇑p.hom ⁻¹' {x})

/-- Membership in the finite-fibre property of objects of `TopCat / X`. -/
@[simp]
theorem hasFiniteFibers_iff {X : TopCat.{u}} {p : CategoryTheory.Over X} :
    hasFiniteFibers X p ↔ ∀ x : X, Finite ↥(⇑p.hom ⁻¹' {x}) :=
  Iff.rfl

end Over

/-- The category of finite covering spaces over `X`: covering maps to `X` all of whose fibres are
finite, and continuous maps commuting with the projections to `X`. -/
abbrev FiniteCoveringSpace (X : TopCat.{u}) : Type _ :=
  (Over.isCoveringMap X ⊓ Over.hasFiniteFibers X).FullSubcategory

namespace FiniteCoveringSpace

variable {X : TopCat.{u}}

/-- The fully faithful inclusion of finite covering spaces into all covering spaces. -/
abbrev forget (X : TopCat.{u}) : FiniteCoveringSpace X ⥤ CoveringSpace X :=
  ObjectProperty.ιOfLE inf_le_left

/-- The functor taking a finite covering space to its total space. -/
abbrev totalSpace (X : TopCat.{u}) : FiniteCoveringSpace X ⥤ TopCat :=
  forget X ⋙ CoveringSpace.totalSpace X

/-- A finite covering space over `X` coerces to its total space. -/
instance : CoeOut (FiniteCoveringSpace X) TopCat where
  coe p := p.obj.left

/-- Construct a finite covering space from a covering map with finite fibres. -/
def mk {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p)
    (hfin : ∀ x : X, Finite ↥(⇑p ⁻¹' {x})) : FiniteCoveringSpace X where
  obj := CategoryTheory.Over.mk p
  property := ⟨Over.isCoveringMap_iff.2 hp, Over.hasFiniteFibers_iff.2 hfin⟩

@[simp]
theorem mk_coe {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p)
    (hfin : ∀ x : X, Finite ↥(⇑p ⁻¹' {x})) : (mk p hp hfin : TopCat) = E :=
  (rfl)

/-- The projection of a finite covering space to its base. -/
abbrev proj (p : FiniteCoveringSpace X) : (p : TopCat) ⟶ X :=
  p.obj.hom

@[simp]
theorem forget_obj_coe (p : FiniteCoveringSpace X) :
    ((forget X).obj p : TopCat) = (p : TopCat) :=
  rfl

@[simp]
theorem forget_obj_proj (p : FiniteCoveringSpace X) : ((forget X).obj p).proj = p.proj :=
  rfl

@[simp]
theorem forget_map_hom_left {p q : FiniteCoveringSpace X} (f : p ⟶ q) :
    ((forget X).map f).hom.left = f.hom.left :=
  rfl

@[simp]
theorem mk_proj {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p)
    (hfin : ∀ x : X, Finite ↥(⇑p ⁻¹' {x})) :
    (mk p hp hfin).proj = eqToHom (mk_coe p hp hfin) ≫ p :=
  (rfl)

/-- The projection from an object of `FiniteCoveringSpace X` is a covering map. -/
theorem isCoveringMap_proj (p : FiniteCoveringSpace X) : _root_.IsCoveringMap p.proj :=
  Over.isCoveringMap_iff.1 p.property.1

/-- Every fibre of a finite covering space is finite. -/
instance finite_fiber (p : FiniteCoveringSpace X) (x : X) : Finite ↥(⇑p.proj ⁻¹' {x}) :=
  Over.hasFiniteFibers_iff.1 p.property.2 x

/-- The inclusion `FiniteCoveringSpace X ⥤ CoveringSpace X` is fully faithful. -/
def fullyFaithfulForget (X : TopCat.{u}) : (forget X).FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE _

@[simp]
theorem totalSpace_obj (p : FiniteCoveringSpace X) : (totalSpace X).obj p = (p : TopCat) :=
  rfl

@[simp]
theorem totalSpace_map {p q : FiniteCoveringSpace X} (f : p ⟶ q) :
    (totalSpace X).map f = f.hom.left :=
  rfl

/-- A morphism of finite covering spaces commutes with the projections to the base. -/
@[reassoc]
theorem w {p q : FiniteCoveringSpace X} (f : p ⟶ q) : f.hom.left ≫ q.proj = p.proj :=
  CategoryTheory.Over.w _

/-- Construct a morphism of finite covering spaces from a continuous map over the base. -/
def homMk {p q : FiniteCoveringSpace X} (f : (p : TopCat) ⟶ (q : TopCat))
    (w : f ≫ q.proj = p.proj := by cat_disch) : p ⟶ q :=
  ObjectProperty.homMk (CategoryTheory.Over.homMk f w)

@[simp]
theorem homMk_hom_left {p q : FiniteCoveringSpace X} (f : (p : TopCat) ⟶ (q : TopCat))
    (w : f ≫ q.proj = p.proj) : (homMk f w).hom.left = f :=
  (rfl)

/-- Construct an isomorphism of finite covering spaces from an isomorphism of their total spaces
over the base. -/
def isoMk {p q : FiniteCoveringSpace X} (e : (p : TopCat) ≅ (q : TopCat))
    (w : e.hom ≫ q.proj = p.proj := by cat_disch) : p ≅ q :=
  ObjectProperty.isoMk _ (CategoryTheory.Over.isoMk e w)

@[simp]
theorem isoMk_hom_hom_left {p q : FiniteCoveringSpace X} (e : (p : TopCat) ≅ (q : TopCat))
    (w : e.hom ≫ q.proj = p.proj) : (isoMk e w).hom.hom.left = e.hom :=
  (rfl)

@[simp]
theorem isoMk_inv_hom_left {p q : FiniteCoveringSpace X} (e : (p : TopCat) ≅ (q : TopCat))
    (w : e.hom ≫ q.proj = p.proj) : (isoMk e w).inv.hom.left = e.inv :=
  (rfl)

/-- A map of finite covering spaces is an isomorphism exactly when its map of total spaces is a
homeomorphism. -/
theorem isIso_iff_isHomeomorph_hom_left {p q : FiniteCoveringSpace X} (f : p ⟶ q) :
    IsIso f ↔ IsHomeomorph f.hom.left := by
  rw [← isIso_iff_of_reflects_iso f (forget X)]
  exact CoveringSpace.isIso_iff_isHomeomorph_hom_left ((forget X).map f)

end FiniteCoveringSpace

/-- **Over a path-connected base one finite fibre makes a covering space finite.** -/
theorem hasFiniteFibers_of_finite_fiber {X : TopCat.{u}} [PathConnectedSpace X]
    (p : CoveringSpace X) (x₀ : X) (h : Finite ↥(⇑p.proj ⁻¹' {x₀})) :
    Over.hasFiniteFibers X p.obj :=
  Over.hasFiniteFibers_iff.2 fun x => finite_fiber_of_finite_fiber p.isCoveringMap_proj h x

end TauCeti
