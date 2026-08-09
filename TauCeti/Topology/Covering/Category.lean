/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Covering.Basic

/-!
# The category of covering spaces over a fixed base

For a topological space `X`, this file defines `TauCeti.CoveringSpace X`, whose objects are
covering maps to `X` and whose morphisms are continuous maps over `X`. It is constructed as the
full subcategory of `TopCat / X` cut out by `IsCoveringMap`, so its category structure and the
commuting triangle carried by every morphism come from Mathlib's `Over` and
`ObjectProperty.FullSubcategory` APIs.

The full subcategory `TauCeti.ConnectedCoveringSpace X` consists of the covers with connected
total space. This is the source category for the connected-cover classification by transitive
fundamental-group actions.

## Main declarations

* `TauCeti.CoveringSpace X`: covering spaces over `X` and maps over `X`.
* `TauCeti.CoveringSpace.mk`: construct a covering space from a covering map.
* `TauCeti.CoveringSpace.totalSpace`: the functor taking a cover to its total space.
* `TauCeti.ConnectedCoveringSpace X`: connected covering spaces over `X`.
* `TauCeti.ConnectedCoveringSpace.forget`: the fully faithful inclusion of connected covers into
  all covers.

## References

This is the categorical packaging required by Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`, which asks for the classification of covers by
functors from the fundamental groupoid and of connected covers by transitive fundamental-group
actions. The construction follows Mathlib's `CategoryTheory.MonoOver`: both are full
subcategories of an over category selected by a property of the structure morphism. No Mathlib
proof is vendored.
-/

public section

universe u

namespace TauCeti

open CategoryTheory

/-- The category of covering spaces over `X`. Its objects are covering maps to `X`, and its
morphisms are continuous maps commuting with the projections to `X`. -/
abbrev CoveringSpace (X : TopCat.{u}) :=
  ObjectProperty.FullSubcategory fun p : Over X ↦ _root_.IsCoveringMap p.hom

namespace CoveringSpace

variable {X : TopCat.{u}}

/-- The fully faithful inclusion of covering spaces over `X` into `TopCat / X`. -/
abbrev forget (X : TopCat.{u}) : CoveringSpace X ⥤ Over X :=
  ObjectProperty.ι _

/-- The functor taking a covering space to its total space. -/
abbrev totalSpace (X : TopCat.{u}) : CoveringSpace X ⥤ TopCat :=
  forget X ⋙ Over.forget X

instance : CoeOut (CoveringSpace X) TopCat where
  coe p := p.obj.left

/-- Construct a covering space over `X` from a covering map `p`. -/
abbrev mk {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p) : CoveringSpace X where
  obj := Over.mk p
  property := hp

@[simp]
theorem mk_coe {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p) :
    (mk p hp : TopCat) = E :=
  rfl

/-- The projection of a covering space to its base. -/
abbrev proj (p : CoveringSpace X) : (p : TopCat) ⟶ X :=
  p.obj.hom

@[simp]
theorem mk_proj {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p) :
    (mk p hp).proj = p :=
  rfl

/-- The projection from an object of `CoveringSpace X` is a covering map. -/
theorem isCoveringMap_proj (p : CoveringSpace X) : _root_.IsCoveringMap p.proj :=
  p.property

/-- The inclusion `CoveringSpace X ⥤ TopCat / X` is fully faithful. -/
def fullyFaithfulForget (X : TopCat.{u}) : (forget X).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

@[simp]
theorem totalSpace_obj (p : CoveringSpace X) : (totalSpace X).obj p = (p : TopCat) :=
  rfl

/-- Every map of covering spaces commutes with the projections to the base. -/
@[reassoc]
theorem w {p q : CoveringSpace X} (f : p ⟶ q) : f.hom.left ≫ q.proj = p.proj :=
  Over.w _

/-- Construct a morphism of covering spaces from a continuous map over the base. -/
abbrev homMk {p q : CoveringSpace X} (f : (p : TopCat) ⟶ (q : TopCat))
    (w : f ≫ q.proj = p.proj := by aesop_cat) : p ⟶ q :=
  InducedCategory.homMk (Over.homMk f w)

@[simp]
theorem homMk_hom_left {p q : CoveringSpace X} (f : (p : TopCat) ⟶ (q : TopCat))
    (w : f ≫ q.proj = p.proj) : (homMk f w).hom.left = f :=
  rfl

/-- Construct an isomorphism of covering spaces from an isomorphism of their total spaces over
the base. -/
def isoMk {p q : CoveringSpace X} (e : (p : TopCat) ≅ (q : TopCat))
    (w : e.hom ≫ q.proj = p.proj := by aesop_cat) : p ≅ q where
  hom := homMk e.hom w
  inv := homMk e.inv (by rw [e.inv_comp_eq, w])

/-- Reconstructing a covering space from its projection gives an isomorphic object. -/
def mkProjIso (p : CoveringSpace X) : mk p.proj p.isCoveringMap_proj ≅ p :=
  isoMk (Iso.refl _)

instance {p q : CoveringSpace X} (f : p ⟶ q) [IsIso f] : IsIso f.hom.left :=
  inferInstanceAs (IsIso ((forget X ⋙ Over.forget X).map f))

/-- A map of covering spaces is an isomorphism exactly when its map of total spaces is a
homeomorphism. -/
theorem isIso_iff_isHomeomorph {p q : CoveringSpace X} (f : p ⟶ q) :
    IsIso f ↔ IsHomeomorph f.hom.left := by
  rw [← TopCat.isIso_iff_isHomeomorph]
  exact (isIso_iff_of_reflects_iso _ (forget X ⋙ Over.forget X)).symm

end CoveringSpace

/-- The category of connected covering spaces over `X`. -/
abbrev ConnectedCoveringSpace (X : TopCat.{u}) :=
  ObjectProperty.FullSubcategory fun p : Over X ↦
    _root_.IsCoveringMap p.hom ∧ ConnectedSpace p.left

namespace ConnectedCoveringSpace

variable {X : TopCat.{u}}

/-- The fully faithful inclusion of connected covering spaces into all covering spaces. -/
abbrev forget (X : TopCat.{u}) : ConnectedCoveringSpace X ⥤ CoveringSpace X :=
  ObjectProperty.ιOfLE fun _ hp ↦ hp.1

/-- The functor taking a connected covering space to its total space. -/
abbrev totalSpace (X : TopCat.{u}) : ConnectedCoveringSpace X ⥤ TopCat :=
  forget X ⋙ CoveringSpace.totalSpace X

instance : CoeOut (ConnectedCoveringSpace X) TopCat where
  coe p := p.obj.left

/-- Construct a connected covering space from a covering map with connected total space. -/
abbrev mk {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p) [ConnectedSpace E] :
    ConnectedCoveringSpace X where
  obj := Over.mk p
  property := ⟨hp, by exact ‹ConnectedSpace E›⟩

@[simp]
theorem mk_coe {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p)
    [ConnectedSpace E] : (mk p hp : TopCat) = E :=
  rfl

/-- The projection of a connected covering space to its base. -/
abbrev proj (p : ConnectedCoveringSpace X) : (p : TopCat) ⟶ X :=
  p.obj.hom

@[simp]
theorem mk_proj {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p)
    [ConnectedSpace E] : (mk p hp).proj = p :=
  rfl

/-- The total space of a connected covering space is connected. -/
instance connectedSpace (p : ConnectedCoveringSpace X) : ConnectedSpace (p : TopCat) :=
  p.property.2

/-- The projection from an object of `ConnectedCoveringSpace X` is a covering map. -/
theorem isCoveringMap_proj (p : ConnectedCoveringSpace X) : _root_.IsCoveringMap p.proj :=
  p.property.1

/-- The inclusion `ConnectedCoveringSpace X ⥤ CoveringSpace X` is fully faithful. -/
def fullyFaithfulForget (X : TopCat.{u}) : (forget X).FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE _

@[simp]
theorem totalSpace_obj (p : ConnectedCoveringSpace X) :
    (totalSpace X).obj p = (p : TopCat) :=
  rfl

/-- Every map of connected covering spaces commutes with the projections to the base. -/
@[reassoc]
theorem w {p q : ConnectedCoveringSpace X} (f : p ⟶ q) :
    f.hom.left ≫ q.proj = p.proj :=
  Over.w _

/-- Construct a morphism of connected covering spaces from a continuous map over the base. -/
abbrev homMk {p q : ConnectedCoveringSpace X} (f : (p : TopCat) ⟶ (q : TopCat))
    (w : f ≫ q.proj = p.proj := by aesop_cat) : p ⟶ q :=
  InducedCategory.homMk (Over.homMk f w)

@[simp]
theorem homMk_hom_left {p q : ConnectedCoveringSpace X}
    (f : (p : TopCat) ⟶ (q : TopCat)) (w : f ≫ q.proj = p.proj) :
    (homMk f w).hom.left = f :=
  rfl

/-- Construct an isomorphism of connected covering spaces from an isomorphism of their total
spaces over the base. -/
def isoMk {p q : ConnectedCoveringSpace X} (e : (p : TopCat) ≅ (q : TopCat))
    (w : e.hom ≫ q.proj = p.proj := by aesop_cat) : p ≅ q where
  hom := homMk e.hom w
  inv := homMk e.inv (by rw [e.inv_comp_eq, w])

/-- Reconstructing a connected covering space from its projection gives an isomorphic object. -/
def mkProjIso (p : ConnectedCoveringSpace X) : mk p.proj p.isCoveringMap_proj ≅ p :=
  isoMk (Iso.refl _)

instance {p q : ConnectedCoveringSpace X} (f : p ⟶ q) [IsIso f] :
    IsIso f.hom.left :=
  inferInstanceAs (IsIso ((forget X ⋙ CoveringSpace.totalSpace X).map f))

/-- A map of connected covering spaces is an isomorphism exactly when its map of total spaces is
a homeomorphism. -/
theorem isIso_iff_isHomeomorph {p q : ConnectedCoveringSpace X} (f : p ⟶ q) :
    IsIso f ↔ IsHomeomorph f.hom.left := by
  rw [← TopCat.isIso_iff_isHomeomorph]
  exact (isIso_iff_of_reflects_iso _ (forget X ⋙ CoveringSpace.totalSpace X)).symm

end ConnectedCoveringSpace

end TauCeti
