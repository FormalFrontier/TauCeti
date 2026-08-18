/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
* `TauCeti.CoveringSpace.mk`, `proj`, `homMk`, `isoMk`: constructors for covering spaces and
  their morphisms and isomorphisms.
* `TauCeti.CoveringSpace.forget`, `fullyFaithfulForget`: the inclusion into `TopCat / X` and its
  full faithfulness.
* `TauCeti.CoveringSpace.totalSpace`: the functor taking a cover to its total space.
* `TauCeti.CoveringSpace.isIso_iff_isHomeomorph_hom_left`: a map of covers is an isomorphism
  exactly when its map of total spaces is a homeomorphism.
* `TauCeti.ConnectedCoveringSpace X`: connected covering spaces over `X`.
* `TauCeti.ConnectedCoveringSpace.mk`, `proj`, `homMk`, `isoMk`: the connected-cover constructor
  API.
* `TauCeti.ConnectedCoveringSpace.forget`, `fullyFaithfulForget`: the inclusion of connected
  covers into all covers and its full faithfulness.
* `TauCeti.ConnectedCoveringSpace.isIso_iff_isHomeomorph_hom_left`: the corresponding
  isomorphism criterion for connected covers.

## References

This is the categorical packaging required by Stage 2, item 8 of
`TauCetiRoadmap/UniversalCovers/README.md`, which asks for the classification of covers by
functors from the fundamental groupoid and of connected covers by transitive fundamental-group
actions. The construction follows Mathlib's `CategoryTheory.MonoOver`: both are full
subcategories of an over category selected by a property of the structure morphism. The
`forget`, `mk`, `proj`, `homMk`, `isoMk`, and isomorphism-characterization APIs are adapted from
`Mathlib/CategoryTheory/Subobject/MonoOver.lean`, using the generic `Over` and
`ObjectProperty.FullSubcategory` constructors directly.
-/

public section

universe u

namespace TauCeti

open CategoryTheory

namespace Over

/-- The property of an object of `TopCat / X` that its structure morphism is a covering map. -/
def isCoveringMap (X : TopCat.{u}) : ObjectProperty (CategoryTheory.Over X) :=
  fun p ↦ _root_.IsCoveringMap p.hom

/-- An isomorphism in `TopCat / X` induces an isomorphism on left objects. -/
instance {X : TopCat.{u}} {p q : CategoryTheory.Over X} (f : p ⟶ q) [IsIso f] :
    IsIso f.left :=
  inferInstanceAs (IsIso ((CategoryTheory.Over.forget X).map f))

/-- A morphism in `TopCat / X` is an isomorphism exactly when its map on left objects is a
homeomorphism. -/
theorem isIso_iff_isHomeomorph_left {X : TopCat.{u}} {p q : CategoryTheory.Over X}
    (f : p ⟶ q) : IsIso f ↔ IsHomeomorph f.left := by
  rw [← TopCat.isIso_iff_isHomeomorph]
  exact (isIso_iff_of_reflects_iso _ (CategoryTheory.Over.forget X)).symm

end Over

/-- The category of covering spaces over `X`. Its objects are covering maps to `X`, and its
morphisms are continuous maps commuting with the projections to `X`. -/
abbrev CoveringSpace (X : TopCat.{u}) : Type _ :=
  (Over.isCoveringMap X).FullSubcategory

namespace CoveringSpace

variable {X : TopCat.{u}}

/-- The fully faithful inclusion of covering spaces over `X` into `TopCat / X`. -/
abbrev forget (X : TopCat.{u}) : CoveringSpace X ⥤ Over X :=
  ObjectProperty.ι _

/-- The functor taking a covering space to its total space. -/
abbrev totalSpace (X : TopCat.{u}) : CoveringSpace X ⥤ TopCat :=
  forget X ⋙ CategoryTheory.Over.forget X

/-- A covering space over `X` coerces to its total space. -/
instance : CoeOut (CoveringSpace X) TopCat where
  coe p := p.obj.left

/-- Construct a covering space over `X` from a covering map `p`. -/
def mk {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p) : CoveringSpace X where
  obj := CategoryTheory.Over.mk p
  property := hp

@[simp]
theorem mk_coe {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p) :
    (mk p hp : TopCat) = E :=
  (rfl)

/-- The projection of a covering space to its base. -/
abbrev proj (p : CoveringSpace X) : (p : TopCat) ⟶ X :=
  p.obj.hom

@[simp]
theorem forget_obj_left (p : CoveringSpace X) : ((forget X).obj p).left = (p : TopCat) :=
  rfl

theorem forget_obj_hom (p : CoveringSpace X) : ((forget X).obj p).hom = p.proj :=
  rfl

@[simp]
theorem mk_proj {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p) :
    (mk p hp).proj = eqToHom (mk_coe p hp) ≫ p :=
  (rfl)

/-- The projection from an object of `CoveringSpace X` is a covering map. -/
theorem isCoveringMap_proj (p : CoveringSpace X) : _root_.IsCoveringMap p.proj :=
  p.property

/-- The inclusion `CoveringSpace X ⥤ TopCat / X` is fully faithful. -/
def fullyFaithfulForget (X : TopCat.{u}) : (forget X).FullyFaithful :=
  ObjectProperty.fullyFaithfulι _

@[simp]
theorem totalSpace_obj (p : CoveringSpace X) : (totalSpace X).obj p = (p : TopCat) :=
  rfl

@[simp]
theorem totalSpace_map {p q : CoveringSpace X} (f : p ⟶ q) :
    (totalSpace X).map f = f.hom.left :=
  rfl

/-- A morphism of covering spaces commutes with the projections to the base. -/
@[reassoc]
theorem w {p q : CoveringSpace X} (f : p ⟶ q) : f.hom.left ≫ q.proj = p.proj :=
  CategoryTheory.Over.w _

/-- The commuting triangle of a morphism of covering spaces, as an equality of the underlying
functions. -/
theorem proj_hom_comp_hom_left_hom {p q : CoveringSpace X} (f : p ⟶ q) :
    q.proj.hom ∘ f.hom.left.hom = p.proj.hom := by
  funext e
  exact DFunLike.congr_fun (congrArg TopCat.Hom.hom (w f)) e

/-- Construct a morphism of covering spaces from a continuous map over the base. -/
def homMk {p q : CoveringSpace X} (f : (p : TopCat) ⟶ (q : TopCat))
    (w : f ≫ q.proj = p.proj := by cat_disch) : p ⟶ q :=
  ObjectProperty.homMk (CategoryTheory.Over.homMk f w)

@[simp]
theorem homMk_hom_left {p q : CoveringSpace X} (f : (p : TopCat) ⟶ (q : TopCat))
    (w : f ≫ q.proj = p.proj) : (homMk f w).hom.left = f :=
  (rfl)

/-- Construct an isomorphism of covering spaces from an isomorphism of their total spaces over
the base. -/
def isoMk {p q : CoveringSpace X} (e : (p : TopCat) ≅ (q : TopCat))
    (w : e.hom ≫ q.proj = p.proj := by cat_disch) : p ≅ q :=
  ObjectProperty.isoMk _ (CategoryTheory.Over.isoMk e w)

@[simp]
theorem isoMk_hom_hom_left {p q : CoveringSpace X} (e : (p : TopCat) ≅ (q : TopCat))
    (w : e.hom ≫ q.proj = p.proj) : (isoMk e w).hom.hom.left = e.hom :=
  (rfl)

@[simp]
theorem isoMk_inv_hom_left {p q : CoveringSpace X} (e : (p : TopCat) ≅ (q : TopCat))
    (w : e.hom ≫ q.proj = p.proj) : (isoMk e w).inv.hom.left = e.inv :=
  (rfl)

/-- Reconstructing a covering space from its projection gives an isomorphic object. -/
def mkProjIso (p : CoveringSpace X) : mk p.proj p.isCoveringMap_proj ≅ p :=
  isoMk (Iso.refl _)

@[simp]
theorem mkProjIso_hom_hom_left (p : CoveringSpace X) :
    (mkProjIso p).hom.hom.left = eqToHom (mk_coe p.proj p.isCoveringMap_proj) :=
  (rfl)

@[simp]
theorem mkProjIso_inv_hom_left (p : CoveringSpace X) :
    (mkProjIso p).inv.hom.left = eqToHom (mk_coe p.proj p.isCoveringMap_proj).symm :=
  (rfl)

/-- A map of covering spaces is an isomorphism exactly when its map of total spaces is a
homeomorphism. -/
theorem isIso_iff_isHomeomorph_hom_left {p q : CoveringSpace X} (f : p ⟶ q) :
    IsIso f ↔ IsHomeomorph f.hom.left := by
  rw [← ObjectProperty.isIso_hom_iff, Over.isIso_iff_isHomeomorph_left]

end CoveringSpace

/-- The category of connected covering spaces over `X`. -/
abbrev ConnectedCoveringSpace (X : TopCat.{u}) : Type _ :=
  (Over.isCoveringMap X ⊓ fun p ↦ ConnectedSpace p.left).FullSubcategory

namespace ConnectedCoveringSpace

variable {X : TopCat.{u}}

/-- The fully faithful inclusion of connected covering spaces into all covering spaces. -/
abbrev forget (X : TopCat.{u}) : ConnectedCoveringSpace X ⥤ CoveringSpace X :=
  ObjectProperty.ιOfLE inf_le_left

/-- The functor taking a connected covering space to its total space. -/
abbrev totalSpace (X : TopCat.{u}) : ConnectedCoveringSpace X ⥤ TopCat :=
  forget X ⋙ CoveringSpace.totalSpace X

/-- A connected covering space over `X` coerces to its total space. -/
instance : CoeOut (ConnectedCoveringSpace X) TopCat where
  coe p := p.obj.left

/-- Construct a connected covering space from a covering map with connected total space. -/
def mk {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p)
    [ConnectedSpace E] :
    ConnectedCoveringSpace X where
  obj := CategoryTheory.Over.mk p
  -- `Over.mk p` exposes `E` only at default transparency, so instance search alone cannot
  -- identify its left object with `E`.
  property := ⟨hp, by exact ‹ConnectedSpace E›⟩

@[simp]
theorem mk_coe {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p)
    [ConnectedSpace E] : (mk p hp : TopCat) = E :=
  (rfl)

/-- The projection of a connected covering space to its base. -/
abbrev proj (p : ConnectedCoveringSpace X) : (p : TopCat) ⟶ X :=
  p.obj.hom

@[simp]
theorem forget_obj_coe (p : ConnectedCoveringSpace X) :
    ((forget X).obj p : TopCat) = (p : TopCat) :=
  rfl

@[simp]
theorem forget_obj_proj (p : ConnectedCoveringSpace X) :
    ((forget X).obj p).proj = p.proj :=
  rfl

@[simp]
theorem forget_map_hom_left {p q : ConnectedCoveringSpace X} (f : p ⟶ q) :
    ((forget X).map f).hom.left = f.hom.left :=
  rfl

@[simp]
theorem forget_obj_mk {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p)
    [ConnectedSpace E] : (forget X).obj (mk p hp) = CoveringSpace.mk p hp :=
  (rfl)

@[simp]
theorem mk_proj {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p)
    [ConnectedSpace E] : (mk p hp).proj = eqToHom (mk_coe p hp) ≫ p :=
  (rfl)

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

@[simp]
theorem totalSpace_map {p q : ConnectedCoveringSpace X} (f : p ⟶ q) :
    (totalSpace X).map f = f.hom.left :=
  rfl

/-- A morphism of connected covering spaces commutes with the projections to the base. -/
@[reassoc]
theorem w {p q : ConnectedCoveringSpace X} (f : p ⟶ q) :
    f.hom.left ≫ q.proj = p.proj :=
  CategoryTheory.Over.w _

/-- Construct a morphism of connected covering spaces from a continuous map over the base. -/
def homMk {p q : ConnectedCoveringSpace X} (f : (p : TopCat) ⟶ (q : TopCat))
    (w : f ≫ q.proj = p.proj := by cat_disch) : p ⟶ q :=
  ObjectProperty.homMk (CategoryTheory.Over.homMk f w)

@[simp]
theorem homMk_hom_left {p q : ConnectedCoveringSpace X}
    (f : (p : TopCat) ⟶ (q : TopCat)) (w : f ≫ q.proj = p.proj) :
    (homMk f w).hom.left = f :=
  (rfl)

/-- Construct an isomorphism of connected covering spaces from an isomorphism of their total
spaces over the base. -/
def isoMk {p q : ConnectedCoveringSpace X} (e : (p : TopCat) ≅ (q : TopCat))
    (w : e.hom ≫ q.proj = p.proj := by cat_disch) : p ≅ q :=
  ObjectProperty.isoMk _ (CategoryTheory.Over.isoMk e w)

@[simp]
theorem isoMk_hom_hom_left {p q : ConnectedCoveringSpace X}
    (e : (p : TopCat) ≅ (q : TopCat)) (w : e.hom ≫ q.proj = p.proj) :
    (isoMk e w).hom.hom.left = e.hom :=
  (rfl)

@[simp]
theorem isoMk_inv_hom_left {p q : ConnectedCoveringSpace X}
    (e : (p : TopCat) ≅ (q : TopCat)) (w : e.hom ≫ q.proj = p.proj) :
    (isoMk e w).inv.hom.left = e.inv :=
  (rfl)

/-- Reconstructing a connected covering space from its projection gives an isomorphic object. -/
def mkProjIso (p : ConnectedCoveringSpace X) : mk p.proj p.isCoveringMap_proj ≅ p :=
  isoMk (Iso.refl _)

@[simp]
theorem mkProjIso_hom_hom_left (p : ConnectedCoveringSpace X) :
    (mkProjIso p).hom.hom.left = eqToHom (mk_coe p.proj p.isCoveringMap_proj) :=
  (rfl)

@[simp]
theorem mkProjIso_inv_hom_left (p : ConnectedCoveringSpace X) :
    (mkProjIso p).inv.hom.left = eqToHom (mk_coe p.proj p.isCoveringMap_proj).symm :=
  (rfl)

/-- A map of connected covering spaces is an isomorphism exactly when its map of total spaces is
a homeomorphism. -/
theorem isIso_iff_isHomeomorph_hom_left {p q : ConnectedCoveringSpace X} (f : p ⟶ q) :
    IsIso f ↔ IsHomeomorph f.hom.left := by
  rw [← isIso_iff_of_reflects_iso f (forget X)]
  exact CoveringSpace.isIso_iff_isHomeomorph_hom_left ((forget X).map f)

end ConnectedCoveringSpace

end TauCeti
