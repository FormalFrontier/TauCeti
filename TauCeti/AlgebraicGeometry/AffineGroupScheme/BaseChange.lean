/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicGeometry.AffineGroupScheme.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# Base change of affine group schemes

Pullback along `Spec S ⟶ Spec R` carries an affine group scheme over `Spec R` to an affine
group scheme over `Spec S`. This file bundles that construction on objects and morphisms as
`TauCeti.AffineGroupSchemeCat.baseChangeFunctor`.

The group structure is transported by Mathlib's left-exact pullback functor on `Over` categories.
Affineness is preserved because the fibre product of two affine schemes over an arbitrary scheme
is affine. Thus the construction applies over general commutative rings; no field or finite-type
hypothesis is needed.

## Main declarations

* `TauCeti.AffineGroupSchemeCat.baseChange`: base change of one affine group scheme.
* `TauCeti.AffineGroupSchemeCat.baseChangeMap`: base change of a morphism.
* `TauCeti.AffineGroupSchemeCat.baseChangeFunctor`: functorial base change.

## Roadmap

This supplies the scheme-side base-change operation required by Layer 9 of the ReductiveGroups
roadmap. The CFSGStatement roadmap's milestone L0 uses it to evaluate a pinned
Chevalley--Demazure group scheme over `ℤ` after extension to an algebraic closure of a finite
prime field.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

universe u

namespace AffineGroupSchemeCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Base change of an affine group scheme along a ring homomorphism `R → S`.

Its underlying scheme is the fibre product with `Spec S` over `Spec R`, and its group-object
structure is the one transported by pullback. -/
noncomputable abbrev baseChange (f : R →+* S)
    (G : AffineGroupSchemeCat (CommRingCat.of R)) :
    AffineGroupSchemeCat (CommRingCat.of S) :=
  ⟨(Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj G.obj, by
    rw [affineGroupSchemeProperty_iff]
    change IsAffine (Limits.pullback G.obj.X.hom (Spec.map (CommRingCat.ofHom f)))
    infer_instance⟩

/-- The underlying group object of a base-changed affine group scheme is obtained by applying
pullback to the original group object. -/
@[simp]
lemma baseChange_obj (f : R →+* S) (G : AffineGroupSchemeCat (CommRingCat.of R)) :
    (baseChange f G).obj =
      (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.obj G.obj :=
  (rfl)

/-- The underlying object over `Spec S` of a base-changed affine group scheme is the pullback of
the original object over `Spec R`. -/
lemma baseChange_toOver (f : R →+* S) (G : AffineGroupSchemeCat (CommRingCat.of R)) :
    (baseChange f G).obj.X =
      (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj G.obj.X :=
  (rfl)

/-- The underlying scheme of a base-changed affine group scheme is the corresponding fibre
product. -/
lemma baseChange_toScheme (f : R →+* S) (G : AffineGroupSchemeCat (CommRingCat.of R)) :
    (baseChange f G).obj.X.left =
      Limits.pullback G.obj.X.hom (Spec.map (CommRingCat.ofHom f)) :=
  (rfl)

/-- Base change of a morphism of affine group schemes. -/
noncomputable abbrev baseChangeMap (f : R →+* S)
    {G H : AffineGroupSchemeCat (CommRingCat.of R)} (g : G ⟶ H) :
    baseChange f G ⟶ baseChange f H :=
  ObjectProperty.homMk
    ((Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.map g.hom)

/-- The underlying group-object morphism of `baseChangeMap` is obtained by applying pullback. -/
@[simp]
lemma baseChangeMap_hom (f : R →+* S)
    {G H : AffineGroupSchemeCat (CommRingCat.of R)} (g : G ⟶ H) :
    (baseChangeMap f g).hom =
      (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.map g.hom :=
  (rfl)

/-- Base change preserves identity morphisms. -/
@[simp]
lemma baseChangeMap_id (f : R →+* S) (G : AffineGroupSchemeCat (CommRingCat.of R)) :
    baseChangeMap f (𝟙 G) = 𝟙 (baseChange f G) := by
  apply ObjectProperty.hom_ext
  exact (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.map_id G.obj

/-- Base change preserves composition of morphisms. -/
@[simp]
lemma baseChangeMap_comp (f : R →+* S)
    {G H L : AffineGroupSchemeCat (CommRingCat.of R)} (g : G ⟶ H) (h : H ⟶ L) :
    baseChangeMap f (g ≫ h) = baseChangeMap f g ≫ baseChangeMap f h := by
  apply ObjectProperty.hom_ext
  exact (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapGrp.map_comp g.hom h.hom

/-- Pullback along `Spec S ⟶ Spec R` defines a functor from affine group schemes over
`Spec R` to affine group schemes over `Spec S`. -/
noncomputable abbrev baseChangeFunctor (f : R →+* S) :
    AffineGroupSchemeCat (CommRingCat.of R) ⥤
      AffineGroupSchemeCat (CommRingCat.of S) where
  obj G := baseChange f G
  map g := baseChangeMap f g
  map_id G := baseChangeMap_id f G
  map_comp g h := baseChangeMap_comp f g h

/-- The object part of `baseChangeFunctor` is base change of affine group schemes. -/
@[simp]
lemma baseChangeFunctor_obj (f : R →+* S)
    (G : AffineGroupSchemeCat (CommRingCat.of R)) :
    (baseChangeFunctor f).obj G = baseChange f G :=
  (rfl)

/-- The morphism part of `baseChangeFunctor` is base change of affine-group-scheme morphisms. -/
@[simp]
lemma baseChangeFunctor_map (f : R →+* S)
    {G H : AffineGroupSchemeCat (CommRingCat.of R)} (g : G ⟶ H) :
    (baseChangeFunctor f).map g = baseChangeMap f g :=
  (rfl)

end AffineGroupSchemeCat

end TauCeti
