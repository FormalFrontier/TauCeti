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
`TauCeti.AffineGroupSchemeCat.baseChangeFunctor`, and records its coherence in the base ring.

The group structure is transported by Mathlib's left-exact pullback functor on `Over` categories.
Affineness is preserved because the base `Spec R` is itself affine: the structure morphism of an
affine group scheme over `Spec R` is then an affine morphism, and affine morphisms are stable
under base change, so the fibre product with the affine scheme `Spec S` is affine. (Over a general
base scheme this argument is unavailable, and a fibre product of affine schemes need not be
affine.) Thus the construction applies over general commutative rings; no field or finite-type
hypothesis is needed.

## Main declarations

* `TauCeti.AffineGroupSchemeCat.baseChange`: base change of one affine group scheme.
* `TauCeti.AffineGroupSchemeCat.baseChangeMap`: base change of a morphism.
* `TauCeti.AffineGroupSchemeCat.baseChangeFunctor`: functorial base change.
* `TauCeti.AffineGroupSchemeCat.baseChangeFunctorIdIso`,
  `TauCeti.AffineGroupSchemeCat.baseChangeFunctorCompIso`: base change along the identity ring
  map is the identity, and base change along a composite is the composite of base changes.

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

variable {R S T : CommRingCat.{u}}

/-- Base change of an affine group scheme along a morphism `f : R ⟶ S` of commutative rings.

Its underlying scheme is the fibre product with `Spec S` over `Spec R`, and its group-object
structure is the one transported by pullback. -/
noncomputable abbrev baseChange (f : R ⟶ S) (G : AffineGroupSchemeCat R) :
    AffineGroupSchemeCat S :=
  ⟨(Over.pullback (Spec.map f)).mapGrp.obj G.obj, by
    rw [affineGroupSchemeProperty_iff]
    -- unfold the pulled-back group object to its underlying fibre product `G ×[Spec R] Spec S`,
    -- which `Mathlib.AlgebraicGeometry.Morphisms.Affine` knows to be affine
    simp only [Functor.mapGrp_obj_X, Over.pullback_obj_left]
    infer_instance⟩

/-- The underlying group object of a base-changed affine group scheme is obtained by applying
pullback to the original group object. -/
@[simp]
lemma baseChange_obj (f : R ⟶ S) (G : AffineGroupSchemeCat R) :
    (baseChange f G).obj = (Over.pullback (Spec.map f)).mapGrp.obj G.obj :=
  (rfl)

/-- The underlying object over `Spec S` of a base-changed affine group scheme is the pullback of
the original object over `Spec R`. -/
lemma baseChange_obj_X (f : R ⟶ S) (G : AffineGroupSchemeCat R) :
    (baseChange f G).obj.X = (Over.pullback (Spec.map f)).obj G.obj.X :=
  (rfl)

/-- The underlying scheme of a base-changed affine group scheme is the corresponding fibre
product. -/
lemma baseChange_obj_X_left (f : R ⟶ S) (G : AffineGroupSchemeCat R) :
    (baseChange f G).obj.X.left = Limits.pullback G.obj.X.hom (Spec.map f) :=
  (rfl)

/-- Base change of a morphism of affine group schemes. -/
noncomputable abbrev baseChangeMap (f : R ⟶ S) {G H : AffineGroupSchemeCat R} (g : G ⟶ H) :
    baseChange f G ⟶ baseChange f H :=
  ObjectProperty.homMk ((Over.pullback (Spec.map f)).mapGrp.map g.hom)

/-- The underlying group-object morphism of `baseChangeMap` is obtained by applying pullback. -/
@[simp]
lemma baseChangeMap_hom (f : R ⟶ S) {G H : AffineGroupSchemeCat R} (g : G ⟶ H) :
    (baseChangeMap f g).hom = (Over.pullback (Spec.map f)).mapGrp.map g.hom :=
  (rfl)

/-- Pullback along `Spec S ⟶ Spec R` defines a functor from affine group schemes over
`Spec R` to affine group schemes over `Spec S`. It is the lift through the affineness property
of the pullback functor on group objects, so its functor laws are the pullback functor's. -/
noncomputable def baseChangeFunctor (f : R ⟶ S) :
    AffineGroupSchemeCat R ⥤ AffineGroupSchemeCat S :=
  (affineGroupSchemeProperty S).lift
    ((affineGroupSchemeProperty R).ι ⋙ (Over.pullback (Spec.map f)).mapGrp)
    fun G => (baseChange f G).property

/-- The object part of `baseChangeFunctor` is base change of affine group schemes. -/
@[simp]
lemma baseChangeFunctor_obj (f : R ⟶ S) (G : AffineGroupSchemeCat R) :
    (baseChangeFunctor f).obj G = baseChange f G :=
  (rfl)

/-- The morphism part of `baseChangeFunctor` is base change of affine-group-scheme morphisms,
transported along `baseChangeFunctor_obj` at the source and target. -/
@[simp]
lemma baseChangeFunctor_map (f : R ⟶ S) {G H : AffineGroupSchemeCat R} (g : G ⟶ H) :
    (baseChangeFunctor f).map g =
      eqToHom (baseChangeFunctor_obj f G) ≫ baseChangeMap f g ≫
        eqToHom (baseChangeFunctor_obj f H).symm :=
  by
    unfold baseChangeFunctor baseChangeMap baseChange
    rfl

/-- Base change along the identity of `R` is the identity functor on affine group schemes over
`Spec R`.

The isomorphism is `Over.pullbackId` transported to group objects and then through the fully
faithful inclusion of the affine full subcategory; the `eqToIso` only records `Spec.map_id`,
which is not definitional. -/
noncomputable def baseChangeFunctorIdIso :
    baseChangeFunctor (𝟙 R) ≅ 𝟭 (AffineGroupSchemeCat R) :=
  by
    unfold baseChangeFunctor
    exact Functor.fullyFaithfulCancelRight (affineGroupSchemeProperty R).ι
      (Functor.isoWhiskerLeft _ (Functor.mapGrpNatIso
        (eqToIso (by simp only [Spec.map_id]) ≪≫ Over.pullbackId) ≪≫ Functor.mapGrpIdIso))

/-- Base change along a composite `f ≫ g` of ring maps is base change along `f` followed by base
change along `g`.

The isomorphism is `Over.pullbackComp` transported to group objects and then through the fully
faithful inclusion of the affine full subcategory; the `eqToIso` only records `Spec.map_comp`,
which is not definitional. -/
noncomputable def baseChangeFunctorCompIso (f : R ⟶ S) (g : S ⟶ T) :
    baseChangeFunctor (f ≫ g) ≅ baseChangeFunctor f ⋙ baseChangeFunctor g :=
  by
    unfold baseChangeFunctor
    exact Functor.fullyFaithfulCancelRight (affineGroupSchemeProperty T).ι
      (Functor.isoWhiskerLeft _ (Functor.mapGrpNatIso
        (eqToIso (by simp only [Spec.map_comp]) ≪≫ Over.pullbackComp (Spec.map g) (Spec.map f)) ≪≫
          Functor.mapGrpCompIso))

end AffineGroupSchemeCat

end TauCeti
