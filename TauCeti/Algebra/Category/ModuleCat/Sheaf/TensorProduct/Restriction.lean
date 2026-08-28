/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective

/-!
# Restriction of tensor products of sheaves of modules

For a sheaf of commutative rings `R` on a site and sheaves of `R`-modules `M` and `N`,
this file identifies the restriction of `M ⊗ N` to the slice site over an object `X`
with the tensor product of the restrictions of `M` and `N`.

The comparison is obtained from the unit of Mathlib's sheafification adjunction for
presheaves of modules. Its underlying morphism of presheaves of abelian groups is the
sheafification map restricted along `Over.forget X`. Since that functor is cocontinuous,
Mathlib's local-bijectivity results show that the comparison becomes an isomorphism after
sheafification. No formalization is vendored: the ingredients are Mathlib's
`PresheafOfModules.sheafificationAdjunction`,
`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms`, and
`Presheaf.isLocallyInjective_whisker`/`Presheaf.isLocallySurjective_whisker`.

## Main declaration

* `SheafOfModules.sheafificationOverIso` identifies restriction of a sheafification with
  sheafification after restriction;
* `SheafOfModules.tensorProductOverIso` identifies restriction of a tensor product with
  the tensor product of the restrictions.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible
sheaves on a scheme; the Picard group `Pic X` under `⊗`". It supplies the restriction
compatibility needed to put two local trivializations over a common refinement and prove
that an arbitrary tensor product of invertible sheaves is invertible. What remains towards
that item is arbitrary-factor closure under tensor product, duals, coherent associativity,
and the group structure on isomorphism classes.
-/

public section

open CategoryTheory Category MonoidalCategory Opposite

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})
variable (M N : SheafOfModules.{u} (SheafOfModules.ringCatSheaf R))

namespace SheafOfModules

/-- The restriction of a sheafification unit, viewed as a morphism of presheaves of
modules on the slice site. -/
def overSheafificationUnit (P : PresheafOfModules.{u} (ringCatSheaf R).obj) (X : C) :
    (PresheafOfModules.pushforward (𝟙 _)).obj P ⟶
      (((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj P).over X).val :=
  (PresheafOfModules.pushforward (𝟙 _)).map
    ((PresheafOfModules.sheafificationAdjunction
      (R := ringCatSheaf R) (𝟙 (ringCatSheaf R).obj)).unit.app P)

private theorem toPresheaf_map_overSheafificationUnit
    (P : PresheafOfModules.{u} (ringCatSheaf R).obj) (X : C) :
    (PresheafOfModules.toPresheaf _).map (overSheafificationUnit R P X) =
      Functor.whiskerLeft (Over.forget X).op
        (CategoryTheory.toSheafify J P.presheaf) := by
  -- This is `toPresheaf_map_sheafificationAdjunction_unit_app` whiskered using
  -- the definitional comparison `pushforwardCompToPresheaf`.
  rfl

private theorem W_toPresheaf_map_overSheafificationUnit
    (P : PresheafOfModules.{u} (ringCatSheaf R).obj) (X : C)
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (J.over X).W
      ((PresheafOfModules.toPresheaf _).map (overSheafificationUnit R P X)) := by
  rw [toPresheaf_map_overSheafificationUnit]
  exact ((J.over X).W_iff_isLocallyBijective _).mpr
    ⟨Presheaf.isLocallyInjective_whisker (J.over X) J (Over.forget X) _,
      Presheaf.isLocallySurjective_whisker (J.over X) J (Over.forget X) _⟩

private theorem isIso_sheafification_map_overSheafificationUnit
    (P : PresheafOfModules.{u} (ringCatSheaf R).obj) (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (ringCatSheaf (R.over X)).obj)).map (overSheafificationUnit R P X)) := by
  -- Unfold the inverse-image properties here: the source ring presheaf is definitionally
  -- `ringCatSheaf (R.over X)`, but the direct `inverseImage_iff` rewrite does not see that
  -- equality at its default transparency.
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf (R.over X)).obj)))
      (overSheafificationUnit R P X)
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact W_toPresheaf_map_overSheafificationUnit R P X

/-- The canonical comparison from sheafification after restriction to the restriction of
sheafification. -/
def sheafificationOverHom (P : PresheafOfModules.{u} (ringCatSheaf R).obj) (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (PresheafOfModules.sheafification
        (𝟙 (ringCatSheaf (R.over X)).obj)).obj
          (((PresheafOfModules.pushforward (𝟙 _)) :
            PresheafOfModules.{u} (ringCatSheaf R).obj ⥤
              PresheafOfModules.{u} (ringCatSheaf (R.over X)).obj).obj P) ⟶
      ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj P).over X :=
  (PresheafOfModules.sheafification
      (𝟙 (ringCatSheaf (R.over X)).obj)).map (overSheafificationUnit R P X) ≫
    (sheafificationIso (R.over X)
      (((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj P).over X)).hom

/-- Restriction to a slice site commutes with sheafification of presheaves of modules. -/
def sheafificationOverIso (P : PresheafOfModules.{u} (ringCatSheaf R).obj) (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj P).over X ≅
      (PresheafOfModules.sheafification
        (𝟙 (ringCatSheaf (R.over X)).obj)).obj
          (((PresheafOfModules.pushforward (𝟙 _)) :
            PresheafOfModules.{u} (ringCatSheaf R).obj ⥤
              PresheafOfModules.{u} (ringCatSheaf (R.over X)).obj).obj P) := by
  haveI := isIso_sheafification_map_overSheafificationUnit R P X
  exact (sheafificationIso (R.over X)
      (((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj P).over X)).symm ≪≫
    (asIso ((PresheafOfModules.sheafification
      (𝟙 (ringCatSheaf (R.over X)).obj)).map (overSheafificationUnit R P X))).symm

/-- The inverse of `sheafificationOverIso` is the canonical sheafification comparison. -/
@[simp]
theorem sheafificationOverIso_inv (P : PresheafOfModules.{u} (ringCatSheaf R).obj) (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (sheafificationOverIso R P X).inv = sheafificationOverHom R P X := by
  rfl

/-- The canonical comparison from the tensor product of the restrictions to the
restriction of the tensor product. -/
def tensorProductOverHom (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    tensorProduct (R.over X) (M.over X) (N.over X) ⟶
      (tensorProduct R M N).over X :=
  (tensorProductIso (R.over X) (M.over X) (N.over X)).hom ≫
    (PresheafOfModules.sheafification
      (𝟙 (ringCatSheaf (R.over X)).obj)).map
        (Functor.Monoidal.μIso
          (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget X) R.obj)
          M.val N.val).hom ≫
    sheafificationOverHom R (M.val ⊗ N.val) X ≫
    (SheafOfModules.overFunctor (ringCatSheaf R) X).map
      (tensorProductIso R M N).inv

/-- Restriction to a slice site commutes with the tensor product of sheaves of modules.

The isomorphism points from the restriction of the global tensor product to the tensor
product formed on the slice site, so it can rewrite a restricted tensor product into the
local tensor product used by local trivializations. -/
def tensorProductOverIso (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (tensorProduct R M N).over X ≅
      tensorProduct (R.over X) (M.over X) (N.over X) :=
  (SheafOfModules.overFunctor (ringCatSheaf R) X).mapIso
      (tensorProductIso R M N) ≪≫
    sheafificationOverIso R (M.val ⊗ N.val) X ≪≫
    (PresheafOfModules.sheafification
      (𝟙 (ringCatSheaf (R.over X)).obj)).mapIso
        (Functor.Monoidal.μIso
          (PresheafOfModules.pushforward₀OfCommRingCat (Over.forget X) R.obj)
          M.val N.val).symm ≪≫
    (tensorProductIso (R.over X) (M.over X) (N.over X)).symm

/-- The inverse of `tensorProductOverIso` is the canonical tensor-product comparison. -/
@[simp]
theorem tensorProductOverIso_inv (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (tensorProductOverIso R M N X).inv = tensorProductOverHom R M N X := by
  rfl

end SheafOfModules

end

end TauCeti
