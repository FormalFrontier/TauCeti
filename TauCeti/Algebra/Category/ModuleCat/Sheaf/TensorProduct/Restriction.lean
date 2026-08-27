/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
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
sheafification.

## Main declaration

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

open CategoryTheory Category Opposite

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})
variable (M N : SheafOfModules.{u} (SheafOfModules.ringCatSheaf R))

namespace SheafOfModules

private abbrev presheafTensor : PresheafOfModules.{u} (ringCatSheaf R).obj :=
  PresheafOfModules.Monoidal.tensorObj M.val N.val

private abbrev tensorSheafification : SheafOfModules.{u} (ringCatSheaf R) :=
  (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj (presheafTensor R M N)

private abbrev overModule (X : C)
    (P : SheafOfModules.{u} (ringCatSheaf R)) :
    SheafOfModules.{u} (ringCatSheaf (R.over X)) :=
  P.over X

/-- Before sheafification, taking the tensor product commutes definitionally with
restriction to a slice site. -/
private def overTensorPresheafIso (X : C) :
    PresheafOfModules.Monoidal.tensorObj
        (overModule R X M).val (overModule R X N).val ≅
      (PresheafOfModules.pushforward (𝟙 _)).obj (presheafTensor R M N) :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The restriction of the global sheafification map, viewed as a morphism of presheaves
of modules on the slice site. -/
private def restrictedTensorUnit (X : C) :
    (PresheafOfModules.pushforward (𝟙 _)).obj (presheafTensor R M N) ⟶
      ((tensorSheafification R M N).over X).val :=
  (PresheafOfModules.pushforward (𝟙 _)).map
    ((PresheafOfModules.sheafificationAdjunction
      (R := ringCatSheaf R) (𝟙 (ringCatSheaf R).obj)).unit.app (presheafTensor R M N))

/-- The presheaf-level comparison from the tensor product of the restrictions to the
restriction of the tensor product. -/
private def overTensorPresheafMap (X : C) :
    PresheafOfModules.Monoidal.tensorObj
        (overModule R X M).val (overModule R X N).val ⟶
      ((tensorSheafification R M N).over X).val :=
  (overTensorPresheafIso R M N X).hom ≫ restrictedTensorUnit R M N X

private theorem toPresheaf_overTensorPresheafMap (X : C) :
    (PresheafOfModules.toPresheaf _).map (overTensorPresheafMap R M N X) =
      Functor.whiskerLeft (Over.forget X).op
        (CategoryTheory.toSheafify J (presheafTensor R M N).presheaf) := by
  rfl

private theorem overTensorPresheafMap_mem_W (X : C)
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (J.over X).W
      ((PresheafOfModules.toPresheaf _).map (overTensorPresheafMap R M N X)) := by
  rw [toPresheaf_overTensorPresheafMap]
  exact ((J.over X).W_iff_isLocallyBijective _).mpr
    ⟨Presheaf.isLocallyInjective_whisker (J.over X) J (Over.forget X) _,
      Presheaf.isLocallySurjective_whisker (J.over X) J (Over.forget X) _⟩

private theorem isIso_sheafification_map_overTensorPresheafMap (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (ringCatSheaf (R.over X)).obj)).map (overTensorPresheafMap R M N X)) := by
  change ((MorphismProperty.isomorphisms _).inverseImage
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf (R.over X)).obj)))
      (overTensorPresheafMap R M N X)
  rw [← PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms]
  exact overTensorPresheafMap_mem_W R M N X

/-- Restriction to a slice site commutes with the tensor product of sheaves of modules.

The isomorphism points from the restriction of the global tensor product to the tensor
product formed on the slice site, so it can rewrite a restricted tensor product into the
local tensor product used by local trivializations. -/
def tensorProductOverIso (X : C)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (tensorProduct R M N).over X ≅
      tensorProduct (R.over X) (M.over X) (N.over X) := by
  let f := (PresheafOfModules.sheafification
    (𝟙 (ringCatSheaf (R.over X)).obj)).map (overTensorPresheafMap R M N X)
  have hf : IsIso f := isIso_sheafification_map_overTensorPresheafMap R M N X
  exact (SheafOfModules.overFunctor (ringCatSheaf R) X).mapIso
      (tensorProductIso R M N) ≪≫
    (sheafificationIso (R.over X) ((tensorSheafification R M N).over X)).symm ≪≫
    (@asIso _ _ _ _ f hf).symm ≪≫
    (tensorProductIso (R.over X) (M.over X) (N.over X)).symm

end SheafOfModules

end

end TauCeti
