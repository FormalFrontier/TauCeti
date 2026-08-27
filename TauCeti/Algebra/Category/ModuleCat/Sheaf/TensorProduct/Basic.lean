/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Tensor products of sheaves of modules

Given a site `(C, J)` carrying a sheaf of commutative rings `R`, and two sheaves of
`R`-modules `M`, `N`, we construct their tensor product `M ⊗ N` as a sheaf of modules:
sectionwise one tensors the modules of sections over the rings of sections, and the
resulting presheaf of modules is sheafified. Mathlib already provides the sectionwise
symmetric monoidal structure on presheaves of modules over a presheaf of commutative
rings (`PresheafOfModules.Monoidal`, contributed at the AIM workshop "Formalising algebraic
geometry" of June 24–28, 2024, https://aimath.org/pastworkshops/alggeominlean.html); here
that structure is transported to presheaves of modules over the sheaf of rings underlying
`R` and combined with Mathlib's sheafification adjunction for presheaves of modules
(`PresheafOfModules.sheafification`). Nothing here is specific to schemes.

## Main declarations

* `SheafOfModules.tensorProduct R M N` is the sheafified tensor product of two sheaves of
  `R`-modules;
* `SheafOfModules.tensorProductIso R M N` is its defining identification with the
  sheafification of the sectionwise tensor product of the underlying presheaves of modules;
* `SheafOfModules.sheafificationIso R M` identifies the sheafification of the underlying
  presheaf of modules of `M` with `M`;
* `SheafOfModules.tensorProductCongrLeft/right` transport an isomorphism of one argument
  through the tensor product;
* `SheafOfModules.tensorProductUnitIsoLeft/right` identify `R ⊗ M` and `M ⊗ R` with `M`;
* `SheafOfModules.tensorProductComm` provides symmetry.

The scheme-level specialization to `𝒪ₓ`-modules on a scheme `X`
(`AlgebraicGeometry.Scheme.Modules.tensorProduct`) is in
`TauCeti/AlgebraicGeometry/Modules/TensorProduct.lean`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible
sheaves on a scheme; the Picard group `Pic X` under `⊗`": the tensor product is the
operation from which the Picard group will be built. What remains towards that item is
the closure of invertible sheaves under the tensor product, duals, associativity of the
tensor product up to coherent isomorphism, and the resulting group structure on
isomorphism classes.
-/

public section

open CategoryTheory Category Limits MonoidalCategory Opposite

namespace TauCeti

universe u

noncomputable section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (R : Sheaf J CommRingCat.{u})

namespace SheafOfModules

/-- The sheaf of rings underlying a sheaf of commutative rings on a site; the site-level
analogue of `AlgebraicGeometry.Scheme.ringCatSheaf`. -/
abbrev ringCatSheaf : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat.{u})).obj R

/-- The monoidal category structure on presheaves of modules over the sheaf of rings
underlying a sheaf of commutative rings, obtained from Mathlib's monoidal structure on
presheaves of modules over a presheaf of commutative rings. -/
instance instMonoidalPresheafOfModulesRingCatSheaf :
    MonoidalCategory (PresheafOfModules.{u} (ringCatSheaf R).obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat.{u})))

/-- The symmetric category structure on presheaves of modules over the sheaf of rings
underlying a sheaf of commutative rings, obtained from Mathlib's symmetric structure on
presheaves of modules over a presheaf of commutative rings. -/
instance instSymmetricPresheafOfModulesRingCatSheaf :
    SymmetricCategory (PresheafOfModules.{u} (ringCatSheaf R).obj) :=
  inferInstanceAs (SymmetricCategory (PresheafOfModules.{u}
    (R.obj ⋙ forget₂ CommRingCat RingCat.{u})))

/-- The functor of sheafified tensor products with a fixed second argument:
it sends `M` to `M ⊗ N`. -/
def tensorProductRightFunctor (N : SheafOfModules.{u} (ringCatSheaf R)) :
    SheafOfModules.{u} (ringCatSheaf R) ⥤ SheafOfModules.{u} (ringCatSheaf R) :=
  (SheafOfModules.forget (ringCatSheaf R)).comp
    ((MonoidalCategory.tensorRight (C := PresheafOfModules.{u} (ringCatSheaf R).obj)
      N.val).comp (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)))

/-- The functor of sheafified tensor products with a fixed first argument:
it sends `N` to `M ⊗ N`. -/
def tensorProductLeftFunctor (M : SheafOfModules.{u} (ringCatSheaf R)) :
    SheafOfModules.{u} (ringCatSheaf R) ⥤ SheafOfModules.{u} (ringCatSheaf R) :=
  (SheafOfModules.forget (ringCatSheaf R)).comp
    ((MonoidalCategory.tensorLeft (C := PresheafOfModules.{u} (ringCatSheaf R).obj)
      M.val).comp (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)))

/-- The tensor product of two sheaves of `R`-modules: the sectionwise tensor product of
the underlying presheaves of modules, sheafified. -/
def tensorProduct (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    SheafOfModules.{u} (ringCatSheaf R) :=
  (tensorProductRightFunctor R N).obj M

@[simp]
lemma tensorProduct_val (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    (tensorProduct R M N).val =
      ((PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj
        (M.val ⊗ N.val)).val := by
  simp only [tensorProduct, tensorProductRightFunctor]
  rfl

/-- The defining identification of the tensor product with the sheafification of the
sectionwise tensor product of the underlying presheaves of modules. -/
def tensorProductIso (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R M N ≅
      (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj (M.val ⊗ N.val) :=
  Iso.refl _

/-- The sheafification of the underlying presheaf of modules of a sheaf of `R`-modules is
isomorphic to the module; this is the counit of the sheafification adjunction. -/
def sheafificationIso (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).obj M.val ≅ M :=
  (asIso
    (PresheafOfModules.sheafificationAdjunction (𝟙 (ringCatSheaf R).obj)).counit).app M

/-- The forward map of `sheafificationIso` is the counit of the sheafification
adjunction. -/
@[simp]
theorem sheafificationIso_hom (M : SheafOfModules.{u} (ringCatSheaf R)) :
    (sheafificationIso R M).hom =
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (ringCatSheaf R).obj)).counit.app M := by
  simp only [sheafificationIso]
  rfl

/-- An isomorphism of the first argument transports through the tensor product. -/
def tensorProductCongrLeft {M M' N : SheafOfModules.{u} (ringCatSheaf R)} (e : M ≅ M') :
    tensorProduct R M N ≅ tensorProduct R M' N :=
  (tensorProductRightFunctor R N).mapIso e

/-- An isomorphism of the second argument transports through the tensor product. -/
def tensorProductCongrRight {M N N' : SheafOfModules.{u} (ringCatSheaf R)} (e : N ≅ N') :
    tensorProduct R M N ≅ tensorProduct R M N' :=
  (tensorProductLeftFunctor R M).mapIso e

/-- Tensoring with the sheaf of rings itself (on the left) does nothing. -/
def tensorProductUnitIsoLeft (M : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R (_root_.SheafOfModules.unit (ringCatSheaf R)) M ≅ M :=
  (tensorProductIso R _ M).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso (λ_ M.val) ≪≫
      sheafificationIso R M

/-- Tensoring with the sheaf of rings itself (on the right) does nothing. -/
def tensorProductUnitIsoRight (M : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R M (_root_.SheafOfModules.unit (ringCatSheaf R)) ≅ M :=
  (tensorProductIso R M _).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso (ρ_ M.val) ≪≫
      sheafificationIso R M

/-- Symmetry of the tensor product of sheaves of `R`-modules. -/
def tensorProductComm (M N : SheafOfModules.{u} (ringCatSheaf R)) :
    tensorProduct R M N ≅ tensorProduct R N M :=
  (tensorProductIso R M N).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 (ringCatSheaf R).obj)).mapIso (β_ M.val N.val) ≪≫
      tensorProductIso R N M

end SheafOfModules

end

end TauCeti
