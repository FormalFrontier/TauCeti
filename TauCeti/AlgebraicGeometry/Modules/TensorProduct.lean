/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Tensor products of sheaves of modules on a scheme

Given two sheaves of modules `M`, `N` on a scheme `X`, we construct their tensor product
`M ⊗ N` as a sheaf of modules: sectionwise one tensors the modules of sections over the
rings of sections, and the resulting presheaf of modules is sheafified. Mathlib already
provides the sectionwise symmetric monoidal structure on presheaves of modules over a
presheaf of commutative rings; here it is transported to presheaves of modules over the
underlying presheaf of rings of `X` and combined with sheafification.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.tensorProduct M N` is the sheafified tensor
  product;
* `AlgebraicGeometry.Scheme.Modules.tensorProductIso M N` is its defining
  identification with the sheafification of the sectionwise tensor product;
* `AlgebraicGeometry.Scheme.Modules.sheafificationIso M` identifies the
  sheafification of the underlying presheaf of modules of `M` with `M`;
* `AlgebraicGeometry.Scheme.Modules.tensorProductCongrLeft/right` transport an
  isomorphism of one argument through the tensor product;
* `AlgebraicGeometry.Scheme.Modules.tensorProductUnitIsoLeft/right` identify
  `𝒪ₓ ⊗ M` and `M ⊗ 𝒪ₓ` with `M`;
* `AlgebraicGeometry.Scheme.Modules.tensorProductComm` provides symmetry;
* `AlgebraicGeometry.Scheme.Modules.tensorProductSheafAssoc` provides the
  associativity isomorphism at the level of sheafifications of sectionwise tensor
  products, the form from which associativity of iterated tensor products of modules is
  obtained by composing with `tensorProductIso` and `sheafificationIso`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible
sheaves on a scheme; the Picard group `Pic X` under `⊗`": the tensor product is the
operation from which the Picard group will be built. What remains towards that item is
the closure of invertible sheaves under the tensor product, duals, and the resulting
group structure on isomorphism classes.
-/

public section

open CategoryTheory Category Limits MonoidalCategory Opposite TopologicalSpace
  AlgebraicGeometry Scheme.Modules

namespace TauCeti

universe u

noncomputable section

namespace AlgebraicGeometry

namespace Scheme

variable (X : Scheme.{u})

/-- The monoidal category structure on presheaves of modules over the underlying presheaf
of rings of `X`, obtained from Mathlib's monoidal structure on presheaves of modules over
a presheaf of commutative rings. -/
instance instMonoidalPresheafOfModulesRingCatSheafObj :
    MonoidalCategory (PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u})))

/-- The symmetric category structure on presheaves of modules over the underlying presheaf
of rings of `X`, obtained from Mathlib's symmetric structure on presheaves of modules over
a presheaf of commutative rings. -/
instance instSymmetricPresheafOfModulesRingCatSheafObj :
    SymmetricCategory (PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (SymmetricCategory (PresheafOfModules.{u}
    (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u})))

namespace Modules

/-- The functor of sheafified tensor products with a fixed second argument:
it sends `M` to `M ⊗ N`. -/
@[expose]
def _root_.AlgebraicGeometry.Scheme.Modules.tensorProductRightFunctor {X : Scheme.{u}}
    (N : X.Modules) : X.Modules ⥤ X.Modules :=
  (SheafOfModules.forget X.ringCatSheaf).comp
    ((MonoidalCategory.tensorRight (C := PresheafOfModules.{u} X.ringCatSheaf.obj)
      N.val).comp (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))

/-- The functor of sheafified tensor products with a fixed first argument:
it sends `N` to `M ⊗ N`. -/
@[expose]
def _root_.AlgebraicGeometry.Scheme.Modules.tensorProductLeftFunctor {X : Scheme.{u}}
    (M : X.Modules) : X.Modules ⥤ X.Modules :=
  (SheafOfModules.forget X.ringCatSheaf).comp
    ((MonoidalCategory.tensorLeft (C := PresheafOfModules.{u} X.ringCatSheaf.obj)
      M.val).comp (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))

/-- The tensor product of two `𝒪ₓ`-modules: the sectionwise tensor product of the
underlying presheaves of modules, sheafified. -/
@[expose]
def _root_.AlgebraicGeometry.Scheme.Modules.tensorProduct {X : Scheme.{u}}
    (M N : X.Modules) : X.Modules :=
  (tensorProductRightFunctor N).obj M

@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.tensorProduct_val {X : Scheme.{u}}
    (M N : X.Modules) :
    (tensorProduct M N).val =
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (M.val ⊗ N.val)).val :=
  rfl

/-- The defining identification of the tensor product with the sheafification of the
sectionwise tensor product of the underlying presheaves of modules. -/
def _root_.AlgebraicGeometry.Scheme.Modules.tensorProductIso {X : Scheme.{u}} (M N : X.Modules) :
    tensorProduct M N ≅
      (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (M.val ⊗ N.val) :=
  Iso.refl _

/-- The sheafification of the underlying presheaf of modules of an `𝒪ₓ`-module is
isomorphic to the module; this is the counit of the sheafification adjunction. -/
@[expose]
def _root_.AlgebraicGeometry.Scheme.Modules.sheafificationIso {X : Scheme.{u}} (M : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M.val ≅ M :=
  (asIso
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app M

/-- The forward map of `sheafificationIso` is the counit of the sheafification
adjunction. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.sheafificationIso_hom {X : Scheme.{u}}
    (M : X.Modules) :
    (sheafificationIso M).hom =
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).counit.app M :=
  rfl

/-- An isomorphism of the first argument transports through the tensor product. -/
def _root_.AlgebraicGeometry.Scheme.Modules.tensorProductCongrLeft {X : Scheme.{u}}
    {M M' N : X.Modules} (e : M ≅ M') :
    tensorProduct M N ≅ tensorProduct M' N :=
  (tensorProductRightFunctor N).mapIso e

/-- An isomorphism of the second argument transports through the tensor product. -/
def _root_.AlgebraicGeometry.Scheme.Modules.tensorProductCongrRight {X : Scheme.{u}}
    {M N N' : X.Modules} (e : N ≅ N') :
    tensorProduct M N ≅ tensorProduct M N' :=
  (tensorProductLeftFunctor M).mapIso e

/-- Congruence in the first argument sends identity morphisms to identity isomorphisms. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.tensorProductCongrLeft_refl {X : Scheme.{u}}
    (M N : X.Modules) :
    tensorProductCongrLeft (Iso.refl M) = Iso.refl (tensorProduct M N) :=
  Functor.mapIso_refl (tensorProductRightFunctor N) M

/-- Congruence in the second argument sends identity morphisms to identity isomorphisms. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.tensorProductCongrRight_refl
    {X : Scheme.{u}} (M N : X.Modules) :
    tensorProductCongrRight (Iso.refl N) = Iso.refl (tensorProduct M N) :=
  Functor.mapIso_refl (tensorProductLeftFunctor M) N

/-- Congruence in the first argument respects composition. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.tensorProductCongrLeft_trans {X : Scheme.{u}}
    {M₁ M₂ M₃ : X.Modules}
    (N : X.Modules) (e₁ : M₁ ≅ M₂) (e₂ : M₂ ≅ M₃) :
    (tensorProductCongrLeft (X := X) (M := M₁) (M' := M₃) (N := N) (e₁ ≪≫ e₂)) =
      tensorProductCongrLeft (X := X) (N := N) e₁ ≪≫
        tensorProductCongrLeft (X := X) (N := N) e₂ :=
  Functor.mapIso_trans _ e₁ e₂

/-- Congruence in the second argument respects composition. -/
@[simp]
theorem _root_.AlgebraicGeometry.Scheme.Modules.tensorProductCongrRight_trans {X : Scheme.{u}}
    (M : X.Modules) {N₁ N₂ N₃ : X.Modules} (e₁ : N₁ ≅ N₂) (e₂ : N₂ ≅ N₃) :
    (tensorProductCongrRight (X := X) (M := M) (N := N₁) (N' := N₃) (e₁ ≪≫ e₂)) =
      tensorProductCongrRight (X := X) (M := M) e₁ ≪≫
        tensorProductCongrRight (X := X) (M := M) e₂ :=
  Functor.mapIso_trans _ e₁ e₂

/-- Tensoring with the structure sheaf (on the left) does nothing. -/
def _root_.AlgebraicGeometry.Scheme.Modules.tensorProductUnitIsoLeft {X : Scheme.{u}}
    (M : X.Modules) :
    tensorProduct (.unit X.ringCatSheaf) M ≅ M :=
  (tensorProductIso (.unit X.ringCatSheaf) M).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (λ_ M.val) ≪≫
      sheafificationIso M

/-- Tensoring with the structure sheaf (on the right) does nothing. -/
def _root_.AlgebraicGeometry.Scheme.Modules.tensorProductUnitIsoRight {X : Scheme.{u}}
    (M : X.Modules) :
    tensorProduct M (.unit X.ringCatSheaf) ≅ M :=
  (tensorProductIso M (.unit X.ringCatSheaf)).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (ρ_ M.val) ≪≫
      sheafificationIso M

/-- Symmetry of the tensor product of `𝒪ₓ`-modules. -/
def _root_.AlgebraicGeometry.Scheme.Modules.tensorProductComm {X : Scheme.{u}}
    (M N : X.Modules) :
    tensorProduct M N ≅ tensorProduct N M :=
  (tensorProductIso M N).symm ≪≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (β_ M.val N.val) ≪≫
      tensorProductIso N M

/-- Associativity of the sectionwise tensor product after sheafification: this is the form
in which associativity of the tensor product of `𝒪ₓ`-modules is available; combined with
`tensorProductIso` and `sheafificationIso` it yields an associativity isomorphism for
iterated tensor products. -/
def _root_.AlgebraicGeometry.Scheme.Modules.tensorProductSheafAssoc {X : Scheme.{u}}
    (M N P : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      ((M.val ⊗ N.val) ⊗ P.val) ≅
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (M.val ⊗ (N.val ⊗ P.val)) :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (α_ M.val N.val P.val)

end Modules

end Scheme

end AlgebraicGeometry

end

end TauCeti
