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

* `TauCeti.AlgebraicGeometry.Scheme.Modules.tensorProduct M N` is the sheafified tensor
  product;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.sheafificationIso M` identifies the
  sheafification of the underlying presheaf of modules of `M` with `M`;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.tensorProductCongrLeft/right` transport an
  isomorphism of one argument through the tensor product;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.tensorProductUnitIsoLeft/right` identify
  `𝒪ₓ ⊗ M` and `M ⊗ 𝒪ₓ` with `M`;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.tensorProductComm` provides symmetry;
* `TauCeti.AlgebraicGeometry.Scheme.Modules.tensorProductSheafAssoc` provides the
  associativity isomorphism at the level of sheafifications of sectionwise tensor
  products, the form from which associativity of iterated tensor products of modules is
  obtained by composing with `sheafificationIso`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer A, item "Invertible
sheaves on a scheme; the Picard group `Pic X` under `⊗`": the tensor product is the
operation from which the Picard group will be built. What remains towards that item is
the closure of invertible sheaves under the tensor product, duals, and the resulting
group structure on isomorphism classes.
-/

public section

open CategoryTheory Category Limits MonoidalCategory Opposite TopologicalSpace

namespace TauCeti

universe u

open AlgebraicGeometry Scheme

noncomputable section

namespace Scheme

variable (X : Scheme.{u})

/-- The identity morphism of the underlying presheaf of rings of `X` is locally injective. -/
instance : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X.toTopCat)
    (𝟙 X.ringCatSheaf.obj) := inferInstance

/-- The identity morphism of the underlying presheaf of rings of `X` is locally surjective. -/
instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X.toTopCat)
    (𝟙 X.ringCatSheaf.obj) := inferInstance

/-- The monoidal category structure on presheaves of modules over the underlying presheaf
of rings of `X`, obtained from Mathlib's monoidal structure on presheaves of modules over
a presheaf of commutative rings. -/
instance instMonoidalPresheafOfModulesRingCatSheafObj :
    MonoidalCategory (PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (MonoidalCategory (PresheafOfModules.{u}
    (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u})))

/-- The braided category structure on presheaves of modules over the underlying presheaf
of rings of `X`. -/
instance instBraidedPresheafOfModulesRingCatSheafObj :
    BraidedCategory (PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs (BraidedCategory (PresheafOfModules.{u}
    (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u})))

namespace Modules

/-- The functor of sheafified tensor products with a fixed second argument:
it sends `M` to `M ⊗ N`. -/
def tensorProductRightFunctor {X : Scheme.{u}} (N : X.Modules) : X.Modules ⥤ X.Modules :=
  (SheafOfModules.forget X.ringCatSheaf).comp
    ((MonoidalCategory.tensorRight (C := PresheafOfModules.{u} X.ringCatSheaf.obj)
      N.val).comp (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))

/-- The functor of sheafified tensor products with a fixed first argument:
it sends `N` to `M ⊗ N`. -/
def tensorProductLeftFunctor {X : Scheme.{u}} (M : X.Modules) : X.Modules ⥤ X.Modules :=
  (SheafOfModules.forget X.ringCatSheaf).comp
    ((MonoidalCategory.tensorLeft (C := PresheafOfModules.{u} X.ringCatSheaf.obj)
      M.val).comp (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))

/-- The tensor product of two `𝒪ₓ`-modules: the sectionwise tensor product of the
underlying presheaves of modules, sheafified. -/
def tensorProduct {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  (tensorProductRightFunctor N).obj M

@[simp]
lemma tensorProduct_obj_val {X : Scheme.{u}} (M N : X.Modules) :
    (tensorProduct M N).val =
      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
        (M.val ⊗ N.val)).val :=
  by
    rw [tensorProduct]
    rfl

/-- The sheafification of the underlying presheaf of modules of an `𝒪ₓ`-module is
isomorphic to the module. This is the counit of the sheafification adjunction, which is an
isomorphism because its right adjoint is fully faithful. -/
def sheafificationIso {X : Scheme.{u}} (M : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj M.val ≅ M := by
  have h := PresheafOfModules.instIsIsoFunctorSheafOfModulesCounitSheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  haveI h2 := ((NatTrans.isIso_iff_isIso_app
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).mp h) M
  exact @asIso _ _ _ _
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit.app M) h2

/-- An isomorphism of the first argument transports through the tensor product. -/
def tensorProductCongrLeft {X : Scheme.{u}} {M M' N : X.Modules} (e : M ≅ M') :
    tensorProduct M N ≅ tensorProduct M' N :=
  (tensorProductRightFunctor N).mapIso e

/-- An isomorphism of the second argument transports through the tensor product. -/
def tensorProductCongrRight {X : Scheme.{u}} {M N N' : X.Modules} (e : N ≅ N') :
    tensorProduct M N ≅ tensorProduct M N' :=
  (tensorProductLeftFunctor M).mapIso e

/-- Tensoring with the structure sheaf (on the left) does nothing. -/
def tensorProductUnitIsoLeft {X : Scheme.{u}} (M : X.Modules) :
    tensorProduct (.unit X.ringCatSheaf) M ≅ M :=
  show (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    ((SheafOfModules.unit X.ringCatSheaf).val ⊗ M.val) ≅ M from
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (λ_ M.val) ≪≫
      sheafificationIso M

/-- Tensoring with the structure sheaf (on the right) does nothing. -/
def tensorProductUnitIsoRight {X : Scheme.{u}} (M : X.Modules) :
    tensorProduct M (.unit X.ringCatSheaf) ≅ M :=
  show (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (M.val ⊗ (SheafOfModules.unit X.ringCatSheaf).val) ≅ M from
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (ρ_ M.val) ≪≫
      sheafificationIso M

/-- Symmetry of the tensor product of `𝒪ₓ`-modules. -/
def tensorProductComm {X : Scheme.{u}} (M N : X.Modules) :
    tensorProduct M N ≅ tensorProduct N M :=
  show (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (M.val ⊗ N.val) ≅
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (N.val ⊗ M.val) from
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (β_ M.val N.val)

/-- Associativity of the sectionwise tensor product after sheafification: this is the form
in which associativity of the tensor product of `𝒪ₓ`-modules is available; combined with
`sheafificationIso` it yields an associativity isomorphism for iterated tensor products. -/
def tensorProductSheafAssoc {X : Scheme.{u}} (M N P : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      ((M.val ⊗ N.val) ⊗ P.val) ≅
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (M.val ⊗ (N.val ⊗ P.val)) :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (α_ M.val N.val P.val)

end Modules

end Scheme

end

end TauCeti
