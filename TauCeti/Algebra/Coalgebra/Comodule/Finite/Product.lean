/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Prod
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Preadditive
public import TauCeti.Algebra.Coalgebra.Comodule.Product

/-!
# Products of finitely generated comodules

This file packages the direct-sum product comodule inside `FGComoduleCat`. The ambient
category `ComoduleCat` already has the product comodule on the cartesian product of the
underlying modules; finite generation is preserved by binary products of modules, so this
construction stays in the full subcategory of finitely generated comodules. The same concrete
object is registered as the categorical binary product, which is upgraded to a biproduct over a
commutative ring. Downstream code then uses Mathlib's generic `M ⨯ N` / `M ⊞ N` API.

This is a small Layer 1 prerequisite for the reductive-groups roadmap target on the
finite-dimensional comodule representation category: products and biproducts are needed before
tensor products, duals, and the rigid monoidal category can be built.

## Main declarations

* `TauCeti.FGComoduleCat.hasBinaryProduct`: the categorical binary product instance using
  the concrete product object.
* `TauCeti.FGComoduleCat.hasBinaryProducts`, `hasFiniteProducts`: product infrastructure
  induced by the binary product and the existing zero object.
* `TauCeti.FGComoduleCat.hasBinaryBiproduct`: the ring/preadditive biproduct instance induced
  by the binary product.
* `TauCeti.FGComoduleCat.hasBinaryBiproducts`, `hasFiniteBiproducts`: aggregate
  ring/preadditive biproduct infrastructure.

## References

This supplies finite-category packaging for `ReductiveGroups/README.md` in TauCetiRoadmap,
Layer 1 target "Comodules over a coalgebra/Hopf algebra": the finite-dimensional comodule
category should have additive finite products before the rigid monoidal representation
category is developed. The construction reuses the direct-sum comodule from
`TauCeti.Algebra.Coalgebra.Comodule.Product`.
-/

public section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

universe u v w

namespace FGComoduleCat

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The product of two finitely generated comodules, carried by the product of the
underlying modules. -/
private abbrev prod (M N : FGComoduleCat.{u, v, w} R C) : FGComoduleCat.{u, v, w} R C where
  obj := ComoduleCat.prod R C M.obj N.obj
  property := by
    -- `ComoduleCat.prod` is carried definitionally by the raw product `M × N`, so the finite
    -- generation obligation is exactly the standard product finiteness instance.
    change Module.Finite R (M × N)
    exact Module.Finite.prod

section Semiring

variable {R C}

private abbrev prodFst (M N : FGComoduleCat.{u, v, w} R C) : prod R C M N ⟶ M :=
  ObjectProperty.homMk (ComoduleCat.prodFst M.obj N.obj)

private abbrev prodSnd (M N : FGComoduleCat.{u, v, w} R C) : prod R C M N ⟶ N :=
  ObjectProperty.homMk (ComoduleCat.prodSnd M.obj N.obj)

private abbrev prodLift {P M N : FGComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    P ⟶ prod R C M N :=
  ObjectProperty.homMk (ComoduleCat.prodLift f.hom g.hom)

private theorem prodFst_hom (M N : FGComoduleCat.{u, v, w} R C) :
    (prodFst M N).hom = ComoduleCat.prodFst M.obj N.obj :=
  rfl

private theorem prodSnd_hom (M N : FGComoduleCat.{u, v, w} R C) :
    (prodSnd M N).hom = ComoduleCat.prodSnd M.obj N.obj :=
  rfl

private theorem prodLift_fst {P M N : FGComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodFst M N = f := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  exact ComoduleCat.prodLift_fst (R := R) (C := C) f.hom g.hom

private theorem prodLift_snd {P M N : FGComoduleCat.{u, v, w} R C} (f : P ⟶ M) (g : P ⟶ N) :
    prodLift f g ≫ prodSnd M N = g := by
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom]
  exact ComoduleCat.prodLift_snd (R := R) (C := C) f.hom g.hom

private theorem prod_hom_ext {P M N : FGComoduleCat.{u, v, w} R C} {f g : P ⟶ prod R C M N}
    (hfst : f ≫ prodFst M N = g ≫ prodFst M N)
    (hsnd : f ≫ prodSnd M N = g ≫ prodSnd M N) : f = g := by
  apply ObjectProperty.hom_ext
  exact ComoduleCat.prod_hom_ext (R := R) (C := C)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, prodFst_hom] using
      congrArg (fun h => h.hom) hfst)
    (by simpa only [ObjectProperty.FullSubcategory.comp_hom, prodSnd_hom] using
      congrArg (fun h => h.hom) hsnd)

private def prodBinaryFan (M N : FGComoduleCat.{u, v, w} R C) : Limits.BinaryFan M N :=
  Limits.BinaryFan.mk (prodFst M N) (prodSnd M N)

private def prodBinaryFanIsLimit (M N : FGComoduleCat.{u, v, w} R C) :
    Limits.IsLimit (prodBinaryFan M N) :=
  Limits.BinaryFan.IsLimit.mk _
    (fun f g => prodLift f g)
    (fun f g => prodLift_fst f g)
    (fun f g => prodLift_snd f g)
    (fun f g _ hfst hsnd =>
      prod_hom_ext
        (hfst.trans (prodLift_fst f g).symm)
        (hsnd.trans (prodLift_snd f g).symm))

/-- The concrete product supplies the categorical binary product of finitely generated
comodules. -/
instance hasBinaryProduct (M N : FGComoduleCat.{u, v, w} R C) :
    Limits.HasBinaryProduct M N :=
  Limits.HasLimit.mk ⟨prodBinaryFan M N, prodBinaryFanIsLimit M N⟩

/-- Finitely generated comodules have categorical binary products. -/
instance hasBinaryProducts : Limits.HasBinaryProducts (FGComoduleCat.{u, v, w} R C) :=
  Limits.hasBinaryProducts_of_hasLimit_pair (FGComoduleCat.{u, v, w} R C)

/-- Finitely generated comodules have finite products. -/
instance hasFiniteProducts : Limits.HasFiniteProducts (FGComoduleCat.{u, v, w} R C) :=
  CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

end Semiring

section Ring

variable {R : Type u} [CommRing R]
variable {C : Type v} [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The preadditive binary product is also a binary biproduct. -/
instance hasBinaryBiproduct (M N : FGComoduleCat.{u, v, w} R C) :
    Limits.HasBinaryBiproduct M N :=
  Limits.HasBinaryBiproduct.of_hasBinaryProduct M N

/-- Finitely generated comodules over a commutative ring have binary biproducts. -/
instance hasBinaryBiproducts : Limits.HasBinaryBiproducts (FGComoduleCat.{u, v, w} R C) :=
  Limits.HasBinaryBiproducts.of_hasBinaryProducts

/-- Finitely generated comodules over a commutative ring have finite biproducts. -/
instance hasFiniteBiproducts : Limits.HasFiniteBiproducts (FGComoduleCat.{u, v, w} R C) :=
  Limits.HasFiniteBiproducts.of_hasFiniteProducts

end Ring

end FGComoduleCat

end TauCeti
