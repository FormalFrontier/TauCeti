/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.PointFaithful
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.ScalarExtension.Monoidal

/-!
# Tensor automorphisms from algebraic-group points

Let `H` be a Hopf algebra over a commutative ring `R`, and let `A` be a commutative
`R`-algebra. Scalar extension of finite `H`-comodules is a strong monoidal functor

```text
FGComoduleCat R H ⥤ SemimoduleCat A,    M ↦ A ⊗[R] M.
```

Every `A`-valued point of `H` already acts naturally on this functor. This file proves that
the action preserves the tensor product and tensor unit, and therefore packages it as an
automorphism of the corresponding bundled lax monoidal functor. Over a principal ideal domain,
when `H` is free as an `R`-module, this map from points to tensor automorphisms is injective.

This is the faithful direction of the tensor-automorphism formulation of Tannakian
reconstruction. The converse, recovering a point from every tensor automorphism, remains a
separate theorem.

## Main declarations

* `TauCeti.Tannaka.fgPointNatIso_isMonoidal`: point actions on finite comodules preserve the
  tensor unit and tensor product.
* `TauCeti.Tannaka.fgPointTensorIsoHom`: points act on finite-comodule scalar extension by
  tensor automorphisms.
* `TauCeti.Tannaka.fgPointTensorIsoHom_injective`: this action is faithful over a principal
  ideal domain when the Hopf algebra is free.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.5 and 9.4.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u

variable (R : Type u) [CommRing R]
variable (H : Type u) [CommRing H] [HopfAlgebra R H]
variable (A : Type u) [CommRing A] [Algebra R A]

open Functor.LaxMonoidal

/-- The scalar-extension functor on finite comodules, bundled as a lax monoidal functor. -/
@[expose] noncomputable def fgScalarExtensionMonoidalFunctor :
    LaxMonoidalFunctor (FGComoduleCat.{u, u, u} R H) (SemimoduleCat.{u} A) :=
  LaxMonoidalFunctor.of (FGComoduleCat.scalarExtensionFunctor R H A)

/-- The natural automorphism induced by an algebra-valued point is monoidal. -/
theorem fgPointNatIso_isMonoidal (g : WithConv (H →ₐ[R] A)) :
    NatTrans.IsMonoidal (fgPointNatIsoHom R H A g).hom := by
  constructor
  · rw [FGComoduleCat.scalarExtensionFunctor_ε, fgPointNatIsoHom_hom_app]
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro a
    simp [Comodule.pointsAction_toLinearMap, Comodule.endOfPoint_trivial]
  · intro M N
    let _ : Comodule R H (M ⊗[R] N) :=
      inferInstanceAs (Comodule R H ((M ⊗ N : FGComoduleCat R H) : Type u))
    have htensor :
            SemimoduleCat.ofHom
              (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap ≫
            SemimoduleCat.ofHom (Comodule.endOfPoint
              ((M ⊗ N : FGComoduleCat R H) : Type u) g.ofConv) =
          (SemimoduleCat.ofHom (Comodule.endOfPoint M g.ofConv) ⊗ₘ
              SemimoduleCat.ofHom (Comodule.endOfPoint N g.ofConv)) ≫
            SemimoduleCat.ofHom
              (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap := by
      apply SemimoduleCat.hom_ext
      exact (Comodule.endOfPoint_tensor_of_coact_eq (R := R) (H := H) (A := A)
        (V := M) (W := N) (FGComoduleCat.tensor_coact (R := R) (C := H) M N)
          g.ofConv).symm
    have hcancel :
        eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A (M ⊗ N)).symm ≫
            eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A (M ⊗ N)) =
          𝟙 _ := by
      simp
    have hcancel_assoc {X : SemimoduleCat.{u} A}
        (f : SemimoduleCat.of A (A ⊗[R] (M ⊗ N)) ⟶ X) :
        eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A (M ⊗ N)).symm ≫
            eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A (M ⊗ N)) ≫ f = f := by
      rw [← Category.assoc, hcancel, Category.id_comp]
    have hcancel_nested {X Y Z : SemimoduleCat.{u} A}
        (f : X ⟶ Y) (q : Y ⟶ SemimoduleCat.of A (A ⊗[R] (M ⊗ N)))
        (r : SemimoduleCat.of A (A ⊗[R] (M ⊗ N)) ⟶ Z) :
        (f ≫ (q ≫
            eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A (M ⊗ N)).symm)) ≫
            eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A (M ⊗ N)) ≫ r =
          f ≫ q ≫ r := by
      simp only [Category.assoc, hcancel_assoc]
    have hcancelTensor :
        (eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm ⊗ₘ
            eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A N).symm) ≫
          (eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M) ⊗ₘ
            eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A N)) = 𝟙 _ := by
      simp
    have hcancelTensor_assoc {X : SemimoduleCat.{u} A}
        (f : ((SemimoduleCat.of A (A ⊗[R] M) ⊗
          SemimoduleCat.of A (A ⊗[R] N)) : SemimoduleCat A) ⟶ X) :
        (eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm ⊗ₘ
            eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A N).symm) ≫
          (eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M) ⊗ₘ
            eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A N)) ≫ f = f := by
      rw [← Category.assoc, hcancelTensor, Category.id_comp]
    have hcancelTensor_nested {X Y Z : SemimoduleCat.{u} A}
        (f : X ⟶ Y)
        (q : Y ⟶
          ((SemimoduleCat.of A (A ⊗[R] M) ⊗
            SemimoduleCat.of A (A ⊗[R] N)) : SemimoduleCat A))
        (r : ((SemimoduleCat.of A (A ⊗[R] M) ⊗
          SemimoduleCat.of A (A ⊗[R] N)) : SemimoduleCat A) ⟶ Z) :
        (f ≫ q ≫
            (eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm ⊗ₘ
              eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A N).symm)) ≫
          (eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M) ⊗ₘ
              eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A N)) ≫ r =
            f ≫ q ≫ r := by
      simp only [Category.assoc, hcancelTensor_assoc]
    erw [FGComoduleCat.scalarExtensionFunctor_μ,
      fgPointNatIsoHom_hom_app, fgPointNatIsoHom_hom_app,
      fgPointNatIsoHom_hom_app]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom,
      ← MonoidalCategory.tensorHom_comp_tensorHom]
    erw [hcancel_nested, hcancelTensor_nested]
    simp only [LinearEquiv.toModuleIsoₛ_hom, Comodule.pointsAction_toLinearMap]
    slice_lhs 2 3 => erw [← Category.assoc, htensor]
    erw [Category.assoc]

/-- An algebra-valued point as a tensor automorphism of finite-comodule scalar extension. -/
@[expose] noncomputable def fgPointTensorIso (g : WithConv (H →ₐ[R] A)) :
    fgScalarExtensionMonoidalFunctor R H A ≅ fgScalarExtensionMonoidalFunctor R H A := by
  exact @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _
    (fgPointNatIsoHom R H A g) (fgPointNatIso_isMonoidal R H A g)

/-- Forgetting tensor compatibility from the point automorphism recovers its underlying natural
automorphism. -/
@[simp]
theorem fgPointTensorIso_hom_hom (g : WithConv (H →ₐ[R] A)) :
    (fgPointTensorIso R H A g).hom.hom = (fgPointNatIsoHom R H A g).hom :=
  (rfl)

/-- Algebra-valued points act on finite-comodule scalar extension by tensor automorphisms. -/
@[expose] noncomputable def fgPointTensorIsoHom :
    WithConv (H →ₐ[R] A) →*
      Aut (fgScalarExtensionMonoidalFunctor R H A) where
  toFun := fgPointTensorIso R H A
  map_one' := by
    apply Aut.ext
    apply LaxMonoidalFunctor.hom_ext
    dsimp only [fgPointTensorIso, LaxMonoidalFunctor.isoMk,
      LaxMonoidalFunctor.homMk]
    change (fgPointNatIsoHom R H A 1).hom = 𝟙 _
    have hone := congrArg Iso.hom (map_one (fgPointNatIsoHom R H A))
    change (fgPointNatIsoHom R H A 1).hom = 𝟙 _ at hone
    exact hone
  map_mul' g h := by
    apply Aut.ext
    apply LaxMonoidalFunctor.hom_ext
    dsimp only [fgPointTensorIso, LaxMonoidalFunctor.isoMk,
      LaxMonoidalFunctor.homMk]
    change (fgPointNatIsoHom R H A (g * h)).hom =
      (fgPointNatIsoHom R H A h).hom ≫ (fgPointNatIsoHom R H A g).hom
    have hmul := congrArg Iso.hom (map_mul (fgPointNatIsoHom R H A) g h)
    change (fgPointNatIsoHom R H A (g * h)).hom =
      (fgPointNatIsoHom R H A h).hom ≫ (fgPointNatIsoHom R H A g).hom at hmul
    exact hmul

/-- Forgetting the tensor compatibility of a point tensor automorphism recovers the original
natural automorphism. -/
@[simp]
theorem fgPointTensorIsoHom_hom_hom (g : WithConv (H →ₐ[R] A)) :
    (fgPointTensorIsoHom R H A g).hom.hom = (fgPointNatIsoHom R H A g).hom :=
  fgPointTensorIso_hom_hom R H A g

/-- The tensor-automorphism action of points is faithful over a principal ideal domain when the
Hopf algebra is free as a module. -/
theorem fgPointTensorIsoHom_injective [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Free R H] :
    Function.Injective (fgPointTensorIsoHom R H A) := by
  intro g h hgh
  apply fgPointNatIsoHom_injective R H A
  apply Iso.ext
  apply NatTrans.ext
  funext (M : FGComoduleCat.{u, u, u} R H)
  have hhom := congrArg LaxMonoidalFunctor.Hom.hom (congrArg Iso.hom hgh)
  rw [fgPointTensorIsoHom_hom_hom, fgPointTensorIsoHom_hom_hom] at hhom
  exact congrArg (fun η ↦ η.app M) hhom

end TauCeti.Tannaka
