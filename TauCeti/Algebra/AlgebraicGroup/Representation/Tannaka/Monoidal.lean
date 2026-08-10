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

Let `H` be a Hopf algebra over a commutative semiring `R`, and let `A` be a commutative
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

* `TauCeti.Tannaka.isMonoidal_fgPointNatIsoHom_hom`: point actions on finite comodules preserve the
  tensor unit and tensor product.
* `TauCeti.Tannaka.fgPointTensorIsoHom`: points act on finite-comodule scalar extension by
  tensor automorphisms.
* `TauCeti.Tannaka.fgPointTensorIsoHom_injective`: this action is faithful over a principal
  ideal domain when the Hopf algebra is free.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§4.5 and 9.4.
* `Mathlib/RepresentationTheory/Tannaka.lean`: the bundled monoidal forgetful functor `forget`
  and point homomorphism `equivHom` provide the formal pattern adapted here to comodules.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u v

section Generic

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [HopfAlgebra R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]

open Functor.LaxMonoidal

/-- The natural automorphism induced by an algebra-valued point is monoidal. -/
theorem isMonoidal_fgPointNatIsoHom_hom (g : WithConv (H →ₐ[R] A)) :
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
    erw [FGComoduleCat.scalarExtensionFunctor_μ,
      fgPointNatIsoHom_hom_app, fgPointNatIsoHom_hom_app,
      fgPointNatIsoHom_hom_app]
    rw [← MonoidalCategory.tensorHom_comp_tensorHom,
      ← MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [cancel_epi]
    erw [Category.assoc, eqToHom_trans_assoc]
    simp only [MonoidalCategory.tensorHom_comp_tensorHom_assoc, eqToHom_trans,
      eqToHom_refl, Category.id_comp, Category.comp_id, LinearEquiv.toModuleIsoₛ_hom,
      Comodule.pointsAction_toLinearMap]
    erw [← Category.assoc, htensor, Category.assoc]

/-- An algebra-valued point as a tensor automorphism of finite-comodule scalar extension. -/
@[expose] noncomputable def fgPointTensorIso (g : WithConv (H →ₐ[R] A)) :
    FGComoduleCat.scalarExtensionMonoidalFunctor R H A ≅
      FGComoduleCat.scalarExtensionMonoidalFunctor R H A := by
  exact @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _
    (fgPointNatIsoHom R H A g) (isMonoidal_fgPointNatIsoHom_hom R H A g)

/-- Forgetting tensor compatibility from the point automorphism recovers its underlying natural
automorphism. -/
@[simp]
theorem fgPointTensorIso_hom_hom (g : WithConv (H →ₐ[R] A)) :
    (fgPointTensorIso R H A g).hom.hom = (fgPointNatIsoHom R H A g).hom :=
  (rfl)

/-- Forgetting tensor compatibility from the inverse point automorphism recovers the inverse
underlying natural automorphism. -/
@[simp]
theorem fgPointTensorIso_inv_hom (g : WithConv (H →ₐ[R] A)) :
    (fgPointTensorIso R H A g).inv.hom = (fgPointNatIsoHom R H A g).inv :=
  rfl

/-- Algebra-valued points act on finite-comodule scalar extension by tensor automorphisms. -/
@[expose] noncomputable def fgPointTensorIsoHom :
    WithConv (H →ₐ[R] A) →*
      Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A) where
  toFun := fgPointTensorIso R H A
  map_one' := by
    apply Aut.ext
    apply LaxMonoidalFunctor.hom_ext
    refine (fgPointTensorIso_hom_hom R H A 1).trans ?_
    exact (congrArg Iso.hom (map_one (fgPointNatIsoHom R H A))).trans (by rfl)
  map_mul' g h := by
    apply Aut.ext
    apply LaxMonoidalFunctor.hom_ext
    refine (fgPointTensorIso_hom_hom R H A (g * h)).trans ?_
    exact (congrArg Iso.hom (map_mul (fgPointNatIsoHom R H A) g h)).trans (by rfl)

/-- Evaluating the point tensor-action homomorphism gives the corresponding tensor
automorphism. -/
@[simp]
theorem fgPointTensorIsoHom_apply (g : WithConv (H →ₐ[R] A)) :
    fgPointTensorIsoHom R H A g = fgPointTensorIso R H A g :=
  rfl

end Generic

section

variable (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable (H : Type u) [Semiring H] [HopfAlgebra R H] [Module.Free R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- The tensor-automorphism action of points is faithful over a principal ideal domain when the
Hopf algebra is free as a module. -/
theorem fgPointTensorIsoHom_injective :
    Function.Injective (fgPointTensorIsoHom R H A) := by
  intro g h hgh
  apply fgPointNatIsoHom_injective R H A
  apply Iso.ext
  apply NatTrans.ext
  funext (M : FGComoduleCat.{u, u, u} R H)
  have hhom := congrArg LaxMonoidalFunctor.Hom.hom (congrArg Iso.hom hgh)
  simp only [fgPointTensorIsoHom_apply, fgPointTensorIso_hom_hom] at hhom
  exact congrArg (fun η ↦ η.app M) hhom

end

end TauCeti.Tannaka
