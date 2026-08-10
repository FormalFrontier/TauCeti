/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Monoidal
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.ScalarExtension
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Monoidal scalar extension of finite comodules

For a commutative `R`-algebra `A`, scalar extension from finitely generated comodules to
`A`-semimodules is a strong monoidal functor. Its tensorator is inverse base-change
distributivity and its unit comparison is `A ≃ A ⊗[R] R`.

The construction follows Mathlib's monoidal structure on `ModuleCat.extendScalars` in
`Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction`, adapted to semimodules and the finite
comodule source category.

## Main declarations

* `TauCeti.FGComoduleCat.instMonoidalScalarExtensionFunctor`: scalar extension is monoidal.
* `TauCeti.FGComoduleCat.scalarExtensionFunctor_μ`: the tensorator formula.
* `TauCeti.FGComoduleCat.scalarExtensionFunctor_ε`: the unit-comparison formula.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.FGComoduleCat

universe u v

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [Bialgebra R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- The explicit objectwise model used to construct monoidal scalar extension. -/
noncomputable abbrev scalarExtensionModel :
    FGComoduleCat.{u, v, u} R H ⥤ SemimoduleCat.{u} A where
  obj M := SemimoduleCat.of A (A ⊗[R] M)
  map f := SemimoduleCat.ofHom (f.hom.toLinearMap.baseChange A)
  map_id _ := SemimoduleCat.hom_ext LinearMap.baseChange_id
  map_comp f g :=
    SemimoduleCat.hom_ext (LinearMap.baseChange_comp f.hom.toLinearMap g.hom.toLinearMap)

private theorem scalarExtension_associativity_tmul
    (M N P : FGComoduleCat.{u, v, u} R H) (a : A) (m : M) (n : N) (p : P) :
    (α_ (SemimoduleCat.of A (A ⊗[R] M))
      (SemimoduleCat.of A (A ⊗[R] N))
      (SemimoduleCat.of A (A ⊗[R] P))).hom
        (((SemimoduleCat.ofHom
          (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).toLinearMap) ▷
            SemimoduleCat.of A (A ⊗[R] P))
          (TensorProduct.AlgebraTensorModule.distribBaseChange R A (M ⊗ N) P
            (a ⊗ₜ[R] ((m ⊗ₜ[R] n) ⊗ₜ[R] p)))) =
      ((SemimoduleCat.of A (A ⊗[R] M) ◁ SemimoduleCat.ofHom
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A N P).toLinearMap)
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A M (N ⊗ P)
          ((TensorProduct.assoc R M N P).toLinearMap.baseChange A
            (a ⊗ₜ[R] ((m ⊗ₜ[R] n) ⊗ₜ[R] p))))) := by
  simp only [LinearMap.baseChange_tmul,
    TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  change
    (α_ (SemimoduleCat.of A (A ⊗[R] M))
      (SemimoduleCat.of A (A ⊗[R] N))
      (SemimoduleCat.of A (A ⊗[R] P))).hom
        (((a ⊗ₜ[R] m) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] n)) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] p)) =
      (SemimoduleCat.of A (A ⊗[R] M) ◁ SemimoduleCat.ofHom
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A N P).toLinearMap)
        ((a ⊗ₜ[R] m) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] (n ⊗ₜ[R] p)))
  rw [SemimoduleCat.MonoidalCategory.associator_hom_apply,
    SemimoduleCat.MonoidalCategory.whiskerLeft_apply]
  change _ = (a ⊗ₜ[R] m) ⊗ₜ[A]
    TensorProduct.AlgebraTensorModule.distribBaseChange R A N P
      ((1 : A) ⊗ₜ[R] (n ⊗ₜ[R] p))
  rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
  rfl

/-- The standard base-change comparisons form a monoidal structure on the explicit model. -/
noncomputable abbrev scalarExtensionModelMonoidal :
    (scalarExtensionModel R H A).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    (.mk'
      (εIso := (TensorProduct.AlgebraTensorModule.rid R A A).symm.toModuleIsoₛ)
      (μIso := fun M N ↦
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toModuleIsoₛ)
      (μIso_inv_natural_left := fun {M M'} f N ↦ by
        apply SemimoduleCat.hom_ext
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | add x y hx hy => rw [map_add, map_add, hx, hy]
        | tmul a z =>
            induction z using TensorProduct.induction_on with
            | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
            | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
            | tmul m n => rfl)
      (μIso_inv_natural_right := fun {N N'} M f ↦ by
        apply SemimoduleCat.hom_ext
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | add x y hx hy => rw [map_add, map_add, hx, hy]
        | tmul a z =>
            induction z using TensorProduct.induction_on with
            | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
            | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
            | tmul m n => rfl)
      (oplax_associativity := fun M N P ↦ by
        apply SemimoduleCat.hom_ext
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | add x y hx hy => rw [map_add, map_add, hx, hy]
        | tmul a z =>
            induction z using TensorProduct.induction_on with
            | zero => rw [TensorProduct.tmul_zero, map_zero, map_zero]
            | add x y hx hy => rw [TensorProduct.tmul_add, map_add, map_add, hx, hy]
            | tmul z p =>
                induction z using TensorProduct.induction_on with
                | zero =>
                    rw [TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, map_zero]
                | add x y hx hy =>
                    rw [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, map_add, hx, hy]
                | tmul m n =>
                    simp only [scalarExtensionModel]
                    rw [SemimoduleCat.hom_comp, LinearMap.comp_apply,
                      SemimoduleCat.hom_comp, LinearMap.comp_apply,
                      SemimoduleCat.hom_comp, LinearMap.comp_apply,
                      SemimoduleCat.hom_comp, LinearMap.comp_apply,
                      FGComoduleCat.associator_hom_toLinearMap]
                    exact scalarExtension_associativity_tmul R H A M N P a m n p)
      (oplax_left_unitality := fun M ↦ by
        apply SemimoduleCat.hom_ext
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | add x y hx hy => rw [map_add, map_add, hx, hy]
        | tmul a m =>
            simp only [scalarExtensionModel]
            rw [SemimoduleCat.MonoidalCategory.leftUnitor_inv_apply,
              SemimoduleCat.comp_apply, SemimoduleCat.comp_apply]
            change _ =
              ((TensorProduct.AlgebraTensorModule.rid R A A).symm.toModuleIsoₛ.inv ▷
                SemimoduleCat.of A (A ⊗[R] M))
                ((TensorProduct.AlgebraTensorModule.distribBaseChange R A R M).symm.toModuleIsoₛ.inv
                  ((λ_ M).inv.hom.toLinearMap.baseChange A (a ⊗ₜ[R] m)))
            rw [LinearMap.baseChange_tmul, FGComoduleCat.leftUnitor_inv_toLinearMap]
            change _ =
              ((TensorProduct.AlgebraTensorModule.rid R A A).symm.toModuleIsoₛ.inv ▷
                SemimoduleCat.of A (A ⊗[R] M))
                (TensorProduct.AlgebraTensorModule.distribBaseChange R A R M
                  (a ⊗ₜ[R] (1 ⊗ₜ[R] m)))
            rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
              SemimoduleCat.MonoidalCategory.whiskerRight_apply]
            change _ = TensorProduct.AlgebraTensorModule.rid R A A (a ⊗ₜ[R] 1) ⊗ₜ[A]
              (1 ⊗ₜ[R] m)
            rw [TensorProduct.AlgebraTensorModule.rid_tmul, one_smul]
            exact calc
              _ = (1 : A) ⊗ₜ[A] (a • (1 ⊗ₜ[R] m)) :=
                congrArg (fun z : A ⊗[R] M ↦ (1 : A) ⊗ₜ[A] z)
                  (TensorProduct.tmul_eq_smul_one_tmul a m)
              _ = _ := by
                rw [TensorProduct.tmul_smul]
                change (a * 1) ⊗ₜ[A] (1 ⊗ₜ[R] m) = _
                rw [mul_one])
      (oplax_right_unitality := fun M ↦ by
        apply SemimoduleCat.hom_ext
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => rw [map_zero, map_zero]
        | add x y hx hy => rw [map_add, map_add, hx, hy]
        | tmul a m =>
            simp only [scalarExtensionModel]
            rw [SemimoduleCat.MonoidalCategory.rightUnitor_inv_apply,
              SemimoduleCat.comp_apply, SemimoduleCat.comp_apply]
            change _ =
              (SemimoduleCat.of A (A ⊗[R] M) ◁
                (TensorProduct.AlgebraTensorModule.rid R A A).symm.toModuleIsoₛ.inv)
                ((TensorProduct.AlgebraTensorModule.distribBaseChange R A M R).symm.toModuleIsoₛ.inv
                  ((ρ_ M).inv.hom.toLinearMap.baseChange A (a ⊗ₜ[R] m)))
            rw [LinearMap.baseChange_tmul, FGComoduleCat.rightUnitor_inv_toLinearMap]
            change _ =
              (SemimoduleCat.of A (A ⊗[R] M) ◁
                (TensorProduct.AlgebraTensorModule.rid R A A).symm.toModuleIsoₛ.inv)
                (TensorProduct.AlgebraTensorModule.distribBaseChange R A M R
                  (a ⊗ₜ[R] (m ⊗ₜ[R] 1)))
            rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
              SemimoduleCat.MonoidalCategory.whiskerLeft_apply]
            change _ = (a ⊗ₜ[R] m) ⊗ₜ[A]
              TensorProduct.AlgebraTensorModule.rid R A A (1 ⊗ₜ[R] 1)
            rw [TensorProduct.AlgebraTensorModule.rid_tmul, one_smul]))

attribute [instance] scalarExtensionModelMonoidal

/-- Scalar extension from finitely generated comodules to semimodules is strong monoidal. -/
noncomputable abbrev instMonoidalScalarExtensionFunctor :
    (scalarExtensionFunctor.{u, v, u, u} R H A).Monoidal :=
  Functor.Monoidal.transport
    (show scalarExtensionModel R H A ≅ scalarExtensionFunctor R H A from
      NatIso.ofComponents
        (fun M ↦ (eqToIso (scalarExtensionFunctor_obj R H A M)).symm)
        (fun {M N} f ↦ by
          rw [scalarExtensionFunctor_map]
          simp [scalarExtensionModel]))

attribute [instance] instMonoidalScalarExtensionFunctor

open Functor.LaxMonoidal

/-- Formula for the tensorator of finite-comodule scalar extension. -/
theorem scalarExtensionFunctor_μ (M N : FGComoduleCat.{u, v, u} R H) :
    μ (scalarExtensionFunctor R H A) M N =
      (eqToHom (scalarExtensionFunctor_obj R H A M) ⊗ₘ
          eqToHom (scalarExtensionFunctor_obj R H A N)) ≫
        SemimoduleCat.ofHom
          (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap ≫
          eqToHom (scalarExtensionFunctor_obj R H A (M ⊗ N)).symm := rfl

/-- Formula for the unit comparison of finite-comodule scalar extension. -/
theorem scalarExtensionFunctor_ε :
    ε (scalarExtensionFunctor.{u, v, u, u} R H A) =
      SemimoduleCat.ofHom
          (TensorProduct.AlgebraTensorModule.rid R A A).symm.toLinearMap ≫
        eqToHom (scalarExtensionFunctor_obj R H A (𝟙_ (FGComoduleCat R H))).symm := rfl

end TauCeti.FGComoduleCat
