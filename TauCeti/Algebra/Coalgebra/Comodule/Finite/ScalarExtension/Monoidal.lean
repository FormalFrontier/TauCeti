/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.Monoidal
public import TauCeti.Algebra.Coalgebra.Comodule.Finite.ScalarExtension.Basic

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
* `TauCeti.FGComoduleCat.scalarExtensionMonoidalFunctor`: scalar extension bundled as a lax
  monoidal functor.
* `TauCeti.FGComoduleCat.scalarExtensionFunctor_μ`: the tensorator formula.
* `TauCeti.FGComoduleCat.scalarExtensionFunctor_ε`: the unit-comparison formula.
* `TauCeti.FGComoduleCat.scalarExtensionFunctor_δ`: the inverse tensorator formula.
* `TauCeti.FGComoduleCat.scalarExtensionFunctor_η`: the inverse unit-comparison formula.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.FGComoduleCat

universe u v

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [Bialgebra R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- Evaluation of the two base-change composites in the associativity coherence law. -/
private theorem scalarExtension_associativity_tmul
    (M N P : FGComoduleCat.{u, v, u} R H) (m : M) (n : N) (p : P) :
    (α_ (SemimoduleCat.of A (A ⊗[R] M))
      (SemimoduleCat.of A (A ⊗[R] N))
      (SemimoduleCat.of A (A ⊗[R] P))).hom
        (((SemimoduleCat.ofHom
          (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).toLinearMap) ▷
            SemimoduleCat.of A (A ⊗[R] P))
          (SemimoduleCat.ofHom
            (TensorProduct.AlgebraTensorModule.distribBaseChange R A (M ⊗ N) P).toLinearMap
              ((1 : A) ⊗ₜ[R] ((m ⊗ₜ[R] n) ⊗ₜ[R] p)))) =
      (SemimoduleCat.of A (A ⊗[R] M) ◁ SemimoduleCat.ofHom
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A N P).toLinearMap)
        (SemimoduleCat.ofHom
          (TensorProduct.AlgebraTensorModule.distribBaseChange R A M (N ⊗ P)).toLinearMap
            (SemimoduleCat.ofHom
              ((TensorProduct.assoc R M N P).toLinearMap.baseChange A)
                ((1 : A) ⊗ₜ[R] ((m ⊗ₜ[R] n) ⊗ₜ[R] p)))) := rfl

/-- Two maps out of a base-changed module agree as soon as they agree on the pure tensors
`1 ⊗ₜ m`. -/
private theorem baseChange_hom_ext {M : Type u} [AddCommMonoid M] [Module R M]
    {N : SemimoduleCat.{u} A} {f g : SemimoduleCat.of A (A ⊗[R] M) ⟶ N}
    (h : ∀ m, f (1 ⊗ₜ[R] m) = g (1 ⊗ₜ[R] m)) : f = g := by
  let _ : Module R N := Module.compHom N (algebraMap R A)
  let _ : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  apply SemimoduleCat.hom_ext
  apply (LinearMap.liftBaseChangeEquiv A).symm.injective
  apply LinearMap.ext
  intro m
  simpa using h m

/-- Two maps out of a base-changed tensor product agree as soon as they agree on the pure
tensors `1 ⊗ₜ (m ⊗ₜ n)`. -/
private theorem baseChange_tensor_hom_ext {M N : SemimoduleCat.{u} R} {P : SemimoduleCat.{u} A}
    {f g : SemimoduleCat.of A (A ⊗[R] (M ⊗[R] N)) ⟶ P}
    (h : ∀ m n, f (1 ⊗ₜ[R] (m ⊗ₜ[R] n)) = g (1 ⊗ₜ[R] (m ⊗ₜ[R] n))) : f = g := by
  let _ : Module R P := Module.compHom P (algebraMap R A)
  let _ : IsScalarTower R A P := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  apply SemimoduleCat.hom_ext
  apply (LinearMap.liftBaseChangeEquiv A).symm.injective
  apply TensorProduct.ext
  ext m n
  simpa only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
    LinearMap.liftBaseChangeEquiv_symm_apply] using h m n

/-- Two maps out of a base-changed triple tensor product agree as soon as they agree on the pure
tensors `1 ⊗ₜ ((m ⊗ₜ n) ⊗ₜ p)`. -/
private theorem baseChange_tensor₃_hom_ext {M N P : SemimoduleCat.{u} R}
    {Q : SemimoduleCat.{u} A}
    {f g : SemimoduleCat.of A (A ⊗[R] ((M ⊗[R] N) ⊗[R] P)) ⟶ Q}
    (h : ∀ m n p, f (1 ⊗ₜ[R] ((m ⊗ₜ[R] n) ⊗ₜ[R] p)) =
      g (1 ⊗ₜ[R] ((m ⊗ₜ[R] n) ⊗ₜ[R] p))) : f = g := by
  let _ : Module R Q := Module.compHom Q (algebraMap R A)
  let _ : IsScalarTower R A Q := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  apply SemimoduleCat.hom_ext
  apply (LinearMap.liftBaseChangeEquiv A).symm.injective
  exact TensorProduct.ext_threefold fun m n p ↦ by
    simpa only [LinearMap.liftBaseChangeEquiv_symm_apply] using h m n p

/-- Scalar extension from finitely generated comodules to semimodules is strong monoidal. -/
noncomputable instance instMonoidalScalarExtensionFunctor :
    (scalarExtensionFunctor.{u, v, u, u} R H A).Monoidal := by
  let model : FGComoduleCat.{u, v, u} R H ⥤ SemimoduleCat.{u} A :=
    { obj := fun M ↦ SemimoduleCat.of A (A ⊗[R] M)
      map := fun f ↦ SemimoduleCat.ofHom (f.hom.toLinearMap.baseChange A)
      map_id := fun _ ↦ SemimoduleCat.hom_ext LinearMap.baseChange_id
      map_comp := fun f g ↦
        SemimoduleCat.hom_ext (LinearMap.baseChange_comp f.hom.toLinearMap g.hom.toLinearMap) }
  let modelMonoidal : model.Monoidal := Functor.CoreMonoidal.toMonoidal
    (.mk'
      (εIso := (TensorProduct.AlgebraTensorModule.rid R A A).symm.toModuleIsoₛ)
      (μIso := fun M N ↦
        (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toModuleIsoₛ)
      (μIso_inv_natural_left := fun {M M'} f N ↦ by
        apply baseChange_tensor_hom_ext
        intro m n
        rfl)
      (μIso_inv_natural_right := fun {N N'} M f ↦ by
        apply baseChange_tensor_hom_ext
        intro m n
        rfl)
      (oplax_associativity := fun M N P ↦ by
        -- `model` is local construction data, and the source monoidal product is bundled.
        -- Expose that carrier identification once, then use the evaluation lemma above.
        change
          SemimoduleCat.ofHom
                (TensorProduct.AlgebraTensorModule.distribBaseChange R A (M ⊗ N) P).toLinearMap ≫
              (SemimoduleCat.ofHom
                    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).toLinearMap ▷
                SemimoduleCat.of A (A ⊗[R] P)) ≫
                (α_ (SemimoduleCat.of A (A ⊗[R] M))
                  (SemimoduleCat.of A (A ⊗[R] N))
                  (SemimoduleCat.of A (A ⊗[R] P))).hom =
            SemimoduleCat.ofHom ((α_ M N P).hom.hom.toLinearMap.baseChange A) ≫
              SemimoduleCat.ofHom
                  (TensorProduct.AlgebraTensorModule.distribBaseChange R A M (N ⊗ P)).toLinearMap ≫
                (SemimoduleCat.of A (A ⊗[R] M) ◁ SemimoduleCat.ofHom
                  (TensorProduct.AlgebraTensorModule.distribBaseChange R A N P).toLinearMap)
        apply baseChange_tensor₃_hom_ext
        intro m n p
        erw [SemimoduleCat.comp_apply, SemimoduleCat.comp_apply,
          SemimoduleCat.comp_apply, SemimoduleCat.comp_apply]
        rw [FGComoduleCat.associator_hom_toLinearMap]
        exact scalarExtension_associativity_tmul R H A M N P m n p)
      (oplax_left_unitality := fun M ↦ by
        apply baseChange_hom_ext
        intro m
        rw [SemimoduleCat.MonoidalCategory.leftUnitor_inv_apply,
          SemimoduleCat.comp_apply, SemimoduleCat.comp_apply,
          SemimoduleCat.ofHom_apply,
          LinearMap.baseChange_tmul, FGComoduleCat.leftUnitor_inv_toLinearMap]
        erw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          SemimoduleCat.MonoidalCategory.whiskerRight_apply,
          TensorProduct.AlgebraTensorModule.rid_tmul]
        rw [one_smul])
      (oplax_right_unitality := fun M ↦ by
        apply baseChange_hom_ext
        intro m
        rw [SemimoduleCat.MonoidalCategory.rightUnitor_inv_apply,
          SemimoduleCat.comp_apply, SemimoduleCat.comp_apply,
          SemimoduleCat.ofHom_apply,
          LinearMap.baseChange_tmul, FGComoduleCat.rightUnitor_inv_toLinearMap]
        erw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
          SemimoduleCat.MonoidalCategory.whiskerLeft_apply,
          TensorProduct.AlgebraTensorModule.rid_tmul]
        rw [one_smul]))
  letI := modelMonoidal
  exact Functor.Monoidal.transport
    (show model ≅ scalarExtensionFunctor R H A from
      NatIso.ofComponents
        (fun M ↦ (eqToIso (scalarExtensionFunctor_obj R H A M)).symm)
        (fun {M N} f ↦ by
          rw [scalarExtensionFunctor_map]
          simp [model]))

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The scalar-extension functor on finite comodules, bundled as a lax monoidal functor. -/
@[expose] noncomputable def scalarExtensionMonoidalFunctor :
    LaxMonoidalFunctor (FGComoduleCat.{u, v, u} R H) (SemimoduleCat.{u} A) :=
  LaxMonoidalFunctor.of (scalarExtensionFunctor R H A)

/-- The underlying functor of bundled monoidal scalar extension is scalar extension. -/
@[simp]
theorem scalarExtensionMonoidalFunctor_toFunctor :
    (scalarExtensionMonoidalFunctor R H A).toFunctor = scalarExtensionFunctor R H A := by
  rfl

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

/-- Formula for the inverse tensorator of finite-comodule scalar extension. -/
theorem scalarExtensionFunctor_δ (M N : FGComoduleCat.{u, v, u} R H) :
    δ (scalarExtensionFunctor R H A) M N =
      eqToHom (scalarExtensionFunctor_obj R H A (M ⊗ N)) ≫
        SemimoduleCat.ofHom
          (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).toLinearMap ≫
          (eqToHom (scalarExtensionFunctor_obj R H A M).symm ⊗ₘ
            eqToHom (scalarExtensionFunctor_obj R H A N).symm) := rfl

/-- Formula for the inverse unit comparison of finite-comodule scalar extension. -/
theorem scalarExtensionFunctor_η :
    η (scalarExtensionFunctor.{u, v, u, u} R H A) =
      eqToHom (scalarExtensionFunctor_obj R H A (𝟙_ (FGComoduleCat R H))) ≫
        SemimoduleCat.ofHom
          (TensorProduct.AlgebraTensorModule.rid R A A).toLinearMap := rfl

end TauCeti.FGComoduleCat
