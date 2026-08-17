/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.Monoidal
public import TauCeti.LinearAlgebra.End.ScalarExtension

/-!
# Base change of tensor automorphisms of scalar extension

Let `H` be a Hopf algebra over a commutative semiring `R`, and let `f : A →ₐ[R] B` be a morphism
of commutative `R`-algebras. A tensor automorphism of scalar extension on the finite
`H`-comodules has, at each comodule `M`, an `A`-linear automorphism of `A ⊗[R] M`. Base changing
those components along `f` produces a tensor automorphism over `B`, and this is functorial in the
value algebra.

The construction first assembles an automorphism of the scalar-extension functor from an
arbitrary natural family of linear automorphisms, then adds the two monoidal conditions. The
base-changed family satisfies all three because base change of endomorphisms preserves
naturality, the identity, and the tensor comparison
(`TauCeti.Module.End.mapValue`).

Compatibility with the point action is `tensorAutMapValue_fgPointTensorIso`: pushing a point
forward along `f` and acting agrees with acting and then base changing the tensor automorphism.
Together with reconstruction this makes the Tannakian equivalence natural in the value algebra;
see `TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.GroupFunctor`.

## Main declarations

* `TauCeti.Tannaka.autOfComponents`: a natural family of linear automorphisms as an automorphism
  of the scalar-extension functor.
* `TauCeti.Tannaka.monoidalAutOfComponents`: the same, with the unit and tensor conditions, as a
  tensor automorphism.
* `TauCeti.Tannaka.tensorAutMapValue`: base change of tensor automorphisms along a morphism of
  value algebras.
* `TauCeti.Tannaka.rTensor_comp_scalarExtensionComponent`: the transport square characterizing
  the base-changed components.
* `TauCeti.Tannaka.tensorAutMapValue_fgPointTensorIso`: base change is compatible with the point
  action.

## References

* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u v

section Assembly

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [HopfAlgebra R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- A family of `A`-linear automorphisms of the scalar extensions of the finite comodules,
natural in the comodule, as an automorphism of the scalar-extension functor. -/
@[expose] noncomputable def autOfComponents
    (F : ∀ M : FGComoduleCat.{u, v, u} R H, LinearMap.GeneralLinearGroup A (A ⊗[R] M))
    (hnat : ∀ {M N : FGComoduleCat.{u, v, u} R H} (g : M ⟶ N),
      g.hom.toLinearMap.baseChange A ∘ₗ (F M : Module.End A (A ⊗[R] M)) =
        (F N : Module.End A (A ⊗[R] N)) ∘ₗ g.hom.toLinearMap.baseChange A) :
    Aut (FGComoduleCat.scalarExtensionFunctor R H A) :=
  NatIso.ofComponents
    (fun M ↦ (eqToIso (FGComoduleCat.scalarExtensionFunctor_obj R H A M)).trans
      ((F M).toLinearEquiv.toModuleIsoₛ.trans
        (eqToIso (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm)))
    (fun {M N} g ↦ by
      -- Reduce the bundled component isomorphism to its three transports, then cancel the
      -- outer ones against the transports in the functor's action on morphisms.
      change
        (FGComoduleCat.scalarExtensionFunctor R H A).map g ≫
            eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A N) ≫
              (F N).toLinearEquiv.toModuleIsoₛ.hom ≫
                eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A N).symm =
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M) ≫
              (F M).toLinearEquiv.toModuleIsoₛ.hom ≫
                eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm ≫
                  (FGComoduleCat.scalarExtensionFunctor R H A).map g
      rw [FGComoduleCat.scalarExtensionFunctor_map]
      simp only [Category.assoc]
      rw [cancel_epi]
      simp only [← Category.assoc]
      rw [cancel_mono]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
        LinearEquiv.toModuleIsoₛ_hom]
      apply SemimoduleCat.hom_ext
      exact (hnat g).symm)

/-- The component of the automorphism assembled from a natural family of linear automorphisms is
that family, transported to the object chosen by the scalar-extension functor. -/
@[simp]
theorem autOfComponents_hom_app
    (F : ∀ M : FGComoduleCat.{u, v, u} R H, LinearMap.GeneralLinearGroup A (A ⊗[R] M))
    (hnat : ∀ {M N : FGComoduleCat.{u, v, u} R H} (g : M ⟶ N),
      g.hom.toLinearMap.baseChange A ∘ₗ (F M : Module.End A (A ⊗[R] M)) =
        (F N : Module.End A (A ⊗[R] N)) ∘ₗ g.hom.toLinearMap.baseChange A)
    (M : FGComoduleCat.{u, v, u} R H) :
    (autOfComponents R H A F hnat).hom.app M =
      eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M) ≫
        (F M).toLinearEquiv.toModuleIsoₛ.hom ≫
          eqToHom (FGComoduleCat.scalarExtensionFunctor_obj R H A M).symm :=
  rfl

/-- A family of `A`-linear automorphisms of the scalar extensions of the finite comodules that is
natural in the comodule, preserves the tensor unit, and is compatible with the tensor comparison,
as a tensor automorphism of scalar extension. -/
@[expose] noncomputable def monoidalAutOfComponents
    (F : ∀ M : FGComoduleCat.{u, v, u} R H, LinearMap.GeneralLinearGroup A (A ⊗[R] M))
    (hnat : ∀ {M N : FGComoduleCat.{u, v, u} R H} (g : M ⟶ N),
      g.hom.toLinearMap.baseChange A ∘ₗ (F M : Module.End A (A ⊗[R] M)) =
        (F N : Module.End A (A ⊗[R] N)) ∘ₗ g.hom.toLinearMap.baseChange A)
    (hunit : F (𝟙_ (FGComoduleCat R H)) = 1)
    (htensor : ∀ M N : FGComoduleCat.{u, v, u} R H,
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap.comp
          (TensorProduct.map (F M : Module.End A (A ⊗[R] M))
            (F N : Module.End A (A ⊗[R] N))) =
        (F (M ⊗ N : FGComoduleCat R H) :
          Module.End A (A ⊗[R] ((M ⊗ N : FGComoduleCat R H) : Type u))).comp
            (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap) :
    Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A) :=
  @LaxMonoidalFunctor.isoMk _ _ _ _ _ _ _ _ (autOfComponents R H A F hnat)
    (isMonoidal_of_linear_components R H A F (autOfComponents R H A F hnat)
      (autOfComponents_hom_app R H A F hnat) hunit htensor)

/-- The transported component of the tensor automorphism assembled from a natural monoidal family
of linear automorphisms is that family. -/
@[simp]
theorem scalarExtensionComponent_monoidalAutOfComponents
    (F : ∀ M : FGComoduleCat.{u, v, u} R H, LinearMap.GeneralLinearGroup A (A ⊗[R] M))
    (hnat : ∀ {M N : FGComoduleCat.{u, v, u} R H} (g : M ⟶ N),
      g.hom.toLinearMap.baseChange A ∘ₗ (F M : Module.End A (A ⊗[R] M)) =
        (F N : Module.End A (A ⊗[R] N)) ∘ₗ g.hom.toLinearMap.baseChange A)
    (hunit : F (𝟙_ (FGComoduleCat R H)) = 1)
    (htensor : ∀ M N : FGComoduleCat.{u, v, u} R H,
      (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap.comp
          (TensorProduct.map (F M : Module.End A (A ⊗[R] M))
            (F N : Module.End A (A ⊗[R] N))) =
        (F (M ⊗ N : FGComoduleCat R H) :
          Module.End A (A ⊗[R] ((M ⊗ N : FGComoduleCat R H) : Type u))).comp
            (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap)
    (M : FGComoduleCat.{u, v, u} R H) :
    scalarExtensionComponent R H A (monoidalAutOfComponents R H A F hnat hunit htensor) M =
      (F M : Module.End A (A ⊗[R] M)) :=
  scalarExtensionComponent_eq_of_hom_app R H A M (F M) _ (autOfComponents_hom_app R H A F hnat M)

end Assembly

section BaseChange

variable (R : Type u) [CommSemiring R]
variable (H : Type v) [Semiring H] [HopfAlgebra R H]
variable (A : Type u) [CommSemiring A] [Algebra R A]
variable (B : Type u) [CommSemiring B] [Algebra R B]
variable (C : Type u) [CommSemiring C] [Algebra R C]

/-- The base-changed component family of a tensor automorphism is natural in the finite
comodule. -/
theorem baseChangeComponent_natural (f : A →ₐ[R] B)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    {M N : FGComoduleCat.{u, v, u} R H} (g : M ⟶ N) :
    g.hom.toLinearMap.baseChange B ∘ₗ
        (Module.End.mapValueGL f (scalarExtensionComponentGL R H A η M) :
          Module.End B (B ⊗[R] M)) =
      (Module.End.mapValueGL f (scalarExtensionComponentGL R H A η N) :
        Module.End B (B ⊗[R] N)) ∘ₗ g.hom.toLinearMap.baseChange B := by
  rw [Module.End.mapValueGL_coe, Module.End.mapValueGL_coe, scalarExtensionComponentGL_coe,
    scalarExtensionComponentGL_coe]
  exact Module.End.baseChange_comp_mapValue f g.hom.toLinearMap
    (scalarExtensionComponent R H A η M) (scalarExtensionComponent R H A η N)
    (scalarExtensionComponent_natural R H A η g)

/-- The base-changed component family of a tensor automorphism is the identity at the tensor
unit. -/
theorem baseChangeComponent_tensorUnit (f : A →ₐ[R] B)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) :
    Module.End.mapValueGL f
        (scalarExtensionComponentGL R H A η (𝟙_ (FGComoduleCat R H))) = 1 := by
  have h1 : scalarExtensionComponentGL R H A η (𝟙_ (FGComoduleCat R H)) = 1 := by
    apply Units.ext
    rw [scalarExtensionComponentGL_coe, scalarExtensionComponent_tensorUnit,
      ← Module.End.one_eq_id]
    rfl
  rw [h1, map_one]

/-- The base-changed component family of a tensor automorphism is compatible with the tensor
comparison of scalar extensions. -/
theorem baseChangeComponent_tensor (f : A →ₐ[R] B)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (M N : FGComoduleCat.{u, v, u} R H) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R B M N).symm.toLinearMap.comp
        (TensorProduct.map
          (Module.End.mapValueGL f (scalarExtensionComponentGL R H A η M) :
            Module.End B (B ⊗[R] M))
          (Module.End.mapValueGL f (scalarExtensionComponentGL R H A η N) :
            Module.End B (B ⊗[R] N))) =
      (Module.End.mapValueGL f
          (scalarExtensionComponentGL R H A η (M ⊗ N : FGComoduleCat R H)) :
        Module.End B (B ⊗[R] ((M ⊗ N : FGComoduleCat R H) : Type u))).comp
          (TensorProduct.AlgebraTensorModule.distribBaseChange R B M N).symm.toLinearMap := by
  rw [Module.End.mapValueGL_coe, Module.End.mapValueGL_coe, Module.End.mapValueGL_coe,
    scalarExtensionComponentGL_coe, scalarExtensionComponentGL_coe,
    scalarExtensionComponentGL_coe]
  exact Module.End.distribBaseChange_comp_mapValue f (scalarExtensionComponent R H A η M)
    (scalarExtensionComponent R H A η N)
    (scalarExtensionComponent R H A η (M ⊗ N : FGComoduleCat R H))
    (distribBaseChange_comp_scalarExtensionComponent R H A η M N)

/-- Base change of a tensor automorphism of finite-comodule scalar extension along a morphism of
value algebras: base change each transported component. -/
@[expose] noncomputable def tensorAutMapValue (f : A →ₐ[R] B)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) :
    Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H B) :=
  monoidalAutOfComponents R H B
    (fun M ↦ Module.End.mapValueGL f (scalarExtensionComponentGL R H A η M))
    (fun {_ _} g ↦ baseChangeComponent_natural R H A B f η g)
    (baseChangeComponent_tensorUnit R H A B f η)
    (baseChangeComponent_tensor R H A B f η)

/-- The transported component of a base-changed tensor automorphism is the base change of the
transported component. -/
@[simp]
theorem scalarExtensionComponent_tensorAutMapValue (f : A →ₐ[R] B)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (M : FGComoduleCat.{u, v, u} R H) :
    scalarExtensionComponent R H B (tensorAutMapValue R H A B f η) M =
      Module.End.mapValue f (scalarExtensionComponent R H A η M) := by
  rw [tensorAutMapValue, scalarExtensionComponent_monoidalAutOfComponents,
    Module.End.mapValueGL_coe, scalarExtensionComponentGL_coe]

/-- Base change of tensor automorphisms along a morphism of value algebras, as a group
homomorphism. -/
@[expose] noncomputable def tensorAutMapValueHom (f : A →ₐ[R] B) :
    Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A) →*
      Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H B) where
  toFun := tensorAutMapValue R H A B f
  map_one' := by
    apply scalarExtensionComponent_ext
    intro M
    rw [scalarExtensionComponent_tensorAutMapValue, scalarExtensionComponent_one,
      scalarExtensionComponent_one, ← Module.End.one_eq_id, Module.End.mapValue_one,
      Module.End.one_eq_id]
  map_mul' η θ := by
    apply scalarExtensionComponent_ext
    intro M
    rw [scalarExtensionComponent_tensorAutMapValue, scalarExtensionComponent_mul,
      scalarExtensionComponent_mul, scalarExtensionComponent_tensorAutMapValue,
      scalarExtensionComponent_tensorAutMapValue, ← Module.End.mul_eq_comp,
      ← Module.End.mul_eq_comp, Module.End.mapValue_mul]

/-- The bundled base-change homomorphism acts by `tensorAutMapValue`. -/
@[simp]
theorem tensorAutMapValueHom_apply (f : A →ₐ[R] B)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) :
    tensorAutMapValueHom R H A B f η = tensorAutMapValue R H A B f η :=
  rfl

/-- The transport square characterizing the components of a base-changed tensor automorphism:
they are compatible with the original components along the comparison of scalar extensions. -/
theorem rTensor_comp_scalarExtensionComponent (f : A →ₐ[R] B)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A))
    (M : FGComoduleCat.{u, v, u} R H) :
    (scalarExtensionComponent R H B (tensorAutMapValue R H A B f η) M).restrictScalars R ∘ₗ
        LinearMap.rTensor M f.toLinearMap =
      LinearMap.rTensor M f.toLinearMap ∘ₗ
        (scalarExtensionComponent R H A η M).restrictScalars R := by
  rw [scalarExtensionComponent_tensorAutMapValue]
  exact Module.End.mapValue_comp_rTensor f (scalarExtensionComponent R H A η M)

/-- Base change along the identity morphism of value algebras is the identity. -/
@[simp]
theorem tensorAutMapValue_id
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) :
    tensorAutMapValue R H A A (AlgHom.id R A) η = η := by
  apply scalarExtensionComponent_ext
  intro M
  rw [scalarExtensionComponent_tensorAutMapValue, Module.End.mapValue_id]

/-- Base change along a composite of morphisms of value algebras is the composite of base
changes. -/
theorem tensorAutMapValue_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H A)) :
    tensorAutMapValue R H A C (g.comp f) η =
      tensorAutMapValue R H B C g (tensorAutMapValue R H A B f η) := by
  apply scalarExtensionComponent_ext
  intro M
  rw [scalarExtensionComponent_tensorAutMapValue, scalarExtensionComponent_tensorAutMapValue,
    scalarExtensionComponent_tensorAutMapValue, Module.End.mapValue_comp]

/-- Base change of tensor automorphisms is compatible with the point action: pushing an
algebra-valued point forward along `f` and acting agrees with acting and then base changing. -/
@[simp]
theorem tensorAutMapValue_fgPointTensorIso (f : A →ₐ[R] B) (g : WithConv (H →ₐ[R] A)) :
    tensorAutMapValue R H A B f (fgPointTensorIso R H A g) =
      fgPointTensorIso R H B (AlgHom.mapValue f g) := by
  apply scalarExtensionComponent_ext
  intro M
  -- The point automorphism is presented as an isomorphism rather than as an element of `Aut`,
  -- so instantiate the component formula for it explicitly before rewriting.
  have hbase := scalarExtensionComponent_tensorAutMapValue R H A B f (fgPointTensorIso R H A g) M
  rw [hbase, scalarExtensionComponent_fgPointTensorIso, scalarExtensionComponent_fgPointTensorIso,
    Comodule.pointsAction_toLinearMap, Comodule.pointsAction_toLinearMap]
  refine (Module.End.eq_mapValue f (Comodule.endOfPoint (M : Type u) g.ofConv) _ ?_).symm
  simpa only [AlgHom.mapValue_apply, WithConv.ofConv_toConv] using
    (Comodule.rTensor_comp_endOfPoint (M : Type u) f g.ofConv).symm

end BaseChange

end TauCeti.Tannaka
