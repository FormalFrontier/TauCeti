/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change of endomorphisms of a scalar extension

Let `M` be a module over a commutative semiring `R`, and let `f : A →ₐ[R] B` be a morphism of
commutative `R`-algebras. Scalar extension of `M` is compared by the `f`-semilinear map

```text
LinearMap.rTensor M f.toLinearMap : A ⊗[R] M → B ⊗[R] M.
```

An `A`-linear endomorphism of `A ⊗[R] M` transports along this comparison to a unique
`B`-linear endomorphism of `B ⊗[R] M`. This file constructs that transport, `mapValue`, proves
that the transport square characterizes it, and records that it is additive and multiplicative
in the endomorphism, and functorial in the value algebra. It also transports the two
compatibilities needed for monoidal arguments: naturality in `M` and the tensor comparison
`(A ⊗ M) ⊗[A] (A ⊗ N) ≃ A ⊗ (M ⊗ N)`.

The name follows `TauCeti.AlgHom.mapValue`, which transports an algebra-valued point along a
morphism of value algebras; the two are compatible in
`TauCeti.Comodule.rTensor_comp_endOfPoint`.

## Main declarations

* `TauCeti.rTensor_algHom_smul`: the comparison map is semilinear over `f`.
* `Module.End.mapValue`: the transported endomorphism.
* `Module.End.mapValue_comp_rTensor`: the defining transport square.
* `Module.End.eq_mapValue`: the transport square characterizes the transport.
* `Module.End.mapValueRingHom`: the transport as a ring homomorphism.
* `Module.End.mapValueGL`: the transport on general linear groups.
* `Module.End.baseChange_comp_mapValue`: transport preserves naturality in the module.
* `Module.End.distribBaseChange_comp_mapValue`: transport preserves the tensor
  comparison.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R A B C M N : Type*} [CommSemiring R]
variable [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]
variable [CommSemiring C] [Algebra R C]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- The comparison `A ⊗[R] M → B ⊗[R] M` of scalar extensions induced by a morphism `f` of
value algebras is semilinear over `f`. -/
theorem rTensor_algHom_smul (f : A →ₐ[R] B) (a : A) (z : A ⊗[R] M) :
    LinearMap.rTensor M f.toLinearMap (a • z) =
      f a • LinearMap.rTensor M f.toLinearMap z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x m => simp [TensorProduct.smul_tmul', smul_eq_mul, map_mul]
  | add x y hx hy => simp [smul_add, hx, hy]

/-- On pure tensors, the comparison maps of scalar extensions intertwine the tensor comparisons
`(A ⊗ M) ⊗[A] (A ⊗ N) ≃ A ⊗ (M ⊗ N)` for the two value algebras. -/
private theorem distribBaseChange_symm_rTensor_tmul
    (f : A →ₐ[R] B) (u : A ⊗[R] M) (v : A ⊗[R] N) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R B M N).symm
        (LinearMap.rTensor M f.toLinearMap u ⊗ₜ[B] LinearMap.rTensor N f.toLinearMap v) =
      LinearMap.rTensor (M ⊗[R] N) f.toLinearMap
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm (u ⊗ₜ[A] v)) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add u₁ u₂ hu₁ hu₂ =>
      simp only [map_add, TensorProduct.add_tmul, hu₁, hu₂]
  | tmul a m =>
      induction v using TensorProduct.induction_on with
      | zero => simp
      | add v₁ v₂ hv₁ hv₂ =>
          simp only [map_add, TensorProduct.tmul_add, hv₁, hv₂]
      | tmul b n =>
          simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply,
            TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, map_mul]

end TauCeti

namespace Module.End

open TauCeti

variable {R A B C M N : Type*} [CommSemiring R]
variable [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]
variable [CommSemiring C] [Algebra R C]
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/-- Base change of an endomorphism of a scalar extension along a morphism `f : A →ₐ[R] B` of
value algebras: the unique `B`-linear endomorphism of `B ⊗[R] M` compatible with `φ` along the
comparison map. -/
noncomputable def mapValue (f : A →ₐ[R] B) (φ : Module.End A (A ⊗[R] M)) :
    Module.End B (B ⊗[R] M) :=
  LinearMap.liftBaseChange B
    (LinearMap.rTensor M f.toLinearMap ∘ₗ φ.restrictScalars R ∘ₗ TensorProduct.mk R A M 1)

/-- Evaluation of a base-changed endomorphism on a pure tensor. -/
@[simp]
theorem mapValue_tmul (f : A →ₐ[R] B) (φ : Module.End A (A ⊗[R] M)) (b : B) (m : M) :
    mapValue f φ (b ⊗ₜ[R] m) = b • LinearMap.rTensor M f.toLinearMap (φ (1 ⊗ₜ[R] m)) := by
  simp [mapValue]

/-- The transport square defining base change of an endomorphism: transporting and then
comparing scalar extensions agrees with comparing and then applying the original
endomorphism. -/
theorem mapValue_comp_rTensor (f : A →ₐ[R] B) (φ : Module.End A (A ⊗[R] M)) :
    (mapValue f φ).restrictScalars R ∘ₗ LinearMap.rTensor M f.toLinearMap =
      LinearMap.rTensor M f.toLinearMap ∘ₗ φ.restrictScalars R := by
  refine TensorProduct.ext' fun a m ↦ ?_
  have hsmul : φ (a ⊗ₜ[R] m) = a • φ (1 ⊗ₜ[R] m) := by
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
    LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, mapValue_tmul, hsmul,
    rTensor_algHom_smul]

/-- Evaluation form of the transport square. -/
@[simp]
theorem mapValue_rTensor_apply (f : A →ₐ[R] B) (φ : Module.End A (A ⊗[R] M))
    (z : A ⊗[R] M) :
    mapValue f φ (LinearMap.rTensor M f.toLinearMap z) =
      LinearMap.rTensor M f.toLinearMap (φ z) :=
  LinearMap.congr_fun (mapValue_comp_rTensor f φ) z

/-- The transport square characterizes base change of an endomorphism: the comparison map
generates `B ⊗[R] M` over `B`. -/
theorem eq_mapValue (f : A →ₐ[R] B) (φ : Module.End A (A ⊗[R] M))
    (ψ : Module.End B (B ⊗[R] M))
    (h : ψ.restrictScalars R ∘ₗ LinearMap.rTensor M f.toLinearMap =
      LinearMap.rTensor M f.toLinearMap ∘ₗ φ.restrictScalars R) :
    ψ = mapValue f φ := by
  apply (LinearMap.liftBaseChangeEquiv B).symm.injective
  refine LinearMap.ext fun m ↦ ?_
  have hm := LinearMap.congr_fun h (1 ⊗ₜ[R] m)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
    LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, map_one] at hm
  simpa only [LinearMap.liftBaseChangeEquiv_symm_apply, mapValue_tmul, one_smul] using hm

/-- Base change preserves the identity endomorphism. -/
@[simp]
theorem mapValue_one (f : A →ₐ[R] B) :
    mapValue f (1 : Module.End A (A ⊗[R] M)) = 1 :=
  (eq_mapValue f 1 1 rfl).symm

/-- Base change is multiplicative: it turns composition into composition. -/
@[simp]
theorem mapValue_mul (f : A →ₐ[R] B) (φ ψ : Module.End A (A ⊗[R] M)) :
    mapValue f (φ * ψ) = mapValue f φ * mapValue f ψ := by
  refine (eq_mapValue f (φ * ψ) (mapValue f φ * mapValue f ψ) ?_).symm
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
    Module.End.mul_apply, mapValue_rTensor_apply]

/-- Base change preserves the zero endomorphism. -/
@[simp]
theorem mapValue_zero (f : A →ₐ[R] B) :
    mapValue f (0 : Module.End A (A ⊗[R] M)) = 0 := by
  refine (eq_mapValue f 0 0 ?_).symm
  simp

/-- Base change is additive. -/
@[simp]
theorem mapValue_add (f : A →ₐ[R] B) (φ ψ : Module.End A (A ⊗[R] M)) :
    mapValue f (φ + ψ) = mapValue f φ + mapValue f ψ := by
  refine (eq_mapValue f (φ + ψ) (mapValue f φ + mapValue f ψ) ?_).symm
  refine LinearMap.ext fun z ↦ ?_
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
    LinearMap.add_apply, mapValue_rTensor_apply, map_add]

/-- Base change of endomorphisms of a scalar extension, as a ring homomorphism. -/
noncomputable def mapValueRingHom (f : A →ₐ[R] B) :
    Module.End A (A ⊗[R] M) →+* Module.End B (B ⊗[R] M) where
  toFun := mapValue f
  map_one' := mapValue_one f
  map_mul' := mapValue_mul f
  map_zero' := mapValue_zero f
  map_add' := mapValue_add f

/-- The bundled base-change homomorphism acts by `mapValue`. -/
@[simp]
theorem mapValueRingHom_apply (f : A →ₐ[R] B) (φ : Module.End A (A ⊗[R] M)) :
    mapValueRingHom f φ = mapValue f φ := by
  simp [mapValueRingHom]

/-- Base change of automorphisms of a scalar extension, as a group homomorphism. -/
noncomputable def mapValueGL (f : A →ₐ[R] B) :
    LinearMap.GeneralLinearGroup A (A ⊗[R] M) →*
      LinearMap.GeneralLinearGroup B (B ⊗[R] M) :=
  Units.map (mapValueRingHom f).toMonoidHom

/-- The underlying endomorphism of a base-changed automorphism is the base-changed
endomorphism. -/
@[simp]
theorem mapValueGL_coe (f : A →ₐ[R] B) (φ : LinearMap.GeneralLinearGroup A (A ⊗[R] M)) :
    (mapValueGL f φ : Module.End B (B ⊗[R] M)) =
      mapValue f (φ : Module.End A (A ⊗[R] M)) := by
  simp [mapValueGL]

/-- Base change along the identity morphism of value algebras is the identity. -/
@[simp]
theorem mapValue_id (φ : Module.End A (A ⊗[R] M)) :
    mapValue (AlgHom.id R A) φ = φ := by
  refine (eq_mapValue (AlgHom.id R A) φ φ ?_).symm
  simp [LinearMap.rTensor_id]

/-- Base change along a composite of morphisms of value algebras is the composite of base
changes. -/
@[simp]
theorem mapValue_comp (f : A →ₐ[R] B) (g : B →ₐ[R] C) (φ : Module.End A (A ⊗[R] M)) :
    mapValue (g.comp f) φ = mapValue g (mapValue f φ) := by
  refine (eq_mapValue (g.comp f) φ (mapValue g (mapValue f φ)) ?_).symm
  refine LinearMap.ext fun z ↦ ?_
  have hrt : LinearMap.rTensor M (g.comp f).toLinearMap =
      LinearMap.rTensor M g.toLinearMap ∘ₗ LinearMap.rTensor M f.toLinearMap := by
    rw [AlgHom.comp_toLinearMap, LinearMap.rTensor_comp]
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply, hrt,
    mapValue_rTensor_apply]

/-- Base change preserves naturality in the module: a square over `A` transports to the
corresponding square over `B`. -/
theorem baseChange_comp_mapValue (f : A →ₐ[R] B) (u : M →ₗ[R] N)
    (φ : Module.End A (A ⊗[R] M)) (ψ : Module.End A (A ⊗[R] N))
    (h : u.baseChange A ∘ₗ φ = ψ ∘ₗ u.baseChange A) :
    u.baseChange B ∘ₗ mapValue f φ = mapValue f ψ ∘ₗ u.baseChange B := by
  apply (LinearMap.liftBaseChangeEquiv B).symm.injective
  refine LinearMap.ext fun m ↦ ?_
  have hm := LinearMap.congr_fun h (1 ⊗ₜ[R] m)
  simp only [LinearMap.liftBaseChangeEquiv_symm_apply, LinearMap.coe_comp, Function.comp_apply,
    mapValue_tmul, one_smul, LinearMap.baseChange_tmul] at hm ⊢
  rw [← LinearMap.rTensor_baseChange, hm]

/-- Base change preserves the tensor comparison: a tensor-compatibility square over `A`
transports to the corresponding square over `B`. -/
theorem distribBaseChange_comp_mapValue (f : A →ₐ[R] B)
    (φ : Module.End A (A ⊗[R] M)) (ψ : Module.End A (A ⊗[R] N))
    (χ : Module.End A (A ⊗[R] (M ⊗[R] N)))
    (h : (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap ∘ₗ
        TensorProduct.map φ ψ =
      χ ∘ₗ (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R B M N).symm.toLinearMap ∘ₗ
        TensorProduct.map (mapValue f φ) (mapValue f ψ) =
      mapValue f χ ∘ₗ
        (TensorProduct.AlgebraTensorModule.distribBaseChange R B M N).symm.toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro x y
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
      simp only [TensorProduct.add_tmul, map_add, hx₁, hx₂]
  | tmul b m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ hy₁ hy₂ =>
          simp only [TensorProduct.tmul_add, map_add, hy₁, hy₂]
      | tmul c n =>
          have hmn := LinearMap.congr_fun h
            (((1 : A) ⊗ₜ[R] m) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] n))
          simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
            LinearEquiv.coe_coe,
            TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul, one_mul] at hmn
          simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
            LinearEquiv.coe_coe, mapValue_tmul,
            TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
          rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul, map_smul,
            distribBaseChange_symm_rTensor_tmul, hmn]

end Module.End
