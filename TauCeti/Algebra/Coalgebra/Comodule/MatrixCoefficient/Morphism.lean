/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Subcoalgebra
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.RegularSubcomodule
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
public import TauCeti.LinearAlgebra.Dual.BaseChange

/-!
# Matrix coefficients as regular-comodule morphisms

For a right comodule `M` over a coalgebra `C`, every linear functional `φ : M →ₗ[R] R`
defines a matrix-coefficient map

```text
m ↦ c(φ, m) : M → C.
```

The comultiplication formula for matrix coefficients says precisely that this is a morphism
from `M` to the regular right comodule `C`. Applying the counit recovers `φ`, so whenever the
linear dual separates vectors, these morphisms do too. For a free module, they continue to
separate vectors after extending scalars to any commutative algebra.

For a finite free comodule, every coefficient morphism lands in the finite coefficient
subcoalgebra, viewed as a regular subcomodule. Conversely, the ranges of all coefficient
morphisms generate that regular subcomodule. This supplies an intended downstream naturality
bridge for Tannakian reconstruction: for each finite comodule, naturality along these corestricted
maps compares its component with components on finite regular subcomodules, and joint separation
then recovers the original finite-comodule component.

## Main declarations

* `TauCeti.Comodule.matrixCoefficientHom`: a matrix coefficient as a comodule morphism to the
  regular comodule.
* `TauCeti.Comodule.matrixCoefficientHomLinear`: linearity in the functional.
* `TauCeti.Comodule.counit_baseChange_matrixCoefficientHom`: counit evaluation after scalar
  extension recovers the original functional.
* `TauCeti.Comodule.eq_of_matrixCoefficientHom_eq`: coefficient morphisms jointly separate
  vectors in a free module.
* `TauCeti.Comodule.eq_of_baseChange_matrixCoefficientHom_eq`: joint separation after
  scalar extension.
* `TauCeti.Comodule.matrixCoefficientSubcoalgebraHom`: corestriction to the finite coefficient
  subcoalgebra.
* `TauCeti.Comodule.iSup_range_matrixCoefficientHom_eq`: the ranges of the coefficient
  morphisms generate the coefficient subcoalgebra as a regular subcomodule.

## References

* M. Sweedler, *Hopf Algebras*, Chapter 2.
* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The matrix-coefficient map attached to a functional, as a morphism from the given
comodule to the regular right comodule. -/
def matrixCoefficientHom (φ : Module.Dual R M) : Hom R C M C where
  toLinearMap := matrixCoefficientLinear (R := R) (C := C) φ
  map_coact := by
    ext m
    exact (comul_matrixCoefficient (R := R) (C := C) φ m).symm

/-- The underlying linear map of a matrix-coefficient morphism is the corresponding
matrix-coefficient linear map. -/
@[simp]
theorem matrixCoefficientHom_toLinearMap (φ : Module.Dual R M) :
    (matrixCoefficientHom (C := C) φ).toLinearMap =
      matrixCoefficientLinear (R := R) (C := C) φ :=
  (rfl)

/-- Evaluating a matrix-coefficient morphism gives the corresponding matrix coefficient. -/
@[simp]
theorem matrixCoefficientHom_apply (φ : Module.Dual R M) (m : M) :
    matrixCoefficientHom (C := C) φ m =
      matrixCoefficient (R := R) (C := C) φ m :=
  (rfl)

/-- The zero functional gives the zero matrix-coefficient morphism. -/
@[simp]
theorem matrixCoefficientHom_zero :
    matrixCoefficientHom (C := C) (0 : Module.Dual R M) = 0 := by
  ext m
  simp

/-- Matrix-coefficient morphisms are additive in the functional. -/
@[simp]
theorem matrixCoefficientHom_add (φ ψ : Module.Dual R M) :
    matrixCoefficientHom (C := C) (φ + ψ) =
      matrixCoefficientHom (C := C) φ + matrixCoefficientHom (C := C) ψ := by
  ext m
  simp

/-- Matrix-coefficient morphisms commute with scalar multiplication of the functional. -/
@[simp]
theorem matrixCoefficientHom_smul (r : R) (φ : Module.Dual R M) :
    matrixCoefficientHom (C := C) (r • φ) = r • matrixCoefficientHom (C := C) φ := by
  ext m
  simp

/-- Matrix-coefficient morphisms depend linearly on the functional. -/
def matrixCoefficientHomLinear :
    Module.Dual R M →ₗ[R] Hom R C M C where
  toFun := matrixCoefficientHom (C := C)
  map_add' := matrixCoefficientHom_add (C := C)
  map_smul' := matrixCoefficientHom_smul (C := C)

/-- Applying the linear family of matrix-coefficient morphisms gives the morphism attached to
that functional. -/
@[simp]
theorem matrixCoefficientHomLinear_apply (φ : Module.Dual R M) :
    matrixCoefficientHomLinear (C := C) φ = matrixCoefficientHom (C := C) φ :=
  (rfl)

/-- Matrix-coefficient morphisms jointly separate vectors whenever the linear dual does. -/
theorem eq_of_matrixCoefficientHom_eq_of_dual_eval_injective
    {m n : M} (h : ∀ φ : Module.Dual R M,
      matrixCoefficientHom (C := C) φ m = matrixCoefficientHom (C := C) φ n)
    (hdual : Function.Injective (Module.Dual.eval R M)) :
    m = n := by
  apply hdual
  apply LinearMap.ext
  intro φ
  simpa using congrArg (Coalgebra.counit (R := R) (A := C)) (h φ)

/-- For a free module, matrix-coefficient morphisms to the regular comodule jointly separate
vectors. -/
theorem eq_of_matrixCoefficientHom_eq [Module.Free R M] {m n : M}
    (h : ∀ φ : Module.Dual R M,
      matrixCoefficientHom (C := C) φ m = matrixCoefficientHom (C := C) φ n) :
    m = n := by
  exact eq_of_matrixCoefficientHom_eq_of_dual_eval_injective
    h (Module.Free.chooseBasis R M).eval_injective

section BaseChange

variable (A : Type x) [CommSemiring A] [Algebra R A]
variable [Module.Free R M]

omit [Module.Free R M] in
/-- Applying the scalar-extended counit after a scalar-extended matrix-coefficient morphism
recovers the scalar extension of the original functional. -/
theorem counit_baseChange_matrixCoefficientHom (φ : Module.Dual R M)
    (z : A ⊗[R] M) :
    (TensorProduct.AlgebraTensorModule.rid R A A)
        ((Coalgebra.counit (R := R) (A := C)).baseChange A
          ((matrixCoefficientHom (C := C) φ).toLinearMap.baseChange A z)) =
      φ.baseChange A z := by
  have hcomp : Coalgebra.counit (R := R) (A := C) ∘ₗ
      (matrixCoefficientHom (C := C) φ).toLinearMap = φ := by
    ext m
    exact counit_matrixCoefficient (R := R) (C := C) φ m
  calc
    _ = (TensorProduct.AlgebraTensorModule.rid R A A)
        (((Coalgebra.counit (R := R) (A := C) ∘ₗ
          (matrixCoefficientHom (C := C) φ).toLinearMap).baseChange A) z) := by
      simp only [LinearMap.baseChange_comp, LinearMap.coe_comp, Function.comp_apply]
    _ = (TensorProduct.AlgebraTensorModule.rid R A A)
        (LinearMap.baseChange A φ z) := by rw [hcomp]
    _ = φ.baseChange A z := by
      simp only [Module.Dual.baseChange, LinearMap.compRight_apply,
        LinearMap.baseChangeHom_apply, LinearMap.coe_comp, Function.comp_apply,
        LinearEquiv.coe_coe]

/-- After extending scalars to a commutative algebra, the base changes of all
matrix-coefficient morphisms still jointly separate vectors. -/
theorem eq_of_baseChange_matrixCoefficientHom_eq {x y : A ⊗[R] M}
    (h : ∀ φ : Module.Dual R M,
      (matrixCoefficientHom (C := C) φ).toLinearMap.baseChange A x =
        (matrixCoefficientHom (C := C) φ).toLinearMap.baseChange A y) :
    x = y := by
  apply TauCeti.Module.Dual.eq_of_baseChange_eq (A := A)
  intro φ
  rw [← counit_baseChange_matrixCoefficientHom (C := C) A φ x,
    ← counit_baseChange_matrixCoefficientHom (C := C) A φ y, h φ]

end BaseChange

section Finite

variable [Module.Free R M] [Module.Finite R M]

section Corestrict

variable [Module.Flat R C]

/-- A matrix-coefficient morphism corestricted to the coefficient subcoalgebra, viewed as a
finite regular subcomodule. -/
noncomputable def matrixCoefficientSubcoalgebraHom (φ : Module.Dual R M) :
    Hom R C M
    (matrixCoefficientSubcoalgebra (R := R) (C := C) (M := M)).toRegularSubcomodule :=
  (matrixCoefficientHom (C := C) φ).codRestrict
    (matrixCoefficientSubcoalgebra (R := R) (C := C) (M := M)).toRegularSubcomodule
    (matrixCoefficient_mem_subcoalgebra (R := R) (C := C) φ)

/-- Including a corestricted coefficient morphism into the ambient regular comodule recovers
the original matrix-coefficient morphism. -/
@[simp]
theorem matrixCoefficientSubcoalgebraHom_apply_coe (φ : Module.Dual R M) (m : M) :
    (matrixCoefficientSubcoalgebraHom (C := C) φ m : C) =
      matrixCoefficientHom (C := C) φ m :=
  Hom.codRestrict_apply _ _ _ _

end Corestrict

/-- The range of every matrix-coefficient morphism lies in the coefficient subcoalgebra viewed
as a regular subcomodule. -/
theorem range_matrixCoefficientHom_le (φ : Module.Dual R M) :
    (matrixCoefficientHom (C := C) φ).range ≤
      (matrixCoefficientSubcoalgebra (R := R) (C := C) (M := M)).toRegularSubcomodule := by
  rw [Hom.range_le_iff]
  exact matrixCoefficient_mem_subcoalgebra (R := R) (C := C) φ

/-- The coefficient subcoalgebra, viewed as a regular subcomodule, is generated by the ranges
of all matrix-coefficient morphisms. -/
@[simp]
theorem iSup_range_matrixCoefficientHom_eq :
    (⨆ φ : Module.Dual R M, (matrixCoefficientHom (C := C) φ).range) =
      (matrixCoefficientSubcoalgebra (R := R) (C := C) (M := M)).toRegularSubcomodule := by
  have hsub :
      (⨆ φ : Module.Dual R M, (matrixCoefficientHom (C := C) φ).range).toSubmodule =
        (matrixCoefficientSubcoalgebra (R := R) (C := C) (M := M)).toSubmodule := by
    rw [Subcomodule.iSup_toSubmodule, matrixCoefficientSubcoalgebra_toSubmodule]
    simp_rw [Hom.range_toSubmodule, matrixCoefficientHom_toLinearMap]
    apply le_antisymm
    · apply iSup_le
      intro φ
      rintro _ ⟨m, rfl⟩
      exact matrixCoefficient_mem_submodule (R := R) (C := C) φ m
    · apply matrixCoefficientSubmodule_le (R := R) (C := C) (M := M)
      intro φ m
      have hrange : LinearMap.range (matrixCoefficientLinear (R := R) (C := C) φ) ≤
          ⨆ ψ : Module.Dual R M,
            LinearMap.range (matrixCoefficientLinear (R := R) (C := C) ψ) :=
        le_iSup (fun ψ : Module.Dual R M =>
          LinearMap.range (matrixCoefficientLinear (R := R) (C := C) ψ)) φ
      exact hrange (LinearMap.mem_range_self
        (matrixCoefficientLinear (R := R) (C := C) φ) m)
  apply SetLike.ext
  intro c
  rw [← Subcomodule.mem_toSubmodule, ← Subcomodule.mem_toSubmodule,
    TauCeti.Subcoalgebra.toRegularSubcomodule_toSubmodule, hsub]

end Finite

end TauCeti.Comodule
