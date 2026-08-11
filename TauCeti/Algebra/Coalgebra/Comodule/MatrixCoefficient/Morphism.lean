/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
morphisms generate that regular subcomodule. This is the naturality bridge used in Tannakian
reconstruction: a natural transformation on finite comodules is determined on an arbitrary
object by its behavior on finite subcomodules of the regular comodule.

## Main declarations

* `TauCeti.Comodule.matrixCoefficientHom`: a matrix coefficient as a comodule morphism to the
  regular comodule.
* `TauCeti.Comodule.matrixCoefficientHomLinear`: linearity in the functional.
* `TauCeti.Comodule.matrixCoefficientHom_jointly_injective`: coefficient morphisms jointly
  separate vectors over a field.
* `TauCeti.Comodule.baseChange_matrixCoefficientHom_jointly_injective`: joint separation after
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
theorem matrixCoefficientHom_jointly_injective_of_dual_eval_injective
    (hdual : Function.Injective (Module.Dual.eval R M)) {m n : M}
    (h : ∀ φ : Module.Dual R M,
      matrixCoefficientHom (C := C) φ m = matrixCoefficientHom (C := C) φ n) :
    m = n := by
  apply hdual
  apply LinearMap.ext
  intro φ
  simpa using congrArg (Coalgebra.counit (R := R) (A := C)) (h φ)

/-- Over a field, matrix-coefficient morphisms to the regular comodule jointly separate
vectors. -/
theorem matrixCoefficientHom_jointly_injective {k : Type u} [Field k]
    {C : Type v} [AddCommMonoid C] [Module k C] [Coalgebra k C]
    {M : Type w} [AddCommMonoid M] [Module k M] [Comodule k C M]
    {m n : M}
    (h : ∀ φ : Module.Dual k M,
      matrixCoefficientHom (C := C) φ m = matrixCoefficientHom (C := C) φ n) :
    m = n := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup k
  let : Module.Free k M := Module.Free.of_divisionRing k M
  exact matrixCoefficientHom_jointly_injective_of_dual_eval_injective
    (Module.Free.chooseBasis k M).eval_injective h

section BaseChange

variable (A : Type x) [CommSemiring A] [Algebra R A]
variable [Module.Free R M]

private theorem baseChangeDual_jointly_injective {x y : A ⊗[R] M}
    (h : ∀ φ : Module.Dual R M, φ.baseChange A x = φ.baseChange A y) : x = y := by
  let b := Module.Free.chooseBasis R M
  let ibc := TensorProduct.isBaseChange R M A
  let bA := ibc.basis b
  apply bA.ext_elem
  intro i
  have hcoord (z : A ⊗[R] M) :
      bA.repr z i = Module.Dual.baseChange A (b.coord i) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z w hz hw => simpa only [map_add, Finsupp.add_apply] using congrArg₂ (· + ·) hz hw
    | tmul a m =>
        calc
          bA.repr (a ⊗ₜ[R] m) i =
              bA.repr (a • (1 ⊗ₜ[R] m)) i := by simp [TensorProduct.smul_tmul']
          _ = a * bA.repr (1 ⊗ₜ[R] m) i := by simp
          _ = a * algebraMap R A (b.repr m i) := by
            simpa only [bA, ibc, TensorProduct.mk_apply] using congrArg (a * ·)
              (IsBaseChange.basis_repr_comp_apply b ibc m i)
          _ = Module.Dual.baseChange A (b.coord i) (a ⊗ₜ[R] m) := by
            simp [Module.Basis.coord_apply, Algebra.smul_def, mul_comm]
  rw [hcoord, hcoord]
  exact h (b.coord i)

omit [Module.Free R M] in
private theorem counit_baseChange_matrixCoefficientHom (φ : Module.Dual R M)
    (z : A ⊗[R] M) :
    (TensorProduct.AlgebraTensorModule.rid R A A)
        ((Coalgebra.counit (R := R) (A := C)).baseChange A
          ((matrixCoefficientHom (C := C) φ).toLinearMap.baseChange A z)) =
      φ.baseChange A z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add z w hz hw =>
      simp only [map_add]
      rw [hz, hw]
  | tmul a m => simp

/-- After extending scalars to a commutative algebra, the base changes of all
matrix-coefficient morphisms still jointly separate vectors. -/
theorem baseChange_matrixCoefficientHom_jointly_injective {x y : A ⊗[R] M}
    (h : ∀ φ : Module.Dual R M,
      (matrixCoefficientHom (C := C) φ).toLinearMap.baseChange A x =
        (matrixCoefficientHom (C := C) φ).toLinearMap.baseChange A y) :
    x = y := by
  apply baseChangeDual_jointly_injective A
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
