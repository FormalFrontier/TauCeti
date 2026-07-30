/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Basic

/-!
# The coefficient subcoalgebra of a finite free comodule

The comultiplication of a matrix coefficient is controlled by the coaction:

```text
Δ(c(φ, m)) = (c(φ, ·) ⊗ id)(ρ(m)).
```

For a finite basis `(eᵢ)`, expanding the coaction in that basis gives the familiar formula

```text
Δ(c(φ, m)) = ∑ i, c(φ, eᵢ) ⊗ c(eⁱ, m).
```

Consequently, over a commutative semiring, the matrix-coefficient submodule of a finite free
comodule is stable under comultiplication and hence defines a subcoalgebra.

## Main declarations

* `TauCeti.Comodule.comul_matrixCoefficient`: the basis-free comultiplication formula.
* `TauCeti.Comodule.comul_matrixCoefficient_eq_sum`: its expansion in a finite basis.
* `TauCeti.Comodule.matrixCoefficientSubcoalgebra`: the coefficient subcoalgebra of a finite
  free comodule.

## References

This is the standard coefficient-coalgebra construction; see Sweedler, *Hopf Algebras*,
Chapter 2.
-/

public section

open scoped TensorProduct
open TensorProduct Module

namespace TauCeti.Comodule

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

private def applyFirst (φ : Module.Dual R M) :
    M ⊗[R] (C ⊗[R] C) →ₗ[R] C ⊗[R] C :=
  (TensorProduct.lid R (C ⊗[R] C)).toLinearMap.comp
    (TensorProduct.map φ LinearMap.id)

omit [Comodule R C M] in
private theorem applyFirst_comul_lTensor (φ : Module.Dual R M) (x : M ⊗[R] C) :
    applyFirst (C := C) φ (Coalgebra.comul.lTensor M x) =
      Coalgebra.comul
        (TensorProduct.lid R C (TensorProduct.map φ LinearMap.id x)) := by
  induction x with
  | zero => simp [applyFirst]
  | tmul m c => simp [applyFirst]
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

omit [Coalgebra R C] [Comodule R C M] in
private theorem applyFirst_assoc_tmul (φ : Module.Dual R M) (x : M ⊗[R] C) (c : C) :
    applyFirst (C := C) φ
        (TensorProduct.assoc R M C C (x ⊗ₜ[R] c)) =
      TensorProduct.lid R C (TensorProduct.map φ LinearMap.id x) ⊗ₜ[R] c := by
  induction x with
  | zero => simp [applyFirst]
  | tmul m d => simp [applyFirst, TensorProduct.smul_tmul']
  | add x y hx hy =>
      simpa only [map_add, add_tmul] using congrArg₂ (· + ·) hx hy

private theorem applyFirst_assoc_rTensor_coact (φ : Module.Dual R M) (x : M ⊗[R] C) :
    applyFirst (C := C) φ
        (TensorProduct.assoc R M C C
          ((coact (R := R) (C := C) (M := M)).rTensor C x)) =
      TensorProduct.map
        (matrixCoefficientLinear (R := R) (C := C) φ) LinearMap.id x := by
  induction x with
  | zero => simp [applyFirst]
  | tmul m c =>
      rw [LinearMap.rTensor_tmul, applyFirst_assoc_tmul]
      rfl
  | add x y hx hy =>
      simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- Comultiplication of a matrix coefficient is obtained by applying its coefficient map to
the vector factor of the coaction. -/
theorem comul_matrixCoefficient (φ : Module.Dual R M) (m : M) :
    Coalgebra.comul (R := R) (A := C)
        (matrixCoefficient (R := R) (C := C) φ m) =
      TensorProduct.map
        (matrixCoefficientLinear (R := R) (C := C) φ) LinearMap.id
        (coact (R := R) (C := C) (M := M) m) := by
  have h := congrArg (applyFirst (C := C) φ)
    (coassoc_apply (R := R) (C := C) (M := M) m)
  rw [applyFirst_assoc_rTensor_coact, applyFirst_comul_lTensor] at h
  exact h.symm

omit [Coalgebra R C] [Comodule R C M] in
private theorem tensor_eq_sum_basis_tmul {ι : Type x} [Fintype ι]
    (b : Basis ι R M) (x : M ⊗[R] C) :
    x =
      ∑ i, b i ⊗ₜ[R]
        TensorProduct.lid R C
          (TensorProduct.map (b.coord i) LinearMap.id x) := by
  induction x with
  | zero => simp
  | tmul m c =>
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul]
      simp_rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      rw [← TensorProduct.sum_tmul Finset.univ]
      have hb : (∑ i, (b.coord i) m • b i) = m := by
        simpa only [Basis.coord_apply] using b.sum_repr m
      rw [hb]
  | add x y hx hy =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) hx hy

private theorem coact_eq_sum_basis_matrixCoefficient {ι : Type x} [Fintype ι]
    (b : Basis ι R M) (m : M) :
    coact (R := R) (C := C) (M := M) m =
      ∑ i, b i ⊗ₜ[R]
        matrixCoefficient (R := R) (C := C) (b.coord i) m := by
  simpa only [matrixCoefficient_def] using
    tensor_eq_sum_basis_tmul (C := C) b
      (coact (R := R) (C := C) (M := M) m)

/-- The comultiplication of a matrix coefficient, expanded in a finite basis. -/
theorem comul_matrixCoefficient_eq_sum {ι : Type x} [Fintype ι]
    (b : Basis ι R M) (φ : Module.Dual R M) (m : M) :
    Coalgebra.comul (R := R) (A := C)
        (matrixCoefficient (R := R) (C := C) φ m) =
      ∑ i, matrixCoefficient (R := R) (C := C) φ (b i) ⊗ₜ[R]
        matrixCoefficient (R := R) (C := C) (b.coord i) m := by
  rw [comul_matrixCoefficient,
    coact_eq_sum_basis_matrixCoefficient (C := C) b, map_sum]
  simp only [TensorProduct.map_tmul, LinearMap.id_apply,
    matrixCoefficientLinear_apply]

/-- The subcoalgebra spanned by the matrix coefficients of a finite free comodule. -/
@[expose] noncomputable def matrixCoefficientSubcoalgebra
    [Module.Free R M] [Module.Finite R M] :
    Subcoalgebra R C :=
  Subcoalgebra.ofSubmodule
    (matrixCoefficientSubmodule (R := R) (C := C) (M := M)) <| by
      intro c hc
      let D := matrixCoefficientSubmodule (R := R) (C := C) (M := M)
      let P :=
        LinearMap.range (TensorProduct.map D.subtype D.subtype)
      have hle :
          matrixCoefficientSubmodule (R := R) (C := C) (M := M) ≤
            P.comap (Coalgebra.comul (R := R) (A := C)) := by
        apply matrixCoefficientSubmodule_le
        intro φ m
        rw [Submodule.mem_comap]
        rw [comul_matrixCoefficient_eq_sum (Module.Free.chooseBasis R M)]
        refine ⟨∑ i,
          (⟨matrixCoefficient (R := R) (C := C) φ
              (Module.Free.chooseBasis R M i),
            matrixCoefficient_mem_submodule (R := R) (C := C) φ
              (Module.Free.chooseBasis R M i)⟩ : D) ⊗ₜ[R]
          (⟨matrixCoefficient (R := R) (C := C)
              ((Module.Free.chooseBasis R M).coord i) m,
            matrixCoefficient_mem_submodule (R := R) (C := C)
              ((Module.Free.chooseBasis R M).coord i) m⟩ : D), ?_⟩
        simp
      exact hle hc

/-- The underlying submodule of the coefficient subcoalgebra is the matrix-coefficient
submodule. -/
@[simp]
theorem matrixCoefficientSubcoalgebra_toSubmodule
    [Module.Free R M] [Module.Finite R M] :
    (matrixCoefficientSubcoalgebra (R := R) (C := C) (M := M)).toSubmodule =
      matrixCoefficientSubmodule (R := R) (C := C) (M := M) :=
  rfl

/-- Membership in the coefficient subcoalgebra is membership in the matrix-coefficient
submodule. -/
@[simp]
theorem mem_matrixCoefficientSubcoalgebra
    [Module.Free R M] [Module.Finite R M] {c : C} :
    c ∈ matrixCoefficientSubcoalgebra (R := R) (C := C) (M := M) ↔
      c ∈ matrixCoefficientSubmodule (R := R) (C := C) (M := M) :=
  Iff.rfl

/-- Every matrix coefficient belongs to the coefficient subcoalgebra. -/
theorem matrixCoefficient_mem_subcoalgebra
    [Module.Free R M] [Module.Finite R M] (φ : Module.Dual R M) (m : M) :
    matrixCoefficient (R := R) (C := C) φ m ∈
      matrixCoefficientSubcoalgebra (R := R) (C := C) (M := M) :=
  mem_matrixCoefficientSubcoalgebra.2
    (matrixCoefficient_mem_submodule (R := R) (C := C) φ m)

/-- The coefficient subcoalgebra is contained in a subcoalgebra exactly when that
subcoalgebra contains every matrix coefficient. -/
theorem matrixCoefficientSubcoalgebra_le_iff
    [Module.Free R M] [Module.Finite R M] {D : Subcoalgebra R C} :
    matrixCoefficientSubcoalgebra (R := R) (C := C) (M := M) ≤ D ↔
      ∀ (φ : Module.Dual R M) (m : M),
        matrixCoefficient (R := R) (C := C) φ m ∈ D := by
  constructor
  · intro h φ m
    exact h (matrixCoefficient_mem_subcoalgebra (R := R) (C := C) φ m)
  · intro h c hc
    rw [mem_matrixCoefficientSubcoalgebra] at hc
    rw [← Subcoalgebra.mem_toSubmodule]
    exact matrixCoefficientSubmodule_le (R := R) (C := C)
      (fun φ m => Subcoalgebra.mem_toSubmodule.2 (h φ m)) hc

end TauCeti.Comodule
