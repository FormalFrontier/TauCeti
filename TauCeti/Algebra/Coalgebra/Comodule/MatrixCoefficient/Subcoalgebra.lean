/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
* `TauCeti.Comodule.matrixCoefficientSubcoalgebra_le_iff`: its universal property.

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

/-- Comultiplication of a matrix coefficient is obtained by applying its coefficient map to
the vector factor of the coaction. -/
theorem comul_matrixCoefficient (φ : Module.Dual R M) (m : M) :
    Coalgebra.comul (R := R) (A := C)
        (matrixCoefficient (R := R) (C := C) φ m) =
      TensorProduct.map
        (matrixCoefficientLinear (R := R) (C := C) φ) LinearMap.id
        (coact (R := R) (C := C) (M := M) m) := by
  -- Expose matrix coefficients as composite linear maps so `coassoc_simps` can rewrite
  -- coassociativity without tensor induction.
  change (Coalgebra.comul ∘ₗ (TensorProduct.lid R C).toLinearMap ∘ₗ
          TensorProduct.map φ LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := M)) m =
        (TensorProduct.map
            ((TensorProduct.lid R C).toLinearMap ∘ₗ
              TensorProduct.map φ LinearMap.id ∘ₗ
              coact (R := R) (C := C) (M := M))
            LinearMap.id ∘ₗ
          coact (R := R) (C := C) (M := M)) m
  apply LinearMap.congr_fun ?_ m
  calc
    _ = (TensorProduct.lid R (C ⊗[R] C)).toLinearMap ∘ₗ
        TensorProduct.map φ LinearMap.id ∘ₗ
        TensorProduct.map LinearMap.id Coalgebra.comul ∘ₗ
        coact (R := R) (C := C) (M := M) := by
          simp only [coassoc_simps]
    _ = (TensorProduct.lid R (C ⊗[R] C)).toLinearMap ∘ₗ
        TensorProduct.map φ LinearMap.id ∘ₗ
        (TensorProduct.assoc R M C C).toLinearMap ∘ₗ
        TensorProduct.map (coact (R := R) (C := C) (M := M)) LinearMap.id ∘ₗ
        coact (R := R) (C := C) (M := M) := by
          simpa only [coassoc_simps] using congrArg
            (fun f : M →ₗ[R] M ⊗[R] (C ⊗[R] C) =>
              (TensorProduct.lid R (C ⊗[R] C)).toLinearMap ∘ₗ
                TensorProduct.map φ LinearMap.id ∘ₗ f)
            (coact_coassoc (R := R) (C := C) (M := M)).symm
    _ = TensorProduct.map
          ((TensorProduct.lid R C).toLinearMap ∘ₗ
            TensorProduct.map φ LinearMap.id)
          LinearMap.id ∘ₗ
        TensorProduct.map (coact (R := R) (C := C) (M := M)) LinearMap.id ∘ₗ
        coact (R := R) (C := C) (M := M) := by
          simp only [TensorProduct.lid_tensor, coassoc_simps]
    _ = _ := by
      simp only [coassoc_simps]

omit [Coalgebra R C] [Comodule R C M] in
private theorem tensor_eq_sum_basis_tmul {ι : Type x} [Fintype ι]
    (b : Basis ι R M) (x : M ⊗[R] C) :
    x =
      ∑ i, b i ⊗ₜ[R]
        TensorProduct.lid R C
          (TensorProduct.map (b.coord i) LinearMap.id x) := by
  classical
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := C) b
  calc
    x = e.symm (e x) := (e.symm_apply_apply x).symm
    _ = (e x).sum fun i n => b i ⊗ₜ[R] n :=
      TensorProduct.equivFinsuppOfBasisLeft_symm_apply b (e x)
    _ = ∑ i, b i ⊗ₜ[R] (e x i) := Finsupp.sum_fintype _ _ (by simp)
    _ = ∑ i, b i ⊗ₜ[R]
        TensorProduct.lid R C
          (TensorProduct.map (b.coord i) LinearMap.id x) := by
      congr 1
      funext i
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply]
      simp only [LinearMap.rTensor]

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
      -- Fold the carrier into `D` and expose the tensor-inclusion range required by
      -- `Subcoalgebra.ofSubmodule`.
      change Coalgebra.comul (R := R) (A := C) c ∈
        LinearMap.range (TensorProduct.map D.subtype D.subtype)
      rw [TensorProduct.range_mapIncl]
      apply
        (matrixCoefficientSubmodule_le
          (P := (Submodule.map₂ (TensorProduct.mk R C C) D D).comap
            (Coalgebra.comul (R := R) (A := C))) ?_) hc
      intro φ m
      rw [Submodule.mem_comap]
      rw [comul_matrixCoefficient_eq_sum (Module.Free.chooseBasis R M)]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.apply_mem_map₂ _
          (matrixCoefficient_mem_submodule (R := R) (C := C) φ
            (Module.Free.chooseBasis R M i))
          (matrixCoefficient_mem_submodule (R := R) (C := C)
            ((Module.Free.chooseBasis R M).coord i) m)

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

/-- The coefficient subcoalgebra is the smallest subcoalgebra containing all matrix
coefficients. -/
theorem matrixCoefficientSubcoalgebra_le
    [Module.Free R M] [Module.Finite R M] {D : Subcoalgebra R C}
    (hD : ∀ (φ : Module.Dual R M) (m : M),
      matrixCoefficient (R := R) (C := C) φ m ∈ D) :
    matrixCoefficientSubcoalgebra (R := R) (C := C) (M := M) ≤ D := by
  intro c hc
  rw [mem_matrixCoefficientSubcoalgebra] at hc
  rw [← Subcoalgebra.mem_toSubmodule]
  exact matrixCoefficientSubmodule_le (R := R) (C := C)
    (fun φ m => Subcoalgebra.mem_toSubmodule.2 (hD φ m)) hc

/-- The coefficient subcoalgebra is contained in a subcoalgebra exactly when that
subcoalgebra contains every matrix coefficient. -/
theorem matrixCoefficientSubcoalgebra_le_iff
    [Module.Free R M] [Module.Finite R M] {D : Subcoalgebra R C} :
    matrixCoefficientSubcoalgebra (R := R) (C := C) (M := M) ≤ D ↔
      ∀ (φ : Module.Dual R M) (m : M),
        matrixCoefficient (R := R) (C := C) φ m ∈ D := by
  exact
    ⟨fun hD φ m => hD (matrixCoefficient_mem_subcoalgebra (R := R) (C := C) φ m),
      matrixCoefficientSubcoalgebra_le (R := R) (C := C) (M := M)⟩

end TauCeti.Comodule
