/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Comul
public import TauCeti.Algebra.Coalgebra.Subcoalgebra.Basic

/-!
# The coefficient subcoalgebra of a finite free comodule

Expanding the comultiplication of a matrix coefficient in a finite basis `(eᵢ)` gives

```text
Δ(c(φ, m)) = ∑ i, c(φ, eᵢ) ⊗ c(eⁱ, m).
```

Consequently, over a commutative semiring, the matrix-coefficient submodule of a finite free
comodule is stable under comultiplication and hence defines a subcoalgebra.

## Main declarations

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

/-- The subcoalgebra spanned by the matrix coefficients of a finite free comodule. -/
noncomputable def matrixCoefficientSubcoalgebra
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

-- The body of `matrixCoefficientSubcoalgebra` is deliberately not exposed, so the two
-- characteristic lemmas below are written `(rfl)` rather than `rfl`: the parentheses opt out of
-- exporting the definitional equality, which downstream modules do not need and which these
-- lemmas themselves replace.

/-- The underlying submodule of the coefficient subcoalgebra is the matrix-coefficient
submodule. -/
@[simp]
theorem matrixCoefficientSubcoalgebra_toSubmodule
    [Module.Free R M] [Module.Finite R M] :
    (matrixCoefficientSubcoalgebra (R := R) (C := C) (M := M)).toSubmodule =
      matrixCoefficientSubmodule (R := R) (C := C) (M := M) :=
  (rfl)

/-- Membership in the coefficient subcoalgebra is membership in the matrix-coefficient
submodule. -/
@[simp]
theorem mem_matrixCoefficientSubcoalgebra
    [Module.Free R M] [Module.Finite R M] {c : C} :
    c ∈ matrixCoefficientSubcoalgebra (R := R) (C := C) (M := M) ↔
      c ∈ matrixCoefficientSubmodule (R := R) (C := C) (M := M) :=
  (Iff.rfl)

/-- Every matrix coefficient belongs to the coefficient subcoalgebra.

This is not a `simp` lemma: `mem_matrixCoefficientSubcoalgebra` and
`matrixCoefficient_mem_submodule` already discharge the goal, and tagging it would make it
`simpNF`-redundant. -/
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
