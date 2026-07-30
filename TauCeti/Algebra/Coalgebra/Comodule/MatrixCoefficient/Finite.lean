/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin

/-!
# Finite matrix-coefficient submodules

This file identifies the matrix-coefficient submodule of a right comodule with the range of
the linear map from `Module.Dual R M ⊗[R] M`. Over a field, the coefficient submodule of a
finite-dimensional comodule is therefore finite-dimensional.

This is the first finite-dimensionality step toward the fundamental theorem of comodules in
the reductive-groups roadmap. The next substantive step is to show that this finite submodule
is closed under comultiplication, making it a coefficient subcoalgebra.

## Main results

* `TauCeti.Comodule.range_matrixCoefficientTensor`: the tensor map has range equal to the
  matrix-coefficient submodule.
* `TauCeti.Comodule.matrixCoefficientSubmodule_finite`: over a field, a finite-dimensional
  comodule has a finite-dimensional matrix-coefficient submodule.

## References

The coefficient-space construction is standard; see Sweedler, *Hopf Algebras*, Chapter 2.
It advances `ReductiveGroups/README.md` in TauCetiRoadmap, Layer 1,
"Finite-dimensional subcoalgebras (the fundamental theorem of comodules)".
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace Comodule

universe u v w

section Range

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- The range of the tensor-linearized matrix-coefficient map is exactly the submodule
spanned by all matrix coefficients. -/
theorem range_matrixCoefficientTensor :
    LinearMap.range
        (matrixCoefficientTensor (R := R) (C := C) (M := M)) =
      matrixCoefficientSubmodule (R := R) (C := C) (M := M) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x with
    | zero =>
        simpa only [map_zero] using
          (Submodule.zero_mem
            (matrixCoefficientSubmodule (R := R) (C := C) (M := M)))
    | tmul φ m =>
        simpa only [matrixCoefficientTensor_tmul] using
          (matrixCoefficient_mem_submodule (R := R) (C := C) φ m)
    | add x y hx hy =>
        simpa only [map_add] using Submodule.add_mem _ hx hy
  · rw [matrixCoefficientSubmodule_le_iff]
    intro φ m
    exact
      ⟨φ ⊗ₜ[R] m,
        matrixCoefficientTensor_tmul (R := R) (C := C) φ m⟩

end Range

section Field

variable {k : Type u} {C : Type v} {M : Type w} [Field k]
variable [AddCommGroup C] [Module k C] [Coalgebra k C]
variable [AddCommGroup M] [Module k M] [Comodule k C M]

/-- Over a field, the matrix-coefficient submodule of a finite-dimensional comodule is
finite-dimensional. -/
theorem matrixCoefficientSubmodule_finite [Module.Finite k M] :
    Module.Finite k
      (matrixCoefficientSubmodule (R := k) (C := C) (M := M)) := by
  rw [← range_matrixCoefficientTensor]
  infer_instance

end Field

end Comodule

end TauCeti
