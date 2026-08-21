/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin
public import TauCeti.Algebra.Coalgebra.Comodule.Transport

/-!
# Transport invariance of matrix coefficients

This file records how the matrix coefficients of a right comodule behave under transport of
a comodule structure across a linear equivalence. The general functoriality lemmas for
comodule morphisms live with the coefficient span and adjoin API in
`TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin`; this file keeps the
transport-specific consequences behind the `Comodule.Transport` import.

These lemmas are bookkeeping for the reductive-groups roadmap's faithful-representation
criterion: faithful representations are detected by whether their matrix coefficients
generate the coordinate Hopf algebra.

## Main declarations

* `TauCeti.Comodule.matrixCoefficientSet_transport`: the set of coefficients is invariant
  under transported coactions.
* `TauCeti.Comodule.matrixCoefficientSubmodule_transport` and
  `TauCeti.Comodule.matrixCoefficientSubalgebra_transport`: coefficient objects are
  invariant under transported coactions.

## References

This is standard matrix-coefficient functoriality for comodules; see Sweedler, *Hopf
Algebras*, Chapter 2. It supplies a prerequisite for
`ReductiveGroups/README.md` in TauCetiRoadmap, Layer 1, "Faithfulness done right", where
faithful representations are characterized by their matrix coefficients generating the
coordinate Hopf algebra.
-/

public section

namespace TauCeti

namespace Comodule

universe u v w x

variable {R : Type u} {C : Type v} {M : Type w}
variable [CommSemiring R]

section Transport

variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable {N₀ : Type x} [AddCommMonoid N₀] [Module R N₀]

/-- Transporting a comodule structure across a linear equivalence does not change its
coefficient set. -/
@[simp]
theorem matrixCoefficientSet_transport (e : M ≃ₗ[R] N₀) :
    letI : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
    matrixCoefficientSet (R := R) (C := C) (M := N₀) =
      matrixCoefficientSet (R := R) (C := C) (M := M) := by
  let : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
  exact (matrixCoefficientSet_eq_of_inverse_hom
    (R := R) (C := C) (M := M) (N := N₀)
    (transportToHom (R := R) (C := C) (M := M) (N := N₀) e)
    (transportInvHom (R := R) (C := C) (M := M) (N := N₀) e)
    (fun n => e.apply_symm_apply n) (fun m => e.symm_apply_apply m)).symm

/-- Transporting a comodule structure across a linear equivalence does not change its
coefficient submodule. -/
@[simp]
theorem matrixCoefficientSubmodule_transport (e : M ≃ₗ[R] N₀) :
    letI : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
    matrixCoefficientSubmodule (R := R) (C := C) (M := N₀) =
      matrixCoefficientSubmodule (R := R) (C := C) (M := M) := by
  let : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
  rw [matrixCoefficientSubmodule, matrixCoefficientSubmodule, matrixCoefficientSet_transport]

end Transport

section AlgebraTransport

variable [Semiring C] [Algebra R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [Comodule R C M]
variable {N₀ : Type x} [AddCommMonoid N₀] [Module R N₀]

/-- Transporting a comodule structure across a linear equivalence does not change its
coefficient algebra. -/
@[simp]
theorem matrixCoefficientSubalgebra_transport (e : M ≃ₗ[R] N₀) :
    letI : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
    matrixCoefficientSubalgebra (R := R) (C := C) (M := N₀) =
      matrixCoefficientSubalgebra (R := R) (C := C) (M := M) := by
  let : Comodule R C N₀ := Transport (R := R) (C := C) (M := M) (N := N₀) e
  rw [matrixCoefficientSubalgebra, matrixCoefficientSubalgebra, matrixCoefficientSet_transport]

end AlgebraTransport

end Comodule

end TauCeti
