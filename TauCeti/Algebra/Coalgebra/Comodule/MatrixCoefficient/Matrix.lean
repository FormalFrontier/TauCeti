/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Adjoin
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Comul

/-!
# The coefficient matrix of a comodule with a finite basis

For a right comodule `M` over `C` with a finite basis `(eⱼ)` and coordinate functionals `(eⁱ)`,
the matrix coefficients `c(eⁱ, eⱼ)` assemble into a square matrix over `C`. The comodule laws say
that this matrix is multiplicative under comultiplication and specializes to the identity matrix
under the counit.

When `C` is a Hopf algebra, the antipode identities say that the entrywise antipode transform is a
two-sided inverse of the coefficient matrix; over a commutative Hopf algebra its determinant is
therefore a unit.

## Main declarations

* `TauCeti.Comodule.coefficientMatrix`: the matrix of basis matrix coefficients.
* `TauCeti.Comodule.coefficientMatrixSet`: the set of entries of a coefficient matrix.
* `TauCeti.Comodule.span_coefficientMatrixSet`: the entries span the full matrix-coefficient
  submodule.
* `TauCeti.Comodule.adjoin_coefficientMatrixSet`: the entries of the coefficient matrix
  generate the full matrix-coefficient algebra.
* `TauCeti.Comodule.coact_basis_eq_sum_coefficientMatrix`: the coaction of a basis vector is the
  corresponding column of the coefficient matrix.
* `TauCeti.Comodule.comul_coefficientMatrix_eq_sum` and
  `TauCeti.Comodule.counit_coefficientMatrix`: the coalgebra identities.
* `TauCeti.Comodule.coefficientMatrix_mul_map_antipode` and
  `TauCeti.Comodule.map_antipode_mul_coefficientMatrix`: the two inverse-matrix identities.
* `TauCeti.Comodule.isUnit_det_coefficientMatrix`: the determinant is a unit.

## References

This is the standard coefficient matrix of a finite free corepresentation; see Sweedler,
*Hopf Algebras*, Chapter 2, and Milne, *Algebraic Groups* (2017), Chapter 4, Remark 4.1. It
supplies a prerequisite for `ReductiveGroups/README.md` in TauCetiRoadmap, Layer 1,
"Faithfulness done right".
-/

public section

open scoped TensorProduct
open Module

namespace TauCeti.Comodule

universe u v w x

noncomputable section

variable {R : Type u} {C : Type v} {M : Type w} {ι : Type x}
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

section Coalgebra

variable [AddCommMonoid C] [Module R C] [Coalgebra R C] [Comodule R C M]

/-- The matrix of basis matrix coefficients of a comodule.

If `eⱼ` is a basis and `eⁱ` its coordinate functionals, the `(i, j)` entry is `c(eⁱ, eⱼ)`. -/
def coefficientMatrix (b : Basis ι R M) : Matrix ι ι C :=
  fun i j ↦ matrixCoefficient (R := R) (C := C) (b.coord i) (b j)

/-- An entry of the coefficient matrix is the corresponding basis matrix coefficient.

This is not a `simp` lemma: the coefficient matrix is the normal form, and the coalgebra
identities below are stated for its entries. -/
theorem coefficientMatrix_apply (b : Basis ι R M) (i j : ι) :
    coefficientMatrix (C := C) b i j =
      matrixCoefficient (R := R) (C := C) (b.coord i) (b j) := by
  rw [coefficientMatrix]

/-- The set of entries of a coefficient matrix. -/
def coefficientMatrixSet (b : Basis ι R M) : Set C :=
  Set.range fun ij : ι × ι ↦ coefficientMatrix (C := C) b ij.1 ij.2

/-- Membership in the set of entries of a coefficient matrix is witnessed by two basis
indices. -/
theorem mem_coefficientMatrixSet_iff (b : Basis ι R M) (c : C) :
    c ∈ coefficientMatrixSet (C := C) b ↔
      ∃ i j, coefficientMatrix (C := C) b i j = c := by
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨i, j, rfl⟩
  · rintro ⟨i, j, rfl⟩
    exact ⟨(i, j), rfl⟩

/-- Every entry of a coefficient matrix belongs to its set of entries. -/
@[simp]
theorem coefficientMatrix_mem_set (b : Basis ι R M) (i j : ι) :
    coefficientMatrix (C := C) b i j ∈ coefficientMatrixSet (C := C) b :=
  ⟨(i, j), rfl⟩

/-- The entries of a coefficient matrix span the full matrix-coefficient submodule.

Although the left-hand side uses a chosen finite basis, every matrix coefficient is an
`R`-linear combination of these entries. -/
@[simp]
theorem span_coefficientMatrixSet [Finite ι] (b : Basis ι R M) :
    Submodule.span R (coefficientMatrixSet (C := C) b) =
      matrixCoefficientSubmodule (R := R) (C := C) (M := M) := by
  classical
  let _ := Fintype.ofFinite ι
  apply le_antisymm
  · rw [Submodule.span_le]
    intro c hc
    obtain ⟨i, j, rfl⟩ := (mem_coefficientMatrixSet_iff (C := C) b c).mp hc
    rw [coefficientMatrix_apply]
    exact matrixCoefficient_mem_submodule (R := R) (C := C) (b.coord i) (b j)
  · rw [matrixCoefficientSubmodule_le_iff]
    intro φ m
    rw [← matrixCoefficientBilinear_apply_apply]
    rw [← LinearMap.sum_repr_mul_repr_mul (B :=
      matrixCoefficientBilinear (R := R) (C := C) (M := M)) b.dualBasis b φ m]
    simp only [Finsupp.sum]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.sum_mem
    intro j _
    simpa only [matrixCoefficientBilinear_apply_apply, Basis.coe_dualBasis,
      coefficientMatrix_apply] using
      Submodule.smul_mem (Submodule.span R (coefficientMatrixSet (C := C) b))
        ((b.dualBasis.repr φ) i)
        (Submodule.smul_mem (Submodule.span R (coefficientMatrixSet (C := C) b))
          ((b.repr m) j)
          (Submodule.subset_span (coefficientMatrix_mem_set (C := C) b i j)))

/-- The counit of a coefficient entry is the corresponding identity-matrix entry. -/
@[simp]
theorem counit_coefficientMatrix [DecidableEq ι] (b : Basis ι R M) (i j : ι) :
    Coalgebra.counit (R := R) (A := C) (coefficientMatrix (C := C) b i j) =
      if i = j then 1 else 0 := by
  rw [coefficientMatrix_apply, counit_matrixCoefficient]
  simpa only [Basis.coord_apply, eq_comm] using b.repr_self_apply j i

variable [Fintype ι]

/-- The coaction of a basis vector is its column in the coefficient matrix. -/
theorem coact_basis_eq_sum_coefficientMatrix (b : Basis ι R M) (j : ι) :
    coact (R := R) (C := C) (M := M) (b j) =
      ∑ i, b i ⊗ₜ[R] coefficientMatrix (C := C) b i j :=
  coact_eq_sum_basis_matrixCoefficient (C := C) b (b j)

/-- Comultiplication of a coefficient entry is matrix multiplication across the two tensor
factors. -/
@[simp]
theorem comul_coefficientMatrix_eq_sum (b : Basis ι R M) (i j : ι) :
    Coalgebra.comul (R := R) (A := C) (coefficientMatrix (C := C) b i j) =
      ∑ k, coefficientMatrix (C := C) b i k ⊗ₜ[R] coefficientMatrix (C := C) b k j :=
  comul_matrixCoefficient_eq_sum (C := C) b (b.coord i) (b j)

end Coalgebra

section HopfAlgebra

variable [Semiring C] [HopfAlgebra R C] [Comodule R C M] [Fintype ι]

/-- The basis expansion of the comultiplication of a matrix coefficient, packaged as a
`Coalgebra.Repr` so that Mathlib's antipode sums apply to it. -/
private def matrixCoefficientRepr (b : Basis ι R M) (p q : ι) :
    Coalgebra.Repr R (matrixCoefficient (R := R) (C := C) (b.coord p) (b q)) ι where
  index := Finset.univ
  left := fun x ↦ matrixCoefficient (R := R) (C := C) (b.coord p) (b x)
  right := fun x ↦ matrixCoefficient (R := R) (C := C) (b.coord x) (b q)
  eq := (comul_matrixCoefficient_eq_sum (C := C) b (b.coord p) (b q)).symm

/-- Multiplying the matrix of basis coefficients by its entrywise antipode transform gives the
image under `algebraMap` of a single basis coordinate: taking `p` and `q` basis indices, the
right-hand side is `1` when they agree and `0` otherwise. -/
theorem sum_matrixCoefficient_mul_antipode_eq_algebraMap (b : Basis ι R M) (p q : ι) :
    (∑ x : ι, matrixCoefficient (R := R) (C := C) (b.coord p) (b x) *
        HopfAlgebra.antipode R
          (matrixCoefficient (R := R) (C := C) (b.coord x) (b q))) =
      algebraMap R C (b.coord p (b q)) := by
  rw [← counit_matrixCoefficient (R := R) (C := C) (b.coord p) (b q)]
  exact HopfAlgebra.sum_mul_antipode_eq_algebraMap_counit (matrixCoefficientRepr (C := C) b p q)

/-- The opposite multiplication order of `sum_matrixCoefficient_mul_antipode_eq_algebraMap`: the
entrywise antipode transform is also a left inverse of the matrix of basis coefficients. -/
theorem sum_antipode_mul_matrixCoefficient_eq_algebraMap (b : Basis ι R M) (p q : ι) :
    (∑ x : ι, HopfAlgebra.antipode R
          (matrixCoefficient (R := R) (C := C) (b.coord p) (b x)) *
        matrixCoefficient (R := R) (C := C) (b.coord x) (b q)) =
      algebraMap R C (b.coord p (b q)) := by
  rw [← counit_matrixCoefficient (R := R) (C := C) (b.coord p) (b q)]
  exact HopfAlgebra.sum_antipode_mul_eq_algebraMap_counit (matrixCoefficientRepr (C := C) b p q)

variable [DecidableEq ι]

/-- The entrywise antipode of the coefficient matrix is a right inverse. -/
@[simp]
theorem coefficientMatrix_mul_map_antipode (b : Basis ι R M) :
    coefficientMatrix (C := C) b *
        (coefficientMatrix (C := C) b).map (HopfAlgebra.antipode R) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, coefficientMatrix_apply, Matrix.one_apply]
  rw [sum_matrixCoefficient_mul_antipode_eq_algebraMap (C := C) b i j]
  simp only [Basis.coord_apply, Basis.repr_self_apply, apply_ite (algebraMap R C), map_one,
    map_zero, eq_comm]

/-- The entrywise antipode of the coefficient matrix is a left inverse. -/
@[simp]
theorem map_antipode_mul_coefficientMatrix (b : Basis ι R M) :
    (coefficientMatrix (C := C) b).map (HopfAlgebra.antipode R) *
        coefficientMatrix (C := C) b = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, coefficientMatrix_apply, Matrix.one_apply]
  rw [sum_antipode_mul_matrixCoefficient_eq_algebraMap (C := C) b i j]
  simp only [Basis.coord_apply, Basis.repr_self_apply, apply_ite (algebraMap R C), map_one,
    map_zero, eq_comm]

end HopfAlgebra

section CommRing

variable [CommRing C] [HopfAlgebra R C] [Comodule R C M]
variable [Fintype ι] [DecidableEq ι]

/-- The determinant of the coefficient matrix is a unit. -/
theorem isUnit_det_coefficientMatrix (b : Basis ι R M) :
    IsUnit (Matrix.det (coefficientMatrix (C := C) b)) :=
  Matrix.isUnit_det_of_right_inverse (coefficientMatrix_mul_map_antipode (C := C) b)

end CommRing

section Adjoin

variable [Semiring C] [Algebra R C] [Coalgebra R C] [Comodule R C M]

/-- Every coefficient-matrix entry belongs to the algebra generated by all matrix
coefficients. -/
@[simp]
theorem coefficientMatrix_mem_matrixCoefficientSubalgebra
    (b : Basis ι R M) (i j : ι) :
    coefficientMatrix (C := C) b i j ∈
      matrixCoefficientSubalgebra (R := R) (C := C) (M := M) := by
  rw [coefficientMatrix_apply]
  exact matrixCoefficient_mem_subalgebra (R := R) (C := C) (b.coord i) (b j)

variable [Finite ι]

/-- The entries of a coefficient matrix generate the full matrix-coefficient algebra.

Although the left-hand side uses only the coefficients indexed by a chosen finite basis, every
matrix coefficient is an `R`-linear combination of these entries, so the resulting subalgebra is
independent of the basis. -/
@[simp]
theorem adjoin_coefficientMatrixSet (b : Basis ι R M) :
    Algebra.adjoin R (coefficientMatrixSet (C := C) b) =
      matrixCoefficientSubalgebra (R := R) (C := C) (M := M) := by
  calc
    Algebra.adjoin R (coefficientMatrixSet (C := C) b) =
        Algebra.adjoin R (Submodule.span R (coefficientMatrixSet (C := C) b) : Set C) :=
      (Algebra.adjoin_span (R := R) (A := C)).symm
    _ = Algebra.adjoin R
        (matrixCoefficientSubmodule (R := R) (C := C) (M := M) : Set C) := by
      rw [span_coefficientMatrixSet]
    _ = Algebra.adjoin R
        (Submodule.span R (matrixCoefficientSet (R := R) (C := C) (M := M)) : Set C) := by
      rw [matrixCoefficientSubmodule_def]
    _ = Algebra.adjoin R (matrixCoefficientSet (R := R) (C := C) (M := M)) :=
      by rw [Algebra.adjoin_span]
    _ = matrixCoefficientSubalgebra (R := R) (C := C) (M := M) :=
      matrixCoefficientSubalgebra_def.symm

end Adjoin

end

end TauCeti.Comodule
