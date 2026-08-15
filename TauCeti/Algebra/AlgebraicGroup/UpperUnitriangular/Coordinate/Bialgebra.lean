/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommBialgCat
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import TauCeti.LinearAlgebra.Matrix.Triangular

/-!
# The upper-unitriangular coordinate bialgebra

For a commutative semiring `R`, the coordinate ring of the upper-unitriangular matrix monoid
`U_m` is the polynomial algebra on entries strictly above the diagonal. Its generic matrix has
ones on the diagonal and zeros below it. Matrix multiplication and the identity matrix give its
comultiplication and counit.

This is the semiring-level dependency layer for the upper-unitriangular coordinate Hopf algebra;
the antipode and finite-type Hopf package are constructed separately over commutative rings.

## Main declarations

* `TauCeti.UpperUnitriangular.CoordinateRing`: the polynomial coordinate ring of `U_m`.
* `TauCeti.UpperUnitriangular.genericMatrix`: the generic upper-unitriangular matrix.
* `TauCeti.UpperUnitriangular.comul` and `TauCeti.UpperUnitriangular.counit`: the raw structure
  maps.
* `TauCeti.UpperUnitriangular.comul_coassoc`: the comultiplication is coassociative.
* `TauCeti.UpperUnitriangular.comul_rTensor_counit` and
  `TauCeti.UpperUnitriangular.comul_lTensor_counit`: the two counit laws.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, I.2.
* T. A. Springer, *Linear Algebraic Groups*, Section 2.4.

The construction follows the coordinate-bialgebra layout of `TauCeti.MatrixMonoid` in
`GeneralLinear.Coordinate.Bialgebra`.
-/

public section

open scoped TensorProduct

namespace TauCeti.UpperUnitriangular

open Algebra.TensorProduct

universe u v w

/-- Pairs indexing the entries strictly above the diagonal of a square matrix. -/
abbrev Index (m : Type*) [LT m] := {ij : m × m // ij.1 < ij.2}

/-- The polynomial coordinate ring of the upper-unitriangular group. -/
abbrev CoordinateRing (R : Type u) [CommSemiring R] (m : Type*) [LT m] :=
  MvPolynomial (Index m) R

section Bialgebra

variable (R : Type u) [CommSemiring R] (m : Type v) [LinearOrder m]

/-- The generic upper-unitriangular matrix. -/
noncomputable def genericMatrix : Matrix m m (CoordinateRing R m) :=
  fun i j => if h : i < j then MvPolynomial.X (show Index m from ⟨(i, j), h⟩)
    else if i = j then 1 else 0

/-- Above the diagonal, the generic matrix is the corresponding polynomial coordinate. -/
@[simp]
theorem genericMatrix_apply_of_lt {i j : m} (h : i < j) :
    genericMatrix R m i j = MvPolynomial.X (show Index m from ⟨(i, j), h⟩) := by
  simp [genericMatrix, h]

/-- The generic matrix has ones on the diagonal. -/
@[simp]
theorem genericMatrix_apply_diag (i : m) : genericMatrix R m i i = 1 := by
  simp [genericMatrix]

/-- The generic matrix vanishes below the diagonal. -/
@[simp]
theorem genericMatrix_apply_eq_zero_of_gt {i j : m} (h : j < i) :
    genericMatrix R m i j = 0 := by
  simp [genericMatrix, h.asymm, h.ne']

/-- The generic matrix is upper unitriangular. -/
theorem isUpperUnitriangular_genericMatrix : (genericMatrix R m).IsUpperUnitriangular := by
  rw [Matrix.isUpperUnitriangular_def]
  constructor
  · intro i j h
    exact genericMatrix_apply_eq_zero_of_gt R m h
  · exact genericMatrix_apply_diag R m

/-- Evaluating the strict-upper coordinates of the generic matrix at an upper-unitriangular
matrix recovers that matrix. -/
theorem map_aeval_genericMatrix {A : Type w} [CommSemiring A] [Algebra R A]
    (M : Matrix m m A) (hM : M.IsUpperUnitriangular) :
    (genericMatrix R m).map
        (MvPolynomial.aeval fun ij : Index m => M ij.1.1 ij.1.2) = M := by
  apply ((isUpperUnitriangular_genericMatrix R m).map _).ext hM
  intro i j hij
  simp [Matrix.map_apply, genericMatrix_apply_of_lt R m hij]

variable [Fintype m]

/-- Matrix-multiplication comultiplication on the coordinate ring of `U_m`. -/
noncomputable def comul :
    CoordinateRing R m →ₐ[R] CoordinateRing R m ⊗[R] CoordinateRing R m :=
  MvPolynomial.aeval fun ij : Index m =>
    ((genericMatrix R m).map
        (includeLeft : CoordinateRing R m →ₐ[R]
          CoordinateRing R m ⊗[R] CoordinateRing R m) *
      (genericMatrix R m).map
        (includeRight : CoordinateRing R m →ₐ[R]
          CoordinateRing R m ⊗[R] CoordinateRing R m)) ij.1.1 ij.1.2

omit [Fintype m] in
/-- Identity-matrix counit on the coordinate ring of `U_m`. -/
noncomputable def counit : CoordinateRing R m →ₐ[R] R :=
  MvPolynomial.aeval fun ij : Index m => (1 : Matrix m m R) ij.1.1 ij.1.2

/-- Comultiplication evaluates the generic matrix at the product of its two tensor-factor
copies. -/
@[simp]
theorem map_comul_genericMatrix :
    (genericMatrix R m).map (comul R m) =
      (genericMatrix R m).map
          (includeLeft : CoordinateRing R m →ₐ[R]
            CoordinateRing R m ⊗[R] CoordinateRing R m) *
        (genericMatrix R m).map
          (includeRight : CoordinateRing R m →ₐ[R]
            CoordinateRing R m ⊗[R] CoordinateRing R m) := by
  apply map_aeval_genericMatrix
  exact (isUpperUnitriangular_genericMatrix R m).map includeLeft |>.mul
    ((isUpperUnitriangular_genericMatrix R m).map includeRight)

omit [Fintype m] in
/-- The counit evaluates the generic matrix at the identity. -/
@[simp]
theorem map_counit_genericMatrix : (genericMatrix R m).map (counit R m) = 1 := by
  simpa [counit] using map_aeval_genericMatrix R m (1 : Matrix m m R)
    (Matrix.isUpperUnitriangular_one (m := m) (R := R))

/-- Comultiplication on every generic matrix entry is matrix multiplication. -/
@[simp]
theorem comul_genericMatrix_apply (i j : m) :
    comul R m (genericMatrix R m i j) =
      ∑ k : m, genericMatrix R m i k ⊗ₜ[R] genericMatrix R m k j := by
  simpa [Matrix.map_apply, Matrix.mul_apply] using
    congrFun (congrFun (map_comul_genericMatrix R m) i) j

omit [Fintype m] in
/-- The counit on every generic matrix entry is the corresponding identity-matrix entry. -/
@[simp]
theorem counit_genericMatrix_apply (i j : m) :
    counit R m (genericMatrix R m i j) = if i = j then 1 else 0 := by
  exact congrFun (congrFun (map_counit_genericMatrix R m) i) j

/-- Comultiplication on a strict-upper coordinate is the corresponding entry of the product of
the two generic matrices. -/
@[simp]
theorem comul_X (ij : Index m) :
    comul R m (MvPolynomial.X ij) =
      ∑ k : m,
        genericMatrix R m ij.1.1 k ⊗ₜ[R]
          genericMatrix R m k ij.1.2 := by
  rw [← genericMatrix_apply_of_lt R m ij.2]
  exact comul_genericMatrix_apply R m ij.1.1 ij.1.2

omit [Fintype m] in
/-- The counit vanishes on every strict-upper coordinate. -/
@[simp]
theorem counit_X (ij : Index m) : counit R m (MvPolynomial.X ij) = 0 := by
  simp [counit, Matrix.one_apply_ne ij.2.ne]

/-- Matrix-multiplication comultiplication is coassociative. -/
theorem comul_coassoc :
    (Algebra.TensorProduct.assoc R R R
        (CoordinateRing R m) (CoordinateRing R m) (CoordinateRing R m)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comul R m) (.id R (CoordinateRing R m))).comp
        (comul R m)) =
      (Algebra.TensorProduct.map (.id R (CoordinateRing R m)) (comul R m)).comp
        (comul R m) := by
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul, AlgHom.id_apply]
  simp only [comul_genericMatrix_apply, TensorProduct.sum_tmul,
    TensorProduct.tmul_sum, map_sum]
  rw [Finset.sum_comm]
  rfl

/-- Applying the counit in the left tensor factor is the left-unit identification. -/
theorem comul_rTensor_counit :
    (Algebra.TensorProduct.map (counit R m) (.id R (CoordinateRing R m))).comp
        (comul R m) =
      (Algebra.TensorProduct.lid R (CoordinateRing R m)).symm := by
  apply MvPolynomial.algHom_ext
  intro ij
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul,
    counit_genericMatrix_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single i]
  · simp [genericMatrix_apply_of_lt R m hij]
  · intro k _ hki
    simp [hki.symm]
  · simp

/-- Applying the counit in the right tensor factor is the right-unit identification. -/
theorem comul_lTensor_counit :
    (Algebra.TensorProduct.map (.id R (CoordinateRing R m)) (counit R m)).comp
        (comul R m) =
      (Algebra.TensorProduct.rid R R (CoordinateRing R m)).symm := by
  apply MvPolynomial.algHom_ext
  intro ij
  obtain ⟨⟨i, j⟩, hij⟩ := ij
  simp only [AlgHom.comp_apply, comul_X, map_sum, map_tmul,
    counit_genericMatrix_apply, AlgHom.id_apply]
  rw [Finset.sum_eq_single j]
  · simp [genericMatrix_apply_of_lt R m hij]
  · intro k _ hkj
    simp [hkj]
  · simp

end Bialgebra

end TauCeti.UpperUnitriangular
