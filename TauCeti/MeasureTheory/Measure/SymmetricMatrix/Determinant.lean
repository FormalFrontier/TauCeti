/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.MvPolynomialZeroLocus
public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Lebesgue

/-!
# Singular symmetric matrices are Lebesgue-null

The determinant is a polynomial in the upper-triangular coordinates, and it is nonzero because
the identity matrix has determinant one. The zero locus of a nonzero polynomial is
Lebesgue-null, so the singular symmetric matrices are `TauCeti.symmetricLebesgue`-null.

The standard-distributions roadmap uses this for the singularity of the degenerate
Gaussian-Gram Wishart laws with respect to `symmetricLebesgue`.

## Main declarations

* `TauCeti.measurableSet_setOfPred_det_eq_zero` — the singular matrices are measurable.
* `TauCeti.symmetricLebesgue_setOf_det_eq_zero` — the singular matrices are
  `symmetricLebesgue`-null.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 6, item 1,
  **Symmetric matrices and their Lebesgue measure**.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

/-- The determinant of a symmetric matrix, read through the upper-triangular coordinates as a
polynomial. -/
@[expose]
def symmetricDetPolynomial (p : ℕ) : MvPolynomial (upperTriangle p) ℝ :=
  (Matrix.of fun i j : Fin p =>
    if h : i ≤ j then MvPolynomial.X ⟨(i, j), h⟩
    else MvPolynomial.X ⟨(j, i), le_of_not_ge h⟩).det

theorem eval_symmetricDetPolynomial (p : ℕ) (x : upperTriangle p → ℝ) :
    MvPolynomial.eval x (symmetricDetPolynomial p) =
      ((symmetricCoordinates p).symm x : Matrix (Fin p) (Fin p) ℝ).det := by
  rw [symmetricDetPolynomial, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  by_cases h : i ≤ j
  · rw [dite_eq_left h, MvPolynomial.eval_X, coe_symmetricCoordinates_symm_apply_of_le p x h]
  · rw [dite_eq_right h, MvPolynomial.eval_X,
      coe_symmetricCoordinates_symm_apply_of_ge p x (le_of_not_ge h)]

/-- The upper-triangular coordinates of the identity matrix reconstruct the identity matrix. -/
private theorem coe_symmetricCoordinates_symm_one (p : ℕ) :
    ((symmetricCoordinates p).symm
          (fun ij : upperTriangle p => if ij.1.1 = ij.1.2 then (1 : ℝ) else 0) :
        Matrix (Fin p) (Fin p) ℝ) = 1 := by
  ext i j
  by_cases h : i ≤ j
  · rw [coe_symmetricCoordinates_symm_apply_of_le p _ h, Matrix.one_apply]
  · rw [coe_symmetricCoordinates_symm_apply_of_ge p _ (le_of_not_ge h), Matrix.one_apply]
    exact if_congr eq_comm rfl rfl

theorem symmetricDetPolynomial_ne_zero (p : ℕ) : symmetricDetPolynomial p ≠ 0 := by
  intro h
  have hval := eval_symmetricDetPolynomial p
    (fun ij : upperTriangle p => if ij.1.1 = ij.1.2 then (1 : ℝ) else 0)
  rw [h, map_zero, coe_symmetricCoordinates_symm_one, Matrix.det_one] at hval
  exact zero_ne_one hval

/-- The singular symmetric matrices form a closed, hence measurable, set: the determinant is
continuous. -/
theorem measurableSet_setOfPred_det_eq_zero (p : ℕ) :
    MeasurableSet {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
      (A : Matrix (Fin p) (Fin p) ℝ).det = 0} :=
  (isClosed_eq (Continuous.matrix_det continuous_subtype_val) continuous_const).measurableSet

/-- The singular symmetric matrices form a `symmetricLebesgue`-null set. -/
theorem symmetricLebesgue_setOf_det_eq_zero (p : ℕ) :
    symmetricLebesgue p
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).det = 0} = 0 := by
  rw [← (measurePreserving_symmetricCoordinates_symm p).measure_preimage
    (measurableSet_setOfPred_det_eq_zero p).nullMeasurableSet]
  have hpre : ((symmetricCoordinates p).symm ⁻¹'
      {A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (A : Matrix (Fin p) (Fin p) ℝ).det = 0}) =
      {x : upperTriangle p → ℝ | MvPolynomial.eval x (symmetricDetPolynomial p) = 0} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, eval_symmetricDetPolynomial]
  rw [hpre]
  exact MvPolynomial.volume_setOfPred_eval_eq_zero (symmetricDetPolynomial_ne_zero p)

end TauCeti
