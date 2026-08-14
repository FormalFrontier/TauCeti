/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
# Gram determinants of integral lattices

This file attaches an integral Gram matrix to every basis of an integral lattice. Its determinant
is independent of the carrier basis: an integral change-of-basis matrix has determinant `1` or
`-1`, and the Gram matrix changes by multiplication by that matrix and its transpose. The resulting
basis-free signed determinant and its absolute value are the determinant and discriminant of the
lattice.

The rational scalar extension of a Gram matrix is the matrix of the ambient rational bilinear form
in the extended basis. Consequently the signed determinant is nonzero exactly when that form is
nondegenerate. This is the determinant criterion needed before constructing the finite
discriminant group.

## Main definitions

* `TauCeti.IntegralLattice.gramMatrix`: the integral matrix of the restricted form in a carrier
  basis.
* `TauCeti.IntegralLattice.gramDet`: its signed determinant.
* `TauCeti.IntegralLattice.determinant`: the basis-independent signed determinant.
* `TauCeti.IntegralLattice.discriminant`: the nonnegative absolute determinant.

## Main results

* `TauCeti.IntegralLattice.gramDet_eq_gramDet`: Gram determinants agree in any two bases.
* `TauCeti.IntegralLattice.gramDet_ne_zero_iff`: a Gram determinant is nonzero exactly when the
  ambient form is nondegenerate.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 1.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u v w

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

section GramMatrix

variable (L : IntegralLattice V)

/-- The integral Gram matrix of a carrier basis. -/
noncomputable def gramMatrix {ι : Type v} [Fintype ι] (e : Basis ι ℤ L) : Matrix ι ι ℤ :=
  fun i j ↦ L.integralForm (e i) (e j)

open Classical in
/-- A Gram-matrix entry is the value of the integral form on the corresponding basis vectors. -/
@[simp]
theorem gramMatrix_apply {ι : Type v} [Fintype ι] (e : Basis ι ℤ L) (i j : ι) :
    L.gramMatrix e i j = L.integralForm (e i) (e j) :=
  (rfl)

/-- The Gram matrix is Mathlib's matrix of the restricted integral bilinear form. -/
theorem gramMatrix_eq_toMatrix {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    L.gramMatrix e = LinearMap.BilinForm.toMatrix e L.integralForm := by
  ext i j
  rw [gramMatrix_apply, LinearMap.BilinForm.toMatrix_apply]

open Classical in
/-- Casting a Gram-matrix entry to `ℚ` recovers the ambient rational form. -/
theorem intCast_gramMatrix_apply {ι : Type v} [Fintype ι] (e : Basis ι ℤ L) (i j : ι) :
    (L.gramMatrix e i j : ℚ) = L.form (e i : V) (e j : V) := by
  rw [gramMatrix_apply, integralForm_cast]

open Classical in
/-- The Gram matrix of a symmetric integral lattice is symmetric. -/
theorem gramMatrix_isSymm {ι : Type v} [Fintype ι] (e : Basis ι ℤ L) :
    (L.gramMatrix e).IsSymm := by
  rw [gramMatrix_eq_toMatrix, LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm]
  exact L.isSymm_integralForm

/-- Extending the carrier basis and the entries of its Gram matrix to `ℚ` gives the matrix of the
ambient rational form. -/
theorem map_gramMatrix {ι : Type v} [Fintype ι] [DecidableEq ι] (e : Basis ι ℤ L) :
    (L.gramMatrix e).map (algebraMap ℤ ℚ) =
      LinearMap.BilinForm.toMatrix (e.extendOfIsLattice ℚ) L.form := by
  ext i j
  simp only [Matrix.map_apply]
  -- `Matrix.map` displays the integer cast as `algebraMap`; the entry lemma uses cast notation.
  change (L.gramMatrix e i j : ℚ) =
    LinearMap.BilinForm.toMatrix (e.extendOfIsLattice ℚ) L.form i j
  rw [intCast_gramMatrix_apply,
    LinearMap.BilinForm.toMatrix_apply, Basis.extendOfIsLattice_apply,
    Basis.extendOfIsLattice_apply]

/-- The signed determinant of the Gram matrix in a carrier basis. -/
noncomputable def gramDet {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) : ℤ :=
  Matrix.det (L.gramMatrix e)

/-- Casting the signed Gram determinant to `ℚ` gives the determinant of the ambient rational form
in the extended basis. -/
theorem intCast_gramDet {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    (L.gramDet e : ℚ) =
      Matrix.det (LinearMap.BilinForm.toMatrix (e.extendOfIsLattice ℚ) L.form) := by
  rw [gramDet, Int.cast_det]
  exact congrArg Matrix.det (map_gramMatrix L e)

open Classical in
/-- Reindexing a carrier basis simultaneously reindexes the rows and columns of its Gram matrix. -/
theorem gramMatrix_reindex {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    (e : Basis ι ℤ L) (σ : ι ≃ κ) :
    L.gramMatrix (e.reindex σ) = (L.gramMatrix e).submatrix σ.symm σ.symm := by
  classical
  ext i j
  simp only [gramMatrix_apply, Basis.reindex_apply, Matrix.submatrix_apply]

/-- Reindexing a carrier basis does not change its signed Gram determinant. -/
theorem gramDet_reindex {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : Basis ι ℤ L) (σ : ι ≃ κ) :
    L.gramDet (e.reindex σ) = L.gramDet e := by
  rw [gramDet, gramMatrix_reindex, Matrix.det_submatrix_equiv_self, gramDet]

/-- Two carrier bases with the same index type give the same signed Gram determinant. -/
private theorem gramDet_eq_gramDet_sameIndex {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e f : Basis ι ℤ L) : L.gramDet e = L.gramDet f := by
  have hchange : IsUnit (f.toMatrix e).det := f.isUnit_det e
  rw [Int.isUnit_iff, ← sq_eq_one_iff] at hchange
  have hmatrix :
      (f.toMatrix e).transpose * LinearMap.BilinForm.toMatrix f L.integralForm * f.toMatrix e =
        LinearMap.BilinForm.toMatrix e L.integralForm :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := f) e L.integralForm
  rw [gramDet, gramDet, gramMatrix_eq_toMatrix, gramMatrix_eq_toMatrix]
  calc
    Matrix.det (LinearMap.BilinForm.toMatrix e L.integralForm) =
        Matrix.det ((f.toMatrix e).transpose *
          LinearMap.BilinForm.toMatrix f L.integralForm * f.toMatrix e) :=
      congrArg Matrix.det hmatrix.symm
    _ = (f.toMatrix e).det ^ 2 *
        Matrix.det (LinearMap.BilinForm.toMatrix f L.integralForm) := by
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      ring
    _ = Matrix.det (LinearMap.BilinForm.toMatrix f L.integralForm) := by
      rw [hchange, one_mul]

/-- **The signed Gram determinant is independent of the carrier basis.** This permits both the
index type and the basis to change. -/
theorem gramDet_eq_gramDet {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : Basis ι ℤ L) (f : Basis κ ℤ L) :
    L.gramDet e = L.gramDet f := by
  let σ : ι ≃ κ := e.indexEquiv f
  calc
    L.gramDet e = L.gramDet (e.reindex σ) := (gramDet_reindex L e σ).symm
    _ = L.gramDet f := gramDet_eq_gramDet_sameIndex L _ _

/-- A Gram determinant is nonzero exactly when the ambient rational form is nondegenerate. -/
theorem gramDet_ne_zero_iff {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    L.gramDet e ≠ 0 ↔ L.form.Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (e.extendOfIsLattice ℚ),
    ← intCast_gramDet]
  exact (Int.cast_ne_zero (α := ℚ) (n := L.gramDet e)).symm

end GramMatrix

section Invariants

/-- The basis-independent signed determinant of an integral lattice. -/
noncomputable def determinant (L : IntegralLattice V) : ℤ :=
  L.gramDet (Module.Free.chooseBasis ℤ L)

/-- The signed determinant agrees with the determinant of the Gram matrix in every carrier basis. -/
theorem determinant_eq_gramDet (L : IntegralLattice V) {ι : Type v} [Fintype ι]
    [DecidableEq ι] (e : Basis ι ℤ L) :
    L.determinant = L.gramDet e := by
  classical
  exact L.gramDet_eq_gramDet _ _

/-- The basis-independent determinant is nonzero exactly when the ambient rational form is
nondegenerate. -/
theorem determinant_ne_zero_iff (L : IntegralLattice V) :
    L.determinant ≠ 0 ↔ L.form.Nondegenerate := by
  classical
  rw [determinant, gramDet_ne_zero_iff]

/-- The nonnegative discriminant of an integral lattice is the absolute value of its signed
determinant. -/
noncomputable def discriminant (L : IntegralLattice V) : ℕ :=
  L.determinant.natAbs

/-- The discriminant is the absolute value of the Gram determinant in every carrier basis. -/
theorem discriminant_eq_natAbs_gramDet (L : IntegralLattice V) {ι : Type v} [Fintype ι]
    [DecidableEq ι] (e : Basis ι ℤ L) :
    L.discriminant = (L.gramDet e).natAbs := by
  classical
  rw [discriminant, L.determinant_eq_gramDet e]

/-- The discriminant is positive exactly when the ambient rational form is nondegenerate. -/
theorem discriminant_pos_iff (L : IntegralLattice V) :
    0 < L.discriminant ↔ L.form.Nondegenerate := by
  classical
  rw [discriminant, Int.natAbs_pos, determinant_ne_zero_iff]

end Invariants

end TauCeti.IntegralLattice
