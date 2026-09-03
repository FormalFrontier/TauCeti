/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Isometry
import Mathlib.LinearAlgebra.Determinant

/-!
# Gram determinants of integral lattices

This file attaches an integral Gram matrix to every basis of an integral lattice. Its determinant
is independent of the carrier basis: an integral change-of-basis matrix has determinant `1` or
`-1`, and the Gram matrix changes by multiplication by that matrix and its transpose. The resulting
basis-free signed determinant and its absolute value are the determinant and discriminant of the
lattice. An integral-lattice isometry carries every carrier basis to one with the same Gram matrix,
so it preserves both basis-free invariants.

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
* `TauCeti.IntegralLattice.gramMatrix_ofGramMatrix`: the Gram matrix of `ofGramMatrix` in its
  canonical basis is `G`.
* `TauCeti.IntegralLattice.determinant_ofGramMatrix`: the signed determinant of `ofGramMatrix` is
  the determinant of `G`.
* `TauCeti.IntegralLattice.isNondegenerate_ofGramMatrix`: a nonsingular Gram matrix produces a
  nondegenerate integral lattice.
* `TauCeti.IntegralLattice.discriminant_ofGramMatrix`: the discriminant of `ofGramMatrix` is the
  absolute determinant of `G`.
* `TauCeti.IntegralLattice.Isometry.determinant_eq` and `Isometry.discriminant_eq`: isometry
  invariance of the basis-free invariants.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
* `TauCetiRoadmap/IntegralLattices/README.md`, Layer 1.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u v w

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable {W : Type w} [AddCommGroup W] [Module ℚ W]

section GramMatrix

variable (L : IntegralLattice V)

/-- The integral Gram matrix of a carrier basis. -/
noncomputable def gramMatrix {ι : Type v} (e : Basis ι ℤ L) : Matrix ι ι ℤ :=
  LinearMap.BilinForm.toMatrixAux e L.integralForm

/-- A Gram-matrix entry is the value of the integral form on the corresponding basis vectors. -/
@[simp]
theorem gramMatrix_apply {ι : Type v} (e : Basis ι ℤ L) (i j : ι) :
    L.gramMatrix e i j = L.integralForm (e i) (e j) :=
  LinearMap.BilinForm.toMatrixAux_apply L.integralForm e i j

/-- The Gram matrix is Mathlib's matrix of the restricted integral bilinear form. -/
theorem gramMatrix_eq_toMatrix {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    L.gramMatrix e = LinearMap.BilinForm.toMatrix e L.integralForm :=
  LinearMap.BilinForm.toMatrixAux_eq e L.integralForm

/-- Casting a Gram-matrix entry to `ℚ` recovers the ambient rational form. -/
theorem intCast_gramMatrix_apply {ι : Type v} (e : Basis ι ℤ L) (i j : ι) :
    (L.gramMatrix e i j : ℚ) = L.form (e i : V) (e j : V) := by
  rw [gramMatrix_apply, integralForm_cast]

/-- The Gram matrix of a symmetric integral lattice is symmetric. -/
theorem isSymm_gramMatrix {ι : Type v} (e : Basis ι ℤ L) :
    (L.gramMatrix e).IsSymm := by
  ext i j
  rw [Matrix.transpose_apply, gramMatrix_apply, gramMatrix_apply, L.isSymm_integralForm.eq]

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

/-- Unfolding the signed Gram determinant to the matrix determinant. -/
theorem gramDet_def {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    L.gramDet e = Matrix.det (L.gramMatrix e) :=
  (rfl)

/-- Casting the signed Gram determinant to `ℚ` gives the determinant of the ambient rational form
in the extended basis. -/
theorem intCast_gramDet {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    (L.gramDet e : ℚ) =
      Matrix.det (LinearMap.BilinForm.toMatrix (e.extendOfIsLattice ℚ) L.form) := by
  rw [gramDet_def, Int.cast_det]
  exact congrArg Matrix.det (map_gramMatrix L e)

/-- Reindexing a carrier basis simultaneously reindexes the rows and columns of its Gram matrix. -/
theorem gramMatrix_reindex {ι : Type v} {κ : Type w}
    (e : Basis ι ℤ L) (σ : ι ≃ κ) :
    L.gramMatrix (e.reindex σ) = (L.gramMatrix e).submatrix σ.symm σ.symm := by
  ext i j
  simp only [gramMatrix_apply, Basis.reindex_apply, Matrix.submatrix_apply]

/-- Reindexing a carrier basis does not change its signed Gram determinant. -/
theorem gramDet_reindex {ι : Type v} {κ : Type w} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : Basis ι ℤ L) (σ : ι ≃ κ) :
    L.gramDet (e.reindex σ) = L.gramDet e := by
  rw [gramDet_def, gramMatrix_reindex, Matrix.det_submatrix_equiv_self, ← gramDet_def]

/-- Two carrier bases with the same index type give the same signed Gram determinant. -/
private theorem gramDet_eq_gramDet_sameIndex {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e f : Basis ι ℤ L) : L.gramDet e = L.gramDet f := by
  have hchange : IsUnit (f.toMatrix e).det := f.isUnit_det e
  rw [Int.isUnit_iff, ← sq_eq_one_iff] at hchange
  have hmatrix :
      (f.toMatrix e).transpose * LinearMap.BilinForm.toMatrix f L.integralForm * f.toMatrix e =
        LinearMap.BilinForm.toMatrix e L.integralForm :=
    LinearMap.BilinForm.toMatrix_mul_basis_toMatrix (b := f) e L.integralForm
  rw [gramDet_def, gramDet_def, gramMatrix_eq_toMatrix, gramMatrix_eq_toMatrix]
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
@[simp]
theorem gramDet_ne_zero_iff {ι : Type v} [Fintype ι] [DecidableEq ι]
    (e : Basis ι ℤ L) :
    L.gramDet e ≠ 0 ↔ L.form.Nondegenerate := by
  rw [LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (e.extendOfIsLattice ℚ),
    ← intCast_gramDet]
  exact (Int.cast_ne_zero (α := ℚ) (n := L.gramDet e)).symm

/-- The Gram matrix of `ofGramMatrix b G hG` in its canonical carrier basis is `G`. -/
@[simp]
theorem gramMatrix_ofGramMatrix {ι : Type v} [Fintype ι]
    (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    (ofGramMatrix b G hG).gramMatrix (ofGramMatrix.basis b G hG) = G := by
  ext i j
  rw [gramMatrix_apply, integralForm_ofGramMatrix_apply]

/-- The signed Gram determinant of `ofGramMatrix b G hG` in its canonical carrier basis is the
determinant of `G`. -/
@[simp]
theorem gramDet_ofGramMatrix {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    (ofGramMatrix b G hG).gramDet (ofGramMatrix.basis b G hG) = G.det := by
  rw [gramDet_def, gramMatrix_ofGramMatrix]

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

/-- The basis-independent signed determinant of `ofGramMatrix b G hG` is the determinant of `G`. -/
@[simp]
theorem determinant_ofGramMatrix {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    (ofGramMatrix b G hG).determinant = G.det := by
  rw [determinant_eq_gramDet _ (ofGramMatrix.basis b G hG), gramDet_ofGramMatrix]

/-- The basis-independent determinant is nonzero exactly when the ambient rational form is
nondegenerate. -/
@[simp]
theorem determinant_ne_zero_iff (L : IntegralLattice V) :
    L.determinant ≠ 0 ↔ L.form.Nondegenerate := by
  classical
  rw [determinant, gramDet_ne_zero_iff]

open Classical in
/-- An integral lattice constructed from a nonsingular Gram matrix is nondegenerate. -/
theorem isNondegenerate_ofGramMatrix {ι : Type v} [Fintype ι]
    (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) (hdet : G.det ≠ 0) :
    (ofGramMatrix b G hG).IsNondegenerate :=
  ⟨(determinant_ne_zero_iff _).mp (by
    rw [determinant_ofGramMatrix]
    exact hdet)⟩

/-- The nonnegative discriminant of an integral lattice is the absolute value of its signed
determinant. -/
noncomputable def discriminant (L : IntegralLattice V) : ℕ :=
  L.determinant.natAbs

/-- Unfolding the discriminant to the absolute value of the signed determinant. -/
theorem discriminant_def (L : IntegralLattice V) :
    L.discriminant = L.determinant.natAbs :=
  (rfl)

/-- The discriminant is the absolute value of the Gram determinant in every carrier basis. -/
theorem discriminant_eq_natAbs_gramDet (L : IntegralLattice V) {ι : Type v} [Fintype ι]
    [DecidableEq ι] (e : Basis ι ℤ L) :
    L.discriminant = (L.gramDet e).natAbs := by
  classical
  rw [discriminant_def, L.determinant_eq_gramDet e]

/-- The discriminant of `ofGramMatrix b G hG` is the absolute value of the determinant of `G`. -/
@[simp]
theorem discriminant_ofGramMatrix {ι : Type v} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℚ V) (G : Matrix ι ι ℤ) (hG : G.IsSymm) :
    (ofGramMatrix b G hG).discriminant = G.det.natAbs := by
  rw [discriminant_def, determinant_ofGramMatrix]

/-- The discriminant is positive exactly when the ambient rational form is nondegenerate. -/
@[simp]
theorem discriminant_pos_iff (L : IntegralLattice V) :
    0 < L.discriminant ↔ L.form.Nondegenerate := by
  classical
  rw [discriminant_def, Int.natAbs_pos, determinant_ne_zero_iff]

end Invariants

namespace Isometry

variable {L : IntegralLattice V} {M : IntegralLattice W}

-- The two transport lemmas below are not registered with `simp`: `carrierBasisEquiv_apply` is
-- itself a `simp` lemma, so their left-hand sides are not in simp-normal form.

/-- Transporting a carrier basis along an isometry preserves its Gram matrix entrywise. -/
theorem gramMatrix_carrierBasisEquiv (e : Isometry L M) {ι : Type v} (b : Basis ι ℤ L) :
    M.gramMatrix (e.carrierBasisEquiv ι b) = L.gramMatrix b := by
  ext i j
  rw [M.gramMatrix_apply, L.gramMatrix_apply, e.carrierBasisEquiv_apply,
    Basis.map_apply, Basis.map_apply, e.carrierEquiv_map_integralForm]

/-- Transporting a carrier basis along an isometry preserves its signed Gram determinant. -/
theorem gramDet_carrierBasisEquiv (e : Isometry L M) {ι : Type v} [Fintype ι]
    [DecidableEq ι] (b : Basis ι ℤ L) :
    M.gramDet (e.carrierBasisEquiv ι b) = L.gramDet b := by
  rw [M.gramDet_def, L.gramDet_def, e.gramMatrix_carrierBasisEquiv]

/-- The basis-independent signed determinant is invariant under integral-lattice isometry. -/
theorem determinant_eq (e : Isometry L M) : L.determinant = M.determinant := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  calc
    L.determinant = L.gramDet b := L.determinant_eq_gramDet b
    _ = M.gramDet (e.carrierBasisEquiv _ b) := (e.gramDet_carrierBasisEquiv b).symm
    _ = M.determinant := (M.determinant_eq_gramDet (e.carrierBasisEquiv _ b)).symm

/-- The nonnegative discriminant is invariant under integral-lattice isometry. -/
theorem discriminant_eq (e : Isometry L M) : L.discriminant = M.discriminant := by
  rw [L.discriminant_def, M.discriminant_def, e.determinant_eq]

end Isometry

end TauCeti.IntegralLattice
