/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.charpoly`, `Matrix.eval_charpoly` and `Matrix.mem_spectrum_iff_isRoot_charpoly`.
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
-- `Matrix.charpoly_natDegree_eq_dim` and `Matrix.charpoly_monic`, for the cardinality bound. Not
-- `public`: these are used only in proofs.
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
-- `Matrix.exists_mulVec_eq_zero_iff`, the singularity criterion the search rests on; this also
-- supplies `Matrix.isUnit_iff_isUnit_det` and `Matrix.coe_units_inv`. Not `public` for the same
-- reason.
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
-- `Matrix.spectrum_toLin'`, `Matrix.spectrum_diagonal`,
-- `Module.End.hasEigenvalue_iff_mem_spectrum`, and the `spectrum` API itself, including
-- `spectrum.units_conjugate`.
public import Mathlib.LinearAlgebra.Eigenspace.Matrix
-- `ZMod 3` as a field, for the worked example at the end. Not `public`: nothing in the API
-- mentions it.
import Mathlib.Algebra.Field.ZMod
-- The `!![a, b; c, d]` notation, for the same example, and not `public` for the same reason.
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Searching a finite field for the eigenvalues of a matrix

Over a *finite* field the eigenvalues of a square matrix can be found by brute force: run through
the field and keep the scalars `a` at which `a • 1 - A` is singular. This file defines that search,
`TauCeti.eigenvalueSearch`, as a genuine `def` on decidable data, and proves that it finds exactly
the eigenvalues: as a set, `eigenvalueSearch A` is the spectrum of `A`
(`TauCeti.coe_eigenvalueSearch`).

Mathlib has the spectrum, the eigenvalues of an endomorphism, and the identification of both with
the roots of the characteristic polynomial, but each of those is `Set`- or `Multiset`-valued and
none of them computes: `Polynomial` is a `Finsupp`, `spectrum` is a `Set`, and `Finset.toList` is
noncomputable. What is added here is the computable `Finset` together with the theorem that it
agrees with Mathlib's notion, so that a program may use the `Finset` while its correctness proof
uses the whole spectrum API.

This search is the finite-field linear algebra of the Burnside--Dixon--Schneider character-table
algorithm, which refines a partition of the class indices by splitting each block along the
eigenvalues of a class-multiplication matrix reduced mod `p`. That is why the matrix is indexed by
an arbitrary `Fintype` rather than by `Fin n`: there the index type is `ConjClasses G`. It is also
why the eigenvector characterization is recorded on both sides (`*ᵥ` and `ᵥ*`): the eigenrows of
that algorithm are *left* eigenvectors.

## Main definitions

* `TauCeti.eigenvalueSearch`: the `Finset` of eigenvalues of a matrix over a finite field.

## Main results

* `TauCeti.coe_eigenvalueSearch`: the search returns exactly the spectrum.
* `TauCeti.mem_eigenvalueSearch_iff_exists_mulVec` and
  `TauCeti.mem_eigenvalueSearch_iff_exists_vecMul`: membership means a nonzero right, respectively
  left, eigenvector exists.
* `TauCeti.card_eigenvalueSearch_le`: at most `Fintype.card n` scalars are returned.
* `TauCeti.decidableMemSpectrum`: membership in the spectrum is therefore decidable.

## References

This implements the object `eigenvalueSearch` of Layer 6 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
and its
[suggested declarations](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/Suggested.lean).
-/

public section

namespace TauCeti

open Matrix Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n F} {a : F}

/-- The eigenvalues of `A`, found by searching the finite field `F` for the scalars `a` at which
`a • 1 - A` is singular. By `TauCeti.coe_eigenvalueSearch` this is the spectrum of `A`.

A `Finset` rather than a list: the search has no preferred order on the field, and eigenvalues
carry no multiplicity here. The body is exposed because consumers of an executable algorithm
evaluate it, and kernel reduction needs the definition. -/
@[expose] def eigenvalueSearch (A : Matrix n n F) : Finset F :=
  Finset.univ.filter fun a => (Matrix.scalar n a - A).det = 0

/-- The scalars the search keeps are those at which `a • 1 - A` has vanishing determinant. -/
@[simp] theorem mem_eigenvalueSearch :
    a ∈ eigenvalueSearch A ↔ (Matrix.scalar n a - A).det = 0 := by
  rw [eigenvalueSearch, Finset.mem_filter]
  simp

/-- A scalar the search rejects is one at which `a • 1 - A` is invertible. -/
theorem notMem_eigenvalueSearch_iff_isUnit :
    a ∉ eigenvalueSearch A ↔ IsUnit (Matrix.scalar n a - A) := by
  rw [mem_eigenvalueSearch, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ne_eq]

/-- The membership test in the form the algorithm uses it: `a` is an eigenvalue exactly when
`A - a • 1` is singular. -/
theorem mem_eigenvalueSearch_iff_det_sub_smul_eq_zero :
    a ∈ eigenvalueSearch A ↔ (A - a • (1 : Matrix n n F)).det = 0 := by
  have h : Matrix.scalar n a - A = -(A - a • (1 : Matrix n n F)) := by
    rw [neg_sub, Matrix.scalar_apply, smul_one_eq_diagonal]
  rw [mem_eigenvalueSearch, h, Matrix.det_neg]
  simp

/-- The search keeps exactly the roots of the characteristic polynomial. -/
theorem mem_eigenvalueSearch_iff_isRoot_charpoly :
    a ∈ eigenvalueSearch A ↔ A.charpoly.IsRoot a := by
  rw [mem_eigenvalueSearch, IsRoot.def, Matrix.eval_charpoly]

/-- **Correctness of the search**: it returns exactly the spectrum of `A`. -/
@[simp] theorem coe_eigenvalueSearch (A : Matrix n n F) :
    (eigenvalueSearch A : Set F) = spectrum F A := by
  ext a
  rw [Finset.mem_coe, mem_eigenvalueSearch_iff_isRoot_charpoly,
    Matrix.mem_spectrum_iff_isRoot_charpoly]

/-- The pointwise form of `TauCeti.coe_eigenvalueSearch`. -/
theorem mem_eigenvalueSearch_iff_mem_spectrum : a ∈ eigenvalueSearch A ↔ a ∈ spectrum F A := by
  rw [← Finset.mem_coe, coe_eigenvalueSearch]

/-- The search finds the eigenvalues of the endomorphism that `A` defines on `n → F`. -/
theorem mem_eigenvalueSearch_iff_hasEigenvalue :
    a ∈ eigenvalueSearch A ↔ Module.End.HasEigenvalue (Matrix.toLin' A) a := by
  rw [mem_eigenvalueSearch_iff_mem_spectrum, ← Matrix.spectrum_toLin',
    Module.End.hasEigenvalue_iff_mem_spectrum]

/-- The scalar-minus-matrix system is the corresponding eigenvector equation. -/
theorem scalar_sub_mulVec_eq_zero_iff {R : Type*} [NonUnitalNonAssocRing R]
    (A : Matrix n n R) (a : R) (v : n → R) :
    (Matrix.diagonal (fun _ => a) - A) *ᵥ v = 0 ↔ A *ᵥ v = a • v := by
  rw [Matrix.sub_mulVec, sub_eq_zero, eq_comm]
  -- Mathlib's `Matrix.diagonal_const_mulVec` requires `NonAssocSemiring`, whereas this result does
  -- not need a multiplicative identity.
  have hdiag : (Matrix.diagonal (fun _ => a)) *ᵥ v = a • v := by
    funext i
    rw [Matrix.mulVec_diagonal]
    rfl
  rw [hdiag]

/-- A scalar is found by the search exactly when it has a nonzero eigenvector. -/
theorem mem_eigenvalueSearch_iff_exists_mulVec :
    a ∈ eigenvalueSearch A ↔ ∃ v ≠ 0, A *ᵥ v = a • v := by
  rw [mem_eigenvalueSearch, ← Matrix.exists_mulVec_eq_zero_iff]
  refine exists_congr fun v => and_congr_right fun _ => ?_
  exact scalar_sub_mulVec_eq_zero_iff A a v

/-- A matrix and its transpose have the same eigenvalues. -/
@[simp] theorem eigenvalueSearch_transpose (A : Matrix n n F) :
    eigenvalueSearch Aᵀ = eigenvalueSearch A := by
  ext a
  rw [mem_eigenvalueSearch, mem_eigenvalueSearch, ← Matrix.det_transpose,
    Matrix.transpose_sub, Matrix.transpose_transpose, Matrix.scalar_apply,
    Matrix.diagonal_transpose]

/-- A scalar is found by the search exactly when it has a nonzero *left* eigenvector: a row vector
`v` with `v ᵥ* A = a • v`. This is the orientation of the Dixon--Schneider eigenrows. -/
theorem mem_eigenvalueSearch_iff_exists_vecMul :
    a ∈ eigenvalueSearch A ↔ ∃ v ≠ 0, v ᵥ* A = a • v := by
  rw [← eigenvalueSearch_transpose, mem_eigenvalueSearch_iff_exists_mulVec]
  simp [Matrix.mulVec_transpose]

/-- The eigenvalues of `A` are the distinct roots of its characteristic polynomial. -/
theorem eigenvalueSearch_eq_toFinset_roots (A : Matrix n n F) :
    eigenvalueSearch A = A.charpoly.roots.toFinset := by
  ext a
  rw [Multiset.mem_toFinset, mem_roots A.charpoly_monic.ne_zero,
    mem_eigenvalueSearch_iff_isRoot_charpoly]

/-- A matrix has at most as many eigenvalues as it has rows. -/
theorem card_eigenvalueSearch_le (A : Matrix n n F) :
    (eigenvalueSearch A).card ≤ Fintype.card n := by
  rw [eigenvalueSearch_eq_toFinset_roots]
  calc A.charpoly.roots.toFinset.card
      ≤ Multiset.card A.charpoly.roots := Multiset.toFinset_card_le _
    _ ≤ A.charpoly.natDegree := A.charpoly.card_roots'
    _ = Fintype.card n := A.charpoly_natDegree_eq_dim

/-- The eigenvalues of a diagonal matrix are its diagonal entries. -/
@[simp] theorem eigenvalueSearch_diagonal (d : n → F) :
    eigenvalueSearch (Matrix.diagonal d) = Finset.univ.image d := by
  apply Finset.coe_injective
  rw [coe_eigenvalueSearch, spectrum_diagonal, Finset.coe_image, Finset.coe_univ, Set.image_univ]

/-- The only eigenvalue of a scalar matrix is the scalar. This is not `@[simp]`: simp already
takes the left-hand side to `Finset.image (fun _ => a) Finset.univ`, and collapsing that image
needs the nonemptiness hypothesis. -/
theorem eigenvalueSearch_scalar [Nonempty n] (a : F) :
    eigenvalueSearch (Matrix.scalar n a) = {a} := by
  rw [Matrix.scalar_apply, eigenvalueSearch_diagonal, Finset.image_const Finset.univ_nonempty]

/-- The only eigenvalue of the zero matrix is `0`. -/
@[simp] theorem eigenvalueSearch_zero [Nonempty n] :
    eigenvalueSearch (0 : Matrix n n F) = {0} := by
  simpa using eigenvalueSearch_scalar (n := n) (0 : F)

/-- The only eigenvalue of the identity matrix is `1`. -/
@[simp] theorem eigenvalueSearch_one [Nonempty n] :
    eigenvalueSearch (1 : Matrix n n F) = {1} := by
  simpa using eigenvalueSearch_scalar (n := n) (1 : F)

/-- Similar matrices have the same eigenvalues. -/
theorem eigenvalueSearch_conjugate {M : Matrix n n F} (hM : IsUnit M) (A : Matrix n n F) :
    eigenvalueSearch (M * A * M⁻¹) = eigenvalueSearch A := by
  apply Finset.coe_injective
  rw [coe_eigenvalueSearch, coe_eigenvalueSearch, ← hM.unit_spec, ← Matrix.coe_units_inv,
    spectrum.units_conjugate]

/-- A matrix with no rows has no eigenvalues: its `0 × 0` determinant is `1`. -/
@[simp] theorem eigenvalueSearch_eq_empty_of_isEmpty [IsEmpty n] (A : Matrix n n F) :
    eigenvalueSearch A = ∅ := by
  ext a
  simp

/-- Membership in the spectrum of a matrix over a finite field is decidable, by running the
search. -/
instance decidableMemSpectrum (a : F) (A : Matrix n n F) : Decidable (a ∈ spectrum F A) :=
  decidable_of_iff _ mem_eigenvalueSearch_iff_mem_spectrum

/-- The search really runs: over `ZMod 3` the matrix `!![0, 1; 1, 0]` has eigenvalues `1` and
`-1 = 2`. -/
example : eigenvalueSearch (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod 3)) = {1, 2} := by
  decide

end TauCeti
