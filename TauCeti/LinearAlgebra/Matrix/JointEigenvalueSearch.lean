/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.LinearAlgebra.Matrix.EigenvalueSearch
public import TauCeti.LinearAlgebra.Matrix.Echelon.KernelBasis

/-!
# Searching for common eigenvectors over a finite field

For finitely many square matrices over a finite field, common eigenvectors can be found by an
exhaustive but executable search. First choose one eigenvalue of each matrix using
`TauCeti.eigenvalueSearch`. For a tuple `a`, stack the systems
`(a i • 1 - A i) v = 0` into one rectangular matrix and compute its kernel with
`TauCeti.kernelBasis`. The tuple is retained exactly when that kernel basis is nonempty.

This file implements that search and proves that its output is precisely the tuples admitting a
nonzero common eigenvector. It deliberately returns the full kernel basis as a separate
definition: the Dixon--Schneider algorithm needs those bases to refine common eigenspaces until
they are one-dimensional, rather than merely deciding whether a tuple occurs.

## Main definitions

* `TauCeti.jointEigenspaceMatrix`: the matrix obtained by stacking all the eigenvector equations.
* `TauCeti.jointEigenspaceBasis`: a computable basis of the corresponding common eigenspace.
* `TauCeti.eigenvalueTupleSearch`: the finite product of the individual eigenvalue searches.
* `TauCeti.jointEigenvalueSearch`: the tuples with nonzero common eigenspace.
* `TauCeti.leftJointEigenspaceBasis` and `TauCeti.leftJointEigenvalueSearch`: the corresponding
  objects for the common eigenrows used by Dixon--Schneider.

## Main results

* `TauCeti.jointEigenspaceMatrix_mulVec_eq_zero_iff`: the stacked system expresses exactly the
  common eigenvector equations.
* `TauCeti.nonempty_jointEigenspaceBasis_iff`: its computed basis is nonempty exactly when a
  nonzero common eigenvector exists.
* `TauCeti.mem_jointEigenvalueSearch`: correctness of the executable tuple search.

## References

Layer 6 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
requires an eigenvector search over `ZMod p` which combines `eigenvalueSearch` with
`kernelBasis`. This is the common-eigenspace search at the core of that refinement.
-/

public section

namespace TauCeti

open Matrix

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {m n : ℕ}

/-- The rectangular matrix formed by stacking the systems
`(a i • 1 - A i) v = 0`, one block of `n` rows for each `i : Fin m`.

The product row index is flattened to `Fin (m * n)` because `TauCeti.kernelBasis` operates on
matrices with `Fin` row and column types. -/
@[expose] def jointEigenspaceMatrix (A : Fin m → Matrix (Fin n) (Fin n) F)
    (a : Fin m → F) : Matrix (Fin (m * n)) (Fin n) F := fun k j =>
  let ij := finProdFinEquiv.symm k
  (Matrix.scalar (Fin n) (a ij.1) - A ij.1) ij.2 j

omit [Fintype F] [DecidableEq F] in
/-- An entry in the `i`-th block of `TauCeti.jointEigenspaceMatrix`. -/
@[simp]
theorem jointEigenspaceMatrix_apply (A : Fin m → Matrix (Fin n) (Fin n) F)
    (a : Fin m → F) (i : Fin m) (j k : Fin n) :
    jointEigenspaceMatrix A a (finProdFinEquiv (i, j)) k =
      (Matrix.scalar (Fin n) (a i) - A i) j k := by
  simp [jointEigenspaceMatrix]

omit [Fintype F] [DecidableEq F] in
/-- The stacked matrix annihilates `v` exactly when `v` is an eigenvector (possibly zero) of
every `A i`, with eigenvalue `a i`. -/
theorem jointEigenspaceMatrix_mulVec_eq_zero_iff
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) (v : Fin n → F) :
    jointEigenspaceMatrix A a *ᵥ v = 0 ↔ ∀ i, A i *ᵥ v = a i • v := by
  constructor
  · intro h i
    have hi : (Matrix.scalar (Fin n) (a i) - A i) *ᵥ v = 0 := by
      funext j
      simpa only [Matrix.mulVec, jointEigenspaceMatrix_apply, Pi.zero_apply] using
        congrFun h (finProdFinEquiv (i, j))
    rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.scalar_apply, Matrix.diagonal_const_mulVec,
      eq_comm] at hi
    exact hi
  · intro h
    funext k
    let ij := finProdFinEquiv.symm k
    have hi : (Matrix.scalar (Fin n) (a ij.1) - A ij.1) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.scalar_apply, Matrix.diagonal_const_mulVec,
        eq_comm]
      exact h ij.1
    rw [show k = finProdFinEquiv ij by exact (finProdFinEquiv.apply_symm_apply k).symm]
    simpa [Matrix.mulVec, jointEigenspaceMatrix] using congrFun hi ij.2

/-- A computable basis of the simultaneous eigenspace for the eigenvalue tuple `a`. -/
@[expose] def jointEigenspaceBasis (A : Fin m → Matrix (Fin n) (Fin n) F)
    (a : Fin m → F) : List (Fin n → F) :=
  kernelBasis (jointEigenspaceMatrix A a)

omit [Fintype F] in
/-- Every vector returned by `TauCeti.jointEigenspaceBasis` satisfies all the eigenvector
equations. -/
theorem mulVec_eq_smul_of_mem_jointEigenspaceBasis
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F} {v : Fin n → F}
    (hv : v ∈ jointEigenspaceBasis A a) : ∀ i, A i *ᵥ v = a i • v := by
  rw [← jointEigenspaceMatrix_mulVec_eq_zero_iff A a v]
  exact mulVec_eq_zero_of_mem_kernelBasis _ hv

omit [Fintype F] in
/-- The vectors returned for a common eigenspace are linearly independent. -/
theorem linearIndepOn_jointEigenspaceBasis
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) :
    LinearIndepOn F id {v : Fin n → F | v ∈ jointEigenspaceBasis A a} :=
  linearIndepOn_kernelBasis _

omit [Fintype F] in
/-- The vectors returned for a common eigenspace span the kernel of the stacked system. -/
theorem span_jointEigenspaceBasis
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) :
    Submodule.span F {v : Fin n → F | v ∈ jointEigenspaceBasis A a} =
      LinearMap.ker (jointEigenspaceMatrix A a).mulVecLin :=
  span_kernelBasis _

omit [Fintype F] in
/-- The common-eigenspace basis contains no duplicate vectors. -/
theorem nodup_jointEigenspaceBasis
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) :
    (jointEigenspaceBasis A a).Nodup :=
  nodup_kernelBasis _

omit [Fintype F] in
/-- The number of computed basis vectors is the nullity of the stacked system. In particular,
the executable test that this length is one is the test that refinement has reached a
one-dimensional common eigenspace. -/
theorem length_jointEigenspaceBasis
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) :
    (jointEigenspaceBasis A a).length = n - (jointEigenspaceMatrix A a).rank :=
  length_kernelBasis _

omit [Fintype F] in
/-- The common-eigenspace basis is nonempty exactly when the eigenvalue tuple has a nonzero
common eigenvector. -/
theorem nonempty_jointEigenspaceBasis_iff
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) :
    jointEigenspaceBasis A a ≠ [] ↔ ∃ v ≠ 0, ∀ i, A i *ᵥ v = a i • v := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ h
    refine ⟨v, ?_, mulVec_eq_smul_of_mem_jointEigenspaceBasis hv⟩
    exact (linearIndepOn_jointEigenspaceBasis A a).ne_zero hv
  · rintro ⟨v, hv, heig⟩ hnil
    have hker : v ∈ LinearMap.ker (jointEigenspaceMatrix A a).mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
        jointEigenspaceMatrix_mulVec_eq_zero_iff]
      exact heig
    have hspan := span_jointEigenspaceBasis A a
    rw [hnil] at hspan
    simp only [List.not_mem_nil, Set.ofPred_false, Submodule.span_empty] at hspan
    rw [← hspan] at hker
    exact hv ((Submodule.mem_bot F).mp hker)

/-- The finite product of the individual matrix eigenvalue searches. -/
@[expose] def eigenvalueTupleSearch (A : Fin m → Matrix (Fin n) (Fin n) F) :
    Finset (Fin m → F) :=
  Finset.univ.filter fun a => ∀ i, a i ∈ eigenvalueSearch (A i)

/-- Membership in `TauCeti.eigenvalueTupleSearch` is componentwise membership in the individual
searches. -/
@[simp]
theorem mem_eigenvalueTupleSearch {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F} :
    a ∈ eigenvalueTupleSearch A ↔ ∀ i, a i ∈ eigenvalueSearch (A i) := by
  simp [eigenvalueTupleSearch]

/-- Search the finite product of the individual spectra and retain the tuples whose computed
common-eigenspace basis is nonempty. -/
@[expose] def jointEigenvalueSearch (A : Fin m → Matrix (Fin n) (Fin n) F) :
    Finset (Fin m → F) :=
  (eigenvalueTupleSearch A).filter fun a => jointEigenspaceBasis A a ≠ []

/-- **Correctness of the common-eigenvalue search**: it returns exactly the tuples admitting a
nonzero common eigenvector. -/
@[simp]
theorem mem_jointEigenvalueSearch {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F} :
    a ∈ jointEigenvalueSearch A ↔ ∃ v ≠ 0, ∀ i, A i *ᵥ v = a i • v := by
  rw [jointEigenvalueSearch, Finset.mem_filter, nonempty_jointEigenspaceBasis_iff]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨v, hv, heig⟩ := h
    refine ⟨?_, ⟨v, hv, heig⟩⟩
    rw [mem_eigenvalueTupleSearch]
    intro i
    rw [mem_eigenvalueSearch_iff_exists_mulVec]
    exact ⟨v, hv, heig i⟩

/-- Each component of a tuple returned by the common search is found by the corresponding
single-matrix eigenvalue search. -/
theorem apply_mem_eigenvalueSearch_of_mem_jointEigenvalueSearch
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F}
    (ha : a ∈ jointEigenvalueSearch A) (i : Fin m) :
    a i ∈ eigenvalueSearch (A i) := by
  exact mem_eigenvalueTupleSearch.mp (Finset.mem_filter.mp ha).1 i

/-- The basis associated to a returned tuple is nonempty. -/
theorem jointEigenspaceBasis_ne_nil_of_mem_jointEigenvalueSearch
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F}
    (ha : a ∈ jointEigenvalueSearch A) : jointEigenspaceBasis A a ≠ [] :=
  (Finset.mem_filter.mp ha).2

/-! ## Left eigenvectors -/

/-- A computable basis of the simultaneous *left* eigenspace for `a`. These are the eigenrows
needed by the Dixon--Schneider character-table algorithm. -/
@[expose] def leftJointEigenspaceBasis (A : Fin m → Matrix (Fin n) (Fin n) F)
    (a : Fin m → F) : List (Fin n → F) :=
  jointEigenspaceBasis (fun i => (A i)ᵀ) a

omit [Fintype F] in
/-- Every vector returned by `TauCeti.leftJointEigenspaceBasis` is a left eigenvector of every
matrix in the family. -/
theorem vecMul_eq_smul_of_mem_leftJointEigenspaceBasis
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F} {v : Fin n → F}
    (hv : v ∈ leftJointEigenspaceBasis A a) : ∀ i, v ᵥ* A i = a i • v := by
  intro i
  simpa [leftJointEigenspaceBasis, Matrix.mulVec_transpose] using
    mulVec_eq_smul_of_mem_jointEigenspaceBasis (A := fun i => (A i)ᵀ) (a := a) hv i

omit [Fintype F] in
/-- The left common-eigenspace basis is nonempty exactly when the tuple admits a nonzero common
eigenrow. -/
theorem nonempty_leftJointEigenspaceBasis_iff
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) :
    leftJointEigenspaceBasis A a ≠ [] ↔ ∃ v ≠ 0, ∀ i, v ᵥ* A i = a i • v := by
  simpa [leftJointEigenspaceBasis, Matrix.mulVec_transpose] using
    nonempty_jointEigenspaceBasis_iff (fun i => (A i)ᵀ) a

/-- Search for the tuples admitting a nonzero common eigenrow. -/
@[expose] def leftJointEigenvalueSearch (A : Fin m → Matrix (Fin n) (Fin n) F) :
    Finset (Fin m → F) :=
  jointEigenvalueSearch fun i => (A i)ᵀ

/-- **Correctness of the common eigenrow search**: it returns exactly the tuples admitting a
nonzero common left eigenvector. -/
@[simp]
theorem mem_leftJointEigenvalueSearch
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F} :
    a ∈ leftJointEigenvalueSearch A ↔ ∃ v ≠ 0, ∀ i, v ᵥ* A i = a i • v := by
  rw [leftJointEigenvalueSearch, mem_jointEigenvalueSearch]
  simp only [Matrix.mulVec_transpose]

/-- A tuple returned by the left search has a nonempty computed eigenrow basis. -/
theorem leftJointEigenspaceBasis_ne_nil_of_mem_leftJointEigenvalueSearch
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F}
    (ha : a ∈ leftJointEigenvalueSearch A) : leftJointEigenspaceBasis A a ≠ [] := by
  rw [nonempty_leftJointEigenspaceBasis_iff]
  exact mem_leftJointEigenvalueSearch.mp ha

/-- Every component of a tuple returned by the common eigenrow search is an eigenvalue of the
corresponding matrix. -/
theorem apply_mem_eigenvalueSearch_of_mem_leftJointEigenvalueSearch
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F}
    (ha : a ∈ leftJointEigenvalueSearch A) (i : Fin m) :
    a i ∈ eigenvalueSearch (A i) := by
  rw [mem_eigenvalueSearch_iff_exists_vecMul]
  obtain ⟨v, hv, heig⟩ := mem_leftJointEigenvalueSearch.mp ha
  exact ⟨v, hv, heig i⟩

end TauCeti
