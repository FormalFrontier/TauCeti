/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
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
* `TauCeti.jointEigenvalueSearch`: the tuples with nonzero common eigenspace.

Applying these definitions to the transposed family gives the common eigenrows used by
Dixon--Schneider; the final section records their `ᵥ*` characterizations.

## Main results

* `TauCeti.jointEigenspaceMatrix_mulVec_eq_zero_iff`: the stacked system expresses exactly the
  common eigenvector equations.
* `TauCeti.mem_span_jointEigenspaceBasis`: that basis spans the common eigenspace.
* `TauCeti.length_jointEigenspaceBasis`: its length is the nullity of the stacked system, which
  is the executable test for a one-dimensional common eigenspace.
* `TauCeti.jointEigenspaceBasis_ne_nil_iff`: its computed basis is nonempty exactly when a
  nonzero common eigenvector exists.
* `TauCeti.mem_jointEigenvalueSearch`: correctness of the executable tuple search.
* `TauCeti.mem_jointEigenvalueSearch_transpose`: the corresponding common-eigenrow
  characterization.

## References

Layer 6 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md)
requires an eigenvector search over `ZMod p` which combines `eigenvalueSearch` with
`kernelBasis`. This is the common-eigenspace search at the core of that refinement.

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450: the modular class-matrix method, in which the central characters are recovered as
  the common eigenrows of the class matrices. This is the source of the `ᵥ*` orientation
  recorded in the final section.
* G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601--606: the successive splitting of a common eigenspace by further class matrices until it
  is one-dimensional. This is why the full kernel basis, and its length, are exposed here
  rather than only the decision whether a tuple occurs.
-/

public section

namespace TauCeti

open Matrix

universe u

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {m n : ℕ}

/-- The rectangular matrix formed by stacking the systems
`(Matrix.diagonal (fun _ => a i) - A i) v = 0`, one block of `n` rows for each `i : Fin m`.

The product row index is flattened to `Fin (m * n)` because `TauCeti.kernelBasis` operates on
matrices with `Fin` row and column types. -/
@[expose] def jointEigenspaceMatrix {R : Type u} [NonUnitalNonAssocRing R]
    (A : Fin m → Matrix (Fin n) (Fin n) R)
    (a : Fin m → R) : Matrix (Fin (m * n)) (Fin n) R := fun k j =>
  let ij := finProdFinEquiv.symm k
  (Matrix.diagonal (n := Fin n) (fun _ => a ij.1) - A ij.1) ij.2 j

/-- An entry in the `i`-th block of `TauCeti.jointEigenspaceMatrix`. -/
@[simp]
theorem jointEigenspaceMatrix_apply {R : Type u} [NonUnitalNonAssocRing R]
    (A : Fin m → Matrix (Fin n) (Fin n) R)
    (a : Fin m → R) (i : Fin m) (j k : Fin n) :
    jointEigenspaceMatrix A a (finProdFinEquiv (i, j)) k =
      (Matrix.diagonal (n := Fin n) (fun _ => a i) - A i) j k := by
  simp [jointEigenspaceMatrix]

/-- The stacked matrix annihilates `v` exactly when `v` is an eigenvector (possibly zero) of
every `A i`, with eigenvalue `a i`. -/
theorem jointEigenspaceMatrix_mulVec_eq_zero_iff {R : Type u} [NonUnitalNonAssocRing R]
    (A : Fin m → Matrix (Fin n) (Fin n) R) (a : Fin m → R) (v : Fin n → R) :
    jointEigenspaceMatrix A a *ᵥ v = 0 ↔ ∀ i, A i *ᵥ v = a i • v := by
  constructor
  · intro h i
    have hi : (Matrix.diagonal (n := Fin n) (fun _ => a i) - A i) *ᵥ v = 0 := by
      funext j
      simpa only [Matrix.mulVec, jointEigenspaceMatrix_apply, Pi.zero_apply] using
        congrFun h (finProdFinEquiv (i, j))
    rw [scalar_sub_mulVec_eq_zero_iff] at hi
    exact hi
  · intro h
    funext k
    rcases hidx : finProdFinEquiv.symm k with ⟨i, j⟩
    have hi : (Matrix.diagonal (n := Fin n) (fun _ => a i) - A i) *ᵥ v = 0 := by
      rw [scalar_sub_mulVec_eq_zero_iff]
      exact h i
    rw [← finProdFinEquiv.apply_symm_apply k]
    rw [hidx]
    simpa only [Matrix.mulVec, jointEigenspaceMatrix_apply, Pi.zero_apply] using
      congrFun hi j

/-- A computable basis of the simultaneous eigenspace for the eigenvalue tuple `a`.

This is the kernel basis of the stacked system, so the `TauCeti.kernelBasis` API applies to it
verbatim: `TauCeti.linearIndepOn_kernelBasis (jointEigenspaceMatrix A a)` and
`TauCeti.nodup_kernelBasis (jointEigenspaceMatrix A a)` are its linear independence and `Nodup`,
with no unfolding needed. -/
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
/-- The computed basis spans the common eigenspace: a vector lies in its span exactly when it
satisfies every eigenvector equation. -/
theorem mem_span_jointEigenspaceBasis
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) (v : Fin n → F) :
    v ∈ Submodule.span F {w : Fin n → F | w ∈ jointEigenspaceBasis A a} ↔
      ∀ i, A i *ᵥ v = a i • v := by
  rw [jointEigenspaceBasis, span_kernelBasis, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    jointEigenspaceMatrix_mulVec_eq_zero_iff]

omit [Fintype F] in
/-- The number of computed basis vectors is the nullity of the stacked system. Comparing this
length with `1` is the executable test that Dixon--Schneider refinement has reached a
one-dimensional common eigenspace. -/
theorem length_jointEigenspaceBasis
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) :
    (jointEigenspaceBasis A a).length = n - (jointEigenspaceMatrix A a).rank :=
  length_kernelBasis _

omit [Fintype F] in
/-- The common-eigenspace basis is nonempty exactly when the eigenvalue tuple has a nonzero
common eigenvector. -/
theorem jointEigenspaceBasis_ne_nil_iff
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) :
    jointEigenspaceBasis A a ≠ [] ↔ ∃ v ≠ 0, ∀ i, A i *ᵥ v = a i • v := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨v, (linearIndepOn_kernelBasis (jointEigenspaceMatrix A a)).ne_zero hv,
      mulVec_eq_smul_of_mem_jointEigenspaceBasis hv⟩
  · rintro ⟨v, hv, heig⟩ hnil
    have hmem := (mem_span_jointEigenspaceBasis A a v).mpr heig
    rw [hnil] at hmem
    simp only [List.not_mem_nil, Set.ofPred_false, Submodule.span_empty,
      Submodule.mem_bot] at hmem
    exact hv hmem

/-- Search the finite product of the individual spectra and retain the tuples whose computed
common-eigenspace basis is nonempty. -/
@[expose] def jointEigenvalueSearch (A : Fin m → Matrix (Fin n) (Fin n) F) :
    Finset (Fin m → F) :=
  (Fintype.piFinset fun i => eigenvalueSearch (A i)).filter fun a =>
    jointEigenspaceBasis A a ≠ []

/-- **Correctness of the common-eigenvalue search**: it returns exactly the tuples admitting a
nonzero common eigenvector. -/
@[simp]
theorem mem_jointEigenvalueSearch {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F} :
    a ∈ jointEigenvalueSearch A ↔ ∃ v ≠ 0, ∀ i, A i *ᵥ v = a i • v := by
  rw [jointEigenvalueSearch, Finset.mem_filter, jointEigenspaceBasis_ne_nil_iff]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨v, hv, heig⟩ := h
    refine ⟨?_, ⟨v, hv, heig⟩⟩
    rw [Fintype.mem_piFinset]
    intro i
    rw [mem_eigenvalueSearch_iff_exists_mulVec]
    exact ⟨v, hv, heig i⟩

/-- Each component of a tuple returned by the common search is found by the corresponding
single-matrix eigenvalue search. -/
theorem apply_mem_eigenvalueSearch_of_mem_jointEigenvalueSearch
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F}
    (ha : a ∈ jointEigenvalueSearch A) (i : Fin m) :
    a i ∈ eigenvalueSearch (A i) := by
  exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp ha).1 i

/-- The basis associated to a returned tuple is nonempty. -/
theorem jointEigenspaceBasis_ne_nil_of_mem_jointEigenvalueSearch
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F}
    (ha : a ∈ jointEigenvalueSearch A) : jointEigenspaceBasis A a ≠ [] :=
  (Finset.mem_filter.mp ha).2

/-! ## Left-eigenvector characterizations -/

omit [Fintype F] in
/-- Every vector returned for the transposed family is a left eigenvector of every original
matrix. -/
theorem vecMul_eq_smul_of_mem_jointEigenspaceBasis_transpose
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F} {v : Fin n → F}
    (hv : v ∈ jointEigenspaceBasis (fun i => (A i)ᵀ) a) : ∀ i, v ᵥ* A i = a i • v := by
  intro i
  simpa [Matrix.mulVec_transpose] using
    mulVec_eq_smul_of_mem_jointEigenspaceBasis (A := fun i => (A i)ᵀ) (a := a) hv i

omit [Fintype F] in
/-- The common-eigenspace basis for the transposed family is nonempty exactly when the tuple
admits a nonzero common eigenrow. -/
theorem jointEigenspaceBasis_transpose_ne_nil_iff
    (A : Fin m → Matrix (Fin n) (Fin n) F) (a : Fin m → F) :
    jointEigenspaceBasis (fun i => (A i)ᵀ) a ≠ [] ↔
      ∃ v ≠ 0, ∀ i, v ᵥ* A i = a i • v := by
  simpa [Matrix.mulVec_transpose] using
    jointEigenspaceBasis_ne_nil_iff (fun i => (A i)ᵀ) a

/-- **Correctness of the common eigenrow search**: searching the transposed family returns exactly
the tuples admitting a nonzero common left eigenvector. -/
theorem mem_jointEigenvalueSearch_transpose
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F} :
    a ∈ jointEigenvalueSearch (fun i => (A i)ᵀ) ↔
      ∃ v ≠ 0, ∀ i, v ᵥ* A i = a i • v := by
  simp [Matrix.mulVec_transpose]

/-- Every component of a tuple returned by searching the transposed family is an eigenvalue of
the corresponding original matrix. -/
theorem apply_mem_eigenvalueSearch_of_mem_jointEigenvalueSearch_transpose
    {A : Fin m → Matrix (Fin n) (Fin n) F} {a : Fin m → F}
    (ha : a ∈ jointEigenvalueSearch (fun i => (A i)ᵀ)) (i : Fin m) :
    a i ∈ eigenvalueSearch (A i) := by
  rw [← eigenvalueSearch_transpose]
  exact apply_mem_eigenvalueSearch_of_mem_jointEigenvalueSearch ha i

end TauCeti
