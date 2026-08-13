/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Diagonal

/-!
# The diagonal torus in the standard representation

The **diagonal torus** `TauCeti.diagonalTorus k n` of `GL n k`, the subgroup of invertible
diagonal matrices, is built in
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal`, where its three descriptions — as the
range of `TauCeti.diagGL`, by diagonality of the matrix, and as its own centralizer — are proved.
What is recorded here is its action on the coordinate lines `k ∙ eᵢ` of the standard
representation: every torus element scales `eᵢ` by its `i`-th diagonal entry
(`TauCeti.stdRep_apply_basisFun_of_mem_diagonalTorus`), so each line is stable
(`TauCeti.map_stdRep_span_basisFun`).

Over a general `k` these lines are not yet the *weight spaces* of the torus: that identification
needs the coordinate characters to be pairwise distinct, and it fails outright when the torus is
trivial, as it is over `𝔽₂` (`TauCeti.diagonalTorus_eq_bot`).

## Main statements

* `TauCeti.map_stdRep_span_basisFun`: the coordinate lines of the standard representation are
  stable under the diagonal torus.

## References

* [Classical groups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/ClassicalGroups/README.md),
  Layer 3.
* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15.
-/

public section

open Matrix

universe u

namespace TauCeti

variable {k : Type u} [CommRing k] {n : ℕ}

/-- An element of the diagonal torus scales the standard basis vector `eᵢ` by its `(i, i)` matrix
entry, the `i`-th coordinate character of the torus read off `diagGL` through
`TauCeti.diagonalTorusEquiv`.  This is an eigen-relation rather than an eigenvector statement:
over the zero ring `eᵢ` itself vanishes. -/
theorem stdRep_apply_basisFun_of_mem_diagonalTorus {g : GL (Fin n) k}
    (hg : g ∈ diagonalTorus k n) (i : Fin n) :
    stdRep k n g (Pi.basisFun k (Fin n) i) =
      (g : Matrix (Fin n) (Fin n) k) i i • Pi.basisFun k (Fin n) i := by
  obtain ⟨t, rfl⟩ := mem_diagonalTorus_iff_exists_diagGL.mp hg
  rw [stdRep_diagGL_apply_basisFun, diagGL_coe, Matrix.diagonal_apply_eq]

/-- Each coordinate line of the standard representation is stable under the diagonal torus, a
torus element acting on it by the invertible scalar given by its `i`-th diagonal entry. -/
theorem map_stdRep_span_basisFun {g : GL (Fin n) k} (hg : g ∈ diagonalTorus k n) (i : Fin n) :
    Submodule.map (stdRep k n g) (Submodule.span k {Pi.basisFun k (Fin n) i}) =
      Submodule.span k {Pi.basisFun k (Fin n) i} := by
  rw [Submodule.map_span, Set.image_singleton, stdRep_apply_basisFun_of_mem_diagonalTorus hg i]
  exact Submodule.span_singleton_smul_eq (isUnit_apply_of_isDiag
    (isDiag_of_mem_diagonalTorus hg) i) _

end TauCeti
