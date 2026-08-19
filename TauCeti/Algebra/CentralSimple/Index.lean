/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.CentralSimple.MaximalSubfield
public import Mathlib.Algebra.Central.Matrix
public import Mathlib.RingTheory.SimpleRing.Matrix
import Mathlib.Data.Matrix.Composition
import TauCeti.Algebra.CentralSimple.Wedderburn
import TauCeti.RingTheory.Semisimple.MatrixDivisionRing

/-!
# The index of a central simple algebra

Every finite-dimensional central simple algebra `A` over a field `K` has a Wedderburn
presentation

`A ≃ₐ[K] Matrix (Fin n) (Fin n) D`

for a finite-dimensional central division algebra `D`. The division algebra is unique up to ring
isomorphism, and the matrix size `n` is unique. This file defines `TauCeti.Algebra.index K A` to be
the degree of one such `D`, then proves that every presentation computes the same number. Thus the
definition exposes no choice to its users.

The two numerical invariants of a presentation satisfy

`deg K A = n * index K A`.

The index is `1` exactly when `A` is split. Combining the construction with the maximal-subfield
theorem gives the arithmetic meaning required by the semisimple-algebras roadmap: every central
simple algebra has a finite splitting field whose degree over `K` is exactly its index.

## Main results

* `TauCeti.Algebra.index_eq_deg_of_algEquiv_matrix`: the index is the degree of the division
  algebra in any Wedderburn presentation.
* `TauCeti.Algebra.deg_eq_mul_index_of_algEquiv_matrix`: the degree is the product of the matrix
  size and the index.
* `TauCeti.Algebra.isSplittingField_self_iff_index_eq_one`: a central simple algebra is split over
  its base field exactly when its index is one.
* `TauCeti.Algebra.exists_isSplittingField_finrank_eq_index`: every central simple algebra has a
  finite splitting field of degree its index.

## References

This implements the index portion of Layer 6, “Splitting fields, maximal subfields, and the
index”, of the
[semisimple algebras roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md).
See P. Gille and T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.4, and
R. S. Pierce, *Associative Algebras*, Chapter 13.
-/

public section

namespace TauCeti

open Module

universe u

namespace Algebra

attribute [local instance] Algebra.IsCentral.matrix

private structure WedderburnData (K : Type*) [Field K] (A : Type u) [Ring A] [Algebra K A]
    [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] where
  matrixSize : ℕ
  matrixSize_neZero : NeZero matrixSize
  divisionAlgebra : Type u
  divisionRing : DivisionRing divisionAlgebra
  algebra : Algebra K divisionAlgebra
  isCentral : Algebra.IsCentral K divisionAlgebra
  finiteDimensional : FiniteDimensional K divisionAlgebra
  equiv : A ≃ₐ[K] Matrix (Fin matrixSize) (Fin matrixSize) divisionAlgebra

private theorem nonempty_wedderburnData (K : Type*) [Field K] (A : Type u) [Ring A]
    [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] :
    Nonempty (WedderburnData K A) := by
  obtain ⟨n, hn, D, hD, hDalg, hDcentral, hDfinite, -, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_centralDivisionRing K A
  exact ⟨⟨n, hn, D, hD, hDalg, hDcentral, hDfinite, e⟩⟩

private noncomputable def wedderburnData (K : Type*) [Field K] (A : Type u) [Ring A]
    [Algebra K A] [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] :
    WedderburnData K A :=
  Classical.choice (nonempty_wedderburnData K A)

variable (K : Type*) [Field K] (A : Type u) [Ring A] [Algebra K A]
  [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]

/-- The **index** of a finite-dimensional central simple algebra: the degree of the central
division algebra in a Wedderburn presentation.

Although the definition chooses a presentation, `TauCeti.Algebra.index_eq_deg_of_algEquiv_matrix`
shows that every presentation gives the same value. -/
noncomputable def index : ℕ :=
  let W := wedderburnData K A
  let _ := W.divisionRing
  let _ := W.algebra
  deg K W.divisionAlgebra

variable {K A}

/-- **A Wedderburn presentation computes the index.** If `A` is `n × n` matrices over a
finite-dimensional central division algebra `D`, then the index of `A` is `deg K D`.

This is the characteristic property of `TauCeti.Algebra.index`; later results use it instead of
unfolding the choice made in the definition. -/
theorem index_eq_deg_of_algEquiv_matrix {n : ℕ} [NeZero n] {D : Type*} [DivisionRing D]
    [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D]
    (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) D) : index K A = deg K D := by
  let W := wedderburnData K A
  let _ := W.divisionRing
  let _ := W.algebra
  let _ := W.isCentral
  let _ := W.finiteDimensional
  let _ := W.matrixSize_neZero
  have hsize : W.matrixSize = n :=
    (wedderburn_data_unique W.equiv.toRingEquiv e.toRingEquiv).1
  have hW := deg_eq_mul_deg_of_algEquiv_matrix W.equiv
  have hD := deg_eq_mul_deg_of_algEquiv_matrix e
  rw [hsize] at hW
  change deg K W.divisionAlgebra = deg K D
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne n)) (hW.symm.trans hD)

/-- **The degree read from a Wedderburn presentation.** If `A ≃ Mₙ(D)`, then
`deg K A = n * index K A`. -/
theorem deg_eq_mul_index_of_algEquiv_matrix {n : ℕ} [NeZero n] {D : Type*} [DivisionRing D]
    [Algebra K D] [Algebra.IsCentral K D] [FiniteDimensional K D]
    (e : A ≃ₐ[K] Matrix (Fin n) (Fin n) D) : deg K A = n * index K A := by
  rw [deg_eq_mul_deg_of_algEquiv_matrix e, index_eq_deg_of_algEquiv_matrix e]

/-- The index is invariant under isomorphism of central simple `K`-algebras. -/
theorem index_eq_of_algEquiv {B : Type u} [Ring B] [Algebra K B] [Algebra.IsCentral K B]
    [IsSimpleRing B] [FiniteDimensional K B] (e : A ≃ₐ[K] B) : index K A = index K B := by
  let W := wedderburnData K A
  let _ := W.divisionRing
  let _ := W.algebra
  let _ := W.isCentral
  let _ := W.finiteDimensional
  let _ := W.matrixSize_neZero
  exact (index_eq_deg_of_algEquiv_matrix W.equiv).trans
    (index_eq_deg_of_algEquiv_matrix (e.symm.trans W.equiv)).symm

/-- Passing to a positive-size full matrix algebra does not change the index. -/
@[simp]
theorem index_matrix (n : ℕ) [NeZero n] :
    index K (Matrix (Fin n) (Fin n) A) = index K A := by
  let W := wedderburnData K A
  let _ := W.divisionRing
  let _ := W.algebra
  let _ := W.isCentral
  let _ := W.finiteDimensional
  let _ := W.matrixSize_neZero
  let _ : NeZero (n * W.matrixSize) := inferInstance
  let e : Matrix (Fin n) (Fin n) A ≃ₐ[K]
      Matrix (Fin (n * W.matrixSize)) (Fin (n * W.matrixSize)) W.divisionAlgebra :=
    (W.equiv.mapMatrix (m := Fin n)).trans <|
      (Matrix.compAlgEquiv (Fin n) (Fin W.matrixSize) W.divisionAlgebra K).trans <|
        Matrix.reindexAlgEquiv K W.divisionAlgebra finProdFinEquiv
  exact (index_eq_deg_of_algEquiv_matrix e).trans
    (index_eq_deg_of_algEquiv_matrix W.equiv).symm

/-- The index of a central division algebra is its degree. -/
@[simp]
theorem index_eq_deg_of_divisionRing (D : Type u) [DivisionRing D] [Algebra K D]
    [Algebra.IsCentral K D] [FiniteDimensional K D] : index K D = deg K D :=
  (index_matrix (K := K) (A := D) 1).symm.trans
    (index_eq_deg_of_algEquiv_matrix (AlgEquiv.refl :
      Matrix (Fin 1) (Fin 1) D ≃ₐ[K] Matrix (Fin 1) (Fin 1) D))

variable (K A)

/-- The index of a central simple algebra is positive. -/
theorem index_pos : 0 < index K A := by
  let W := wedderburnData K A
  let _ := W.divisionRing
  let _ := W.algebra
  let _ := W.isCentral
  let _ := W.finiteDimensional
  let _ := W.matrixSize_neZero
  rw [index_eq_deg_of_algEquiv_matrix W.equiv]
  exact deg_pos K W.divisionAlgebra

/-- The index of a central simple algebra is nonzero. -/
@[simp]
theorem index_ne_zero : index K A ≠ 0 :=
  (index_pos K A).ne'

/-- The index divides the degree of a central simple algebra. -/
theorem index_dvd_deg : index K A ∣ deg K A := by
  let W := wedderburnData K A
  let _ := W.divisionRing
  let _ := W.algebra
  let _ := W.isCentral
  let _ := W.finiteDimensional
  let _ := W.matrixSize_neZero
  refine ⟨W.matrixSize, ?_⟩
  rw [deg_eq_mul_index_of_algEquiv_matrix W.equiv, mul_comm]

/-- The index is at most the degree of a central simple algebra. -/
theorem index_le_deg : index K A ≤ deg K A :=
  Nat.le_of_dvd (deg_pos K A) (index_dvd_deg K A)

/-- **A central simple algebra is split over its base field exactly when its index is one.** -/
theorem isSplittingField_self_iff_index_eq_one :
    IsSplittingField K A K ↔ index K A = 1 := by
  constructor
  · intro h
    obtain ⟨n, ⟨e⟩⟩ := (isSplittingField_self_iff K A).1 h
    have hn : n ≠ 0 := by
      intro hn
      have hrank := e.toLinearEquiv.finrank_eq
      rw [Module.finrank_matrix, Fintype.card_fin, hn, zero_mul] at hrank
      simp only [zero_mul] at hrank
      exact Module.finrank_pos.ne' hrank
    let _ : NeZero n := ⟨hn⟩
    rw [index_eq_deg_of_algEquiv_matrix e, deg_self]
  · intro hindex
    let W := wedderburnData K A
    let _ := W.divisionRing
    let _ := W.algebra
    let _ := W.isCentral
    let _ := W.finiteDimensional
    let _ := W.matrixSize_neZero
    have hdeg : deg K W.divisionAlgebra = 1 :=
      (index_eq_deg_of_algEquiv_matrix W.equiv).symm.trans hindex
    have hfinrank : finrank K W.divisionAlgebra = 1 := by
      rw [← deg_sq K W.divisionAlgebra, hdeg, one_pow]
    let dToK : W.divisionAlgebra ≃ₐ[K] K :=
      (AlgEquiv.ofBijective (_root_.Algebra.ofId K W.divisionAlgebra)
        (_root_.Algebra.finrank_eq_one_iff_bijective_algebraMap.1 hfinrank)).symm
    exact (isSplittingField_self_iff K A).2
      ⟨W.matrixSize, ⟨W.equiv.trans (AlgEquiv.mapMatrix dToK)⟩⟩

/-- Over an algebraically closed field every central simple algebra has index one. -/
theorem index_eq_one_of_isAlgClosed [IsAlgClosed K] : index K A = 1 :=
  (isSplittingField_self_iff_index_eq_one K A).1
    (isSplittingField_of_isAlgClosed K A K)

/-- Over a finite field every central simple algebra has index one. -/
theorem index_eq_one_of_finite [Finite K] : index K A = 1 :=
  (isSplittingField_self_iff_index_eq_one K A).1
    (isSplittingField_self_of_finite K A)

/-- **Every central simple algebra has a finite splitting field of degree its index.**

Choose `A ≃ Mₙ(D)`, take a maximal subfield `L` of `D`, and use that `L` splits `D`. It then
splits `Mₙ(D)`, hence `A`, while `finrank K L = deg K D = index K A`. -/
theorem exists_isSplittingField_finrank_eq_index :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
      FiniteDimensional K L ∧ finrank K L = index K A ∧ IsSplittingField K A L := by
  let W := wedderburnData K A
  let _ := W.divisionRing
  let _ := W.algebra
  let _ := W.isCentral
  let _ := W.finiteDimensional
  let _ := W.matrixSize_neZero
  obtain ⟨L, hLfield, hLalg, -, hLfinite, hLdegree, hsplit⟩ :=
    exists_isSplittingField_finrank_eq_deg K W.divisionAlgebra
  let _ : Field L := hLfield
  let _ : Algebra K L := hLalg
  refine ⟨L, inferInstance, inferInstance, hLfinite, ?_, ?_⟩
  · rw [hLdegree, index_eq_deg_of_algEquiv_matrix W.equiv]
  · exact IsSplittingField.of_algEquiv K _ L W.equiv.symm
      (IsSplittingField.matrix K W.divisionAlgebra L hsplit W.matrixSize)

end Algebra

end TauCeti
