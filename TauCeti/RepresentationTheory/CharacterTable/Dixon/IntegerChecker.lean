/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.EigenvectorSearch
public import TauCeti.RepresentationTheory.CharacterTable.Specification

/-!
# An exact checker for integer-valued character tables

The rational stage of the Dixon--Schneider algorithm produces two integer matrices: the normalized
central-character table `Ω` and the ordinary character table `X`. This file gives those numbered
matrices an executable certificate and proves that a certified `X`, after casting to `ℂ` and
reindexing its columns by conjugacy classes, satisfies `TauCeti.IsCharacterTableSpec`.

The certificate checks exactly the division-free identities available to an exact computation:
the central rows are normalized common eigenrows, positive integral degrees divide the group order
and have the right square sum, `dᵢ Ωᵢⱼ = |Cⱼ| Xᵢⱼ`, and the rows of `X` satisfy class-size weighted
orthogonality. No equality of complex numbers is evaluated by the checker.

## Main definitions

* `TauCeti.ClassData.IsIntegerCharacterTableSpec`: the exact numbered certificate.
* `TauCeti.ClassData.integerCharacterTableChecker`: its executable Boolean checker.
* `TauCeti.ClassData.complexTableOfInteger`: the integer ordinary table, cast and reindexed into
  the type expected by `TauCeti.IsCharacterTableSpec`.

## Main result

* `TauCeti.ClassData.IsIntegerCharacterTableSpec.isCharacterTableSpec`: a successful exact
  certificate yields the complex character-table specification and therefore identifies the
  result with the character table up to row permutation.

## References

This is the exact checker bridge required by Layer 6, “The assembled solver”, of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).
See J. D. Dixon, *High speed computation of group characters*, Numer. Math. 10 (1967), 446--450,
and G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
601--606.
-/

public section

namespace TauCeti

open Matrix

namespace ClassData

universe u

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable (d : ClassData G)

/-- **An exact certificate for an integer-valued character table.**

The matrices use the numbering supplied by `d`. The matrix `omega` is the central-character table,
`table` is the ordinary table, and `degree` is their common row indexing of the character degrees.
All fields are decidable finite statements over `ℕ` and `ℤ`, so the certificate can be checked by
kernel evaluation. -/
structure IsIntegerCharacterTableSpec
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    (degree : Fin d.numClasses → ℕ) : Prop where
  /-- Every central-character row is normalized at the identity class. -/
  central_one : ∀ i, omega i (d.index 1) = 1
  /-- Every central-character row is a common left eigenrow of the class-multiplication matrices. -/
  central_eigen : ∀ i, d.IsModularEigenrow (omega i)
  /-- Character degrees are positive. -/
  degree_pos : ∀ i, 0 < degree i
  /-- Character degrees divide the group order. -/
  degree_dvd : ∀ i, degree i ∣ Fintype.card G
  /-- The squares of the character degrees sum to the group order. -/
  sum_degree_sq : ∑ i, degree i ^ 2 = Fintype.card G
  /-- Division-free conversion from the central table to the ordinary table. -/
  degree_mul_central : ∀ i j,
    (degree i : ℤ) * omega i j = (d.classFinset j).card * table i j
  /-- Class-size weighted row orthogonality for the ordinary table. -/
  row_orthogonal : ∀ i j,
    ∑ k, (d.classFinset k).card * table i k * table j k =
      if i = j then (Fintype.card G : ℤ) else 0

/-- The exact integer certificate is decidable, since every condition is a finite statement over
`ℕ` or `ℤ`. -/
instance instDecidableIsIntegerCharacterTableSpec
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    (degree : Fin d.numClasses → ℕ) :
    Decidable (d.IsIntegerCharacterTableSpec omega table degree) :=
  decidable_of_iff
    ((∀ i, omega i (d.index 1) = 1) ∧
      (∀ i a b, ∑ k, (d.structureConstant a b k : ℤ) * omega i k =
        omega i a * omega i b) ∧
      (∀ i, 0 < degree i) ∧
      (∀ i, degree i ∣ Fintype.card G) ∧
      (∑ i, degree i ^ 2 = Fintype.card G) ∧
      (∀ i j, (degree i : ℤ) * omega i j = (d.classFinset j).card * table i j) ∧
      (∀ i j, ∑ k, (d.classFinset k).card * table i k * table j k =
        if i = j then (Fintype.card G : ℤ) else 0))
    ⟨fun h =>
      ⟨h.1, fun i => (d.isModularEigenrow_iff (omega i)).mpr (h.2.1 i), h.2.2.1,
        h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩,
      fun h =>
        ⟨h.central_one, fun i => (d.isModularEigenrow_iff (omega i)).mp (h.central_eigen i),
          h.degree_pos, h.degree_dvd, h.sum_degree_sq, h.degree_mul_central,
          h.row_orthogonal⟩⟩

/-- The executable Boolean checker for an integer central-character table, ordinary table, and
their character degrees. -/
def integerCharacterTableChecker
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    (degree : Fin d.numClasses → ℕ) : Bool :=
  decide (d.IsIntegerCharacterTableSpec omega table degree)

/-- The Boolean exact checker succeeds precisely when the integer certificate holds. -/
@[simp]
theorem integerCharacterTableChecker_eq_true_iff
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    (degree : Fin d.numClasses → ℕ) :
    d.integerCharacterTableChecker omega table degree = true ↔
      d.IsIntegerCharacterTableSpec omega table degree := by
  simp [integerCharacterTableChecker]

/-- Cast a numbered integer table to `ℂ`, reindexing its rows by the cardinality of the conjugacy
classes and its columns by the conjugacy classes themselves. -/
noncomputable def complexTableOfInteger
    (table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ) :
    Matrix (Fin (Nat.card (ConjClasses G))) (ConjClasses G) ℂ :=
  (table.map (Int.cast : ℤ → ℂ)).submatrix
    (finCongr d.numClasses_eq_card_conjClasses).symm d.equivConjClasses.symm

/-- The cast-and-reindexed integer table, evaluated at arbitrary row and column indices. -/
@[simp]
theorem complexTableOfInteger_apply
    (table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    (i : Fin (Nat.card (ConjClasses G))) (C : ConjClasses G) :
    d.complexTableOfInteger table i C =
      (table ((finCongr d.numClasses_eq_card_conjClasses).symm i)
        (d.equivConjClasses.symm C) : ℂ) :=
  (rfl)

/-- The cast-and-reindexed integer table evaluated at a numbered row and numbered class. -/
@[simp]
theorem complexTableOfInteger_apply_classOf
    (table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ) (i j : Fin d.numClasses) :
    d.complexTableOfInteger table (finCongr d.numClasses_eq_card_conjClasses i) (d.classOf j) =
      (table i j : ℂ) := by
  rw [d.complexTableOfInteger_apply]
  have hi : (finCongr d.numClasses_eq_card_conjClasses).symm
      (finCongr d.numClasses_eq_card_conjClasses i) = i :=
    (finCongr d.numClasses_eq_card_conjClasses).symm_apply_apply i
  have hj : d.equivConjClasses.symm (d.classOf j) = j := by
    rw [← d.equivConjClasses_apply j, Equiv.symm_apply_apply]
  rw [hi, hj]

namespace IsIntegerCharacterTableSpec

variable {d : ClassData G}
variable {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ}
variable {degree : Fin d.numClasses → ℕ}
variable (h : d.IsIntegerCharacterTableSpec omega table degree)
include h

/-- The identity column of a certified ordinary table is its supplied degree vector. This follows
from the central-to-ordinary conversion at the identity class. -/
theorem table_index_one (i : Fin d.numClasses) : table i (d.index 1) = degree i := by
  have hcard : (d.classFinset (d.index 1)).card = 1 := by
    rw [d.card_classFinset, d.classOf_index, ConjClasses.card_carrier_mk_one]
  have hconvert := h.degree_mul_central i (d.index 1)
  rw [h.central_one i, mul_one, hcard, Nat.cast_one, one_mul] at hconvert
  exact_mod_cast hconvert.symm

/-- Casting a certified integral central row to `ℂ` preserves the common-eigenrow condition. -/
private theorem central_eigen_complex (i : Fin d.numClasses) :
    d.IsModularEigenrow (fun j => (omega i j : ℂ)) := by
  have hi := h.central_eigen i
  rw [d.isModularEigenrow_iff] at hi ⊢
  intro a b
  exact_mod_cast hi a b

/-- The normalized row of the cast ordinary table is the corresponding cast central-character
row, with both transported from the numbering of `d` to conjugacy classes. -/
theorem centralCharacterRow_complexTableOfInteger
    (i : Fin (Nat.card (ConjClasses G))) :
    centralCharacterRow (d.complexTableOfInteger table) i =
      d.reindexModularRow
        (fun j => (omega ((finCongr d.numClasses_eq_card_conjClasses).symm i) j : ℂ)) := by
  let i' := (finCongr d.numClasses_eq_card_conjClasses).symm i
  funext C
  obtain ⟨j, rfl⟩ := d.equivConjClasses.surjective C
  rw [d.equivConjClasses_apply]
  have hdeg : (degree i' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (h.degree_pos i').ne'
  have hconvert := h.degree_mul_central i' j
  have htable (k : Fin d.numClasses) :
      d.complexTableOfInteger table i (d.classOf k) = (table i' k : ℂ) := by
    rw [← (finCongr d.numClasses_eq_card_conjClasses).apply_symm_apply i,
      d.complexTableOfInteger_apply_classOf]
  rw [centralCharacterRow_apply, htable j, ← d.classOf_index (1 : G),
    htable (d.index 1), h.table_index_one, d.reindexModularRow_classOf,
    ← d.card_classFinset]
  apply (div_eq_iff hdeg).2
  have hconvert' :
      ((d.classFinset j).card : ℂ) * table i' j =
        (degree i' : ℂ) * omega i' j := by
    exact_mod_cast hconvert.symm
  simpa only [mul_comm] using hconvert'

/-- **A certified integer table satisfies the complex character-table specification.** This is the
soundness theorem for the exact checker: the only passage to `ℂ` occurs after every condition has
been checked over decidable exact arithmetic. -/
theorem isCharacterTableSpec :
    IsCharacterTableSpec G (d.complexTableOfInteger table) where
  exists_degree i := by
    let i' := (finCongr d.numClasses_eq_card_conjClasses).symm i
    refine ⟨degree i', h.degree_pos i', ?_, ?_⟩
    · rw [← d.classOf_index (1 : G), ← d.equivConjClasses_apply (d.index 1)]
      simpa [complexTableOfInteger, i'] using
        congrArg ((fun z : ℤ => (z : ℂ))) (h.table_index_one i')
    · simpa only [Nat.card_eq_fintype_card] using h.degree_dvd i'
  sum_degree_sq := by
    rw [@Nat.card_eq_fintype_card G]
    rw [← h.sum_degree_sq]
    rw [← (finCongr d.numClasses_eq_card_conjClasses).sum_comp]
    simp only [← d.classOf_index (1 : G), d.complexTableOfInteger_apply_classOf,
      h.table_index_one]
    exact_mod_cast rfl
  row_orthonormal i j := by
    let i' := (finCongr d.numClasses_eq_card_conjClasses).symm i
    let j' := (finCongr d.numClasses_eq_card_conjClasses).symm j
    have hsum := h.row_orthogonal i' j'
    have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
    have htable_i (k : Fin d.numClasses) :
        d.complexTableOfInteger table i (d.classOf k) = (table i' k : ℂ) := by
      rw [← (finCongr d.numClasses_eq_card_conjClasses).apply_symm_apply i,
        d.complexTableOfInteger_apply_classOf]
    have htable_j (k : Fin d.numClasses) :
        d.complexTableOfInteger table j (d.classOf k) = (table j' k : ℂ) := by
      rw [← (finCongr d.numClasses_eq_card_conjClasses).apply_symm_apply j,
        d.complexTableOfInteger_apply_classOf]
    simp only [Nat.card_eq_fintype_card]
    rw [← d.equivConjClasses.sum_comp]
    simp only [d.equivConjClasses_apply, htable_i, htable_j, map_intCast]
    have hsum' :
        (∑ k, (Fintype.card (d.classOf k).carrier : ℂ) * (table i' k : ℂ) *
            (table j' k : ℂ)) =
          if i' = j' then (Fintype.card G : ℂ) else 0 := by
      have hcard (k : Fin d.numClasses) :
          Fintype.card (d.classOf k).carrier = (d.classFinset k).card := by
        rw [← Nat.card_eq_fintype_card, ← d.card_classFinset]
      simp only [hcard]
      exact_mod_cast hsum
    rw [hsum']
    have hij : i' = j' ↔ i = j :=
      (finCongr d.numClasses_eq_card_conjClasses).symm.injective.eq_iff
    rw [if_congr hij rfl rfl]
    split_ifs <;> simp [hG]
  row_eigen i := by
    rw [h.centralCharacterRow_complexTableOfInteger i]
    exact (d.isModularEigenrow_iff_isClassEigenrow _).mp
      (h.central_eigen_complex ((finCongr d.numClasses_eq_card_conjClasses).symm i))

end IsIntegerCharacterTableSpec

end ClassData

end TauCeti
