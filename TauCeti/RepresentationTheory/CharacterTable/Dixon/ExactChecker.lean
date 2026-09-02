/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.EigenvectorSearch
public import TauCeti.RepresentationTheory.CharacterTable.Specification

/-!
# Exact certificates for character tables

This file gives a coefficient-independent certificate for the exact stage of the
Burnside--Dixon--Schneider character-table algorithm.  A numbered central-character table and
ordinary table over a commutative ring with a chosen conjugation are certified by division-free
identities: normalized common eigenrows, positive degrees of the right total size,
central-to-ordinary conversion, and Hermitian row orthogonality.

The certificate is executable whenever equality in the coefficient ring is decidable.  Its
soundness theorem is stated for a ring homomorphism to `ℂ` that preserves `star`; consequently the
same proof serves both the integer-valued stage and the exact cyclotomic stage.

## Main definitions

* `TauCeti.ClassData.IsExactCharacterTableSpec`: an exact numbered certificate over a
  commutative ring with a chosen conjugation operation.
* `TauCeti.ClassData.exactCharacterTableChecker`: its executable Boolean checker.

## Main result

* `TauCeti.ClassData.IsExactCharacterTableSpec.isCharacterTableSpec`: a certified exact table
  maps to the complex character-table specification under any star-preserving ring homomorphism.

This is the checker bridge required by Layer 6, “The assembled solver”, of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).

The certificate follows J. D. Dixon, *High speed computation of group characters*, Numer. Math.
10 (1967), 446--450, and G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic
Comput. 9 (1990), 601--606.
-/

public section

namespace TauCeti

open Matrix

namespace ClassData

universe u v

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable (d : ClassData G)
variable {R : Type v} [CommRing R]

/-- **An exact certificate for a numbered character table over a commutative ring.**

`omega` is the central-character table, `table` is the ordinary table, and `degree` gives their
common row indexing of the character degrees.  The `conj` argument is the exact operation that
maps to complex conjugation: it specializes to the identity over `ℤ` and to exact cyclotomic
conjugation over a cyclotomic coefficient ring. -/
structure IsExactCharacterTableSpec
    (conj : R → R)
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) R)
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
    (degree i : R) * omega i j = (d.classFinset j).card * table i j
  /-- Class-size weighted Hermitian row orthogonality for the ordinary table. -/
  row_orthogonal : ∀ i j,
    ∑ k, (d.classFinset k).card * table i k * conj (table j k) =
      if i = j then (Fintype.card G : R) else 0

/-- The exact certificate is decidable when equality in the coefficient ring is decidable. -/
instance instDecidableIsExactCharacterTableSpec [DecidableEq R]
    (conj : R → R)
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) R)
    (degree : Fin d.numClasses → ℕ) :
    Decidable (d.IsExactCharacterTableSpec conj omega table degree) :=
  decidable_of_iff
    ((∀ i, omega i (d.index 1) = 1) ∧
      (∀ i a b, ∑ k, (d.structureConstant a b k : R) * omega i k =
        omega i a * omega i b) ∧
      (∀ i, 0 < degree i) ∧
      (∀ i, degree i ∣ Fintype.card G) ∧
      (∑ i, degree i ^ 2 = Fintype.card G) ∧
      (∀ i j, (degree i : R) * omega i j = (d.classFinset j).card * table i j) ∧
      (∀ i j, ∑ k, (d.classFinset k).card * table i k * conj (table j k) =
        if i = j then (Fintype.card G : R) else 0))
    ⟨fun h =>
      ⟨h.1, fun i => (d.isModularEigenrow_iff (omega i)).mpr (h.2.1 i), h.2.2.1,
        h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩,
      fun h =>
        ⟨h.central_one, fun i => (d.isModularEigenrow_iff (omega i)).mp (h.central_eigen i),
          h.degree_pos, h.degree_dvd, h.sum_degree_sq, h.degree_mul_central,
          h.row_orthogonal⟩⟩

/-- The executable Boolean checker for an exact central-character table, ordinary table, and
their character degrees. -/
def exactCharacterTableChecker [DecidableEq R]
    (conj : R → R)
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) R)
    (degree : Fin d.numClasses → ℕ) : Bool :=
  decide (d.IsExactCharacterTableSpec conj omega table degree)

/-- The Boolean exact checker succeeds precisely when the exact certificate holds. -/
@[simp]
theorem exactCharacterTableChecker_eq_true_iff [DecidableEq R]
    (conj : R → R)
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) R)
    (degree : Fin d.numClasses → ℕ) :
    d.exactCharacterTableChecker conj omega table degree = true ↔
      d.IsExactCharacterTableSpec conj omega table degree := by
  simp [exactCharacterTableChecker]

namespace IsExactCharacterTableSpec

variable {d : ClassData G}
variable {conj : R → R}
variable {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) R}
variable {degree : Fin d.numClasses → ℕ}
variable (h : d.IsExactCharacterTableSpec conj omega table degree)
include h

/-- The identity column of a certified ordinary table is its supplied degree vector. -/
theorem table_index_one (i : Fin d.numClasses) : table i (d.index 1) = (degree i : R) := by
  have hcard : (d.classFinset (d.index 1)).card = 1 := by
    rw [d.card_classFinset, d.classOf_index, ConjClasses.card_carrier_mk_one]
  have hconvert := h.degree_mul_central i (d.index 1)
  simpa only [h.central_one, mul_one, hcard, Nat.cast_one, one_mul] using hconvert.symm

/-- Mapping a certified central row preserves the common-eigenrow condition. -/
private theorem central_eigen_map (f : R →+* ℂ) (i : Fin d.numClasses) :
    d.IsModularEigenrow (fun j => f (omega i j)) :=
  (h.central_eigen i).map f

/-- The normalized row of the mapped ordinary table is the corresponding mapped central row,
with both transported from the numbering of `d` to conjugacy classes. -/
theorem centralCharacterRow_reindexTableOfMap (f : R →+* ℂ)
    (i : Fin (Nat.card (ConjClasses G))) :
    centralCharacterRow (d.reindexTableOfMap f table) i =
      d.reindexModularRow
        (fun j => f (omega ((finCongr d.numClasses_eq_card_conjClasses).symm i) j)) := by
  let i' := (finCongr d.numClasses_eq_card_conjClasses).symm i
  funext C
  obtain ⟨j, rfl⟩ := d.equivConjClasses.surjective C
  rw [d.equivConjClasses_apply]
  have hdeg : (degree i' : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (h.degree_pos i').ne'
  have hconvert := congrArg f (h.degree_mul_central i' j)
  have htable (k : Fin d.numClasses) :
      d.reindexTableOfMap f table i (d.classOf k) = f (table i' k) := by
    rw [← (finCongr d.numClasses_eq_card_conjClasses).apply_symm_apply i,
      d.reindexTableOfMap_apply_classOf]
  rw [centralCharacterRow_apply, htable j, ← d.classOf_index (1 : G),
    htable (d.index 1), h.table_index_one, map_natCast, d.reindexModularRow_classOf,
    ← d.card_classFinset]
  apply (div_eq_iff hdeg).2
  simpa only [map_mul, map_natCast, mul_comm] using hconvert.symm

/-- The mapped rows of a certified exact table are orthonormal for the complex Hermitian
character pairing. -/
private theorem row_orthonormal_reindexTableOfMap (f : R →+* ℂ)
    (hf : ∀ x, f (conj x) = star (f x))
    (i j : Fin (Nat.card (ConjClasses G))) :
    (Nat.card G : ℂ)⁻¹ * ∑ C : ConjClasses G,
        (Nat.card C.carrier : ℂ) * d.reindexTableOfMap f table i C *
          (starRingEnd ℂ) (d.reindexTableOfMap f table j C) = if i = j then 1 else 0 := by
  let i' := (finCongr d.numClasses_eq_card_conjClasses).symm i
  let j' := (finCongr d.numClasses_eq_card_conjClasses).symm j
  have hsum := congrArg f (h.row_orthogonal i' j')
  have hG : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have htable_i (k : Fin d.numClasses) :
      d.reindexTableOfMap f table i (d.classOf k) = f (table i' k) := by
    rw [← (finCongr d.numClasses_eq_card_conjClasses).apply_symm_apply i,
      d.reindexTableOfMap_apply_classOf]
  have htable_j (k : Fin d.numClasses) :
      d.reindexTableOfMap f table j (d.classOf k) = f (table j' k) := by
    rw [← (finCongr d.numClasses_eq_card_conjClasses).apply_symm_apply j,
      d.reindexTableOfMap_apply_classOf]
  simp only [Nat.card_eq_fintype_card]
  rw [← d.equivConjClasses.sum_comp]
  simp only [d.equivConjClasses_apply, htable_i, htable_j, starRingEnd_apply]
  have hsum' :
      (∑ k, (Fintype.card (d.classOf k).carrier : ℂ) * f (table i' k) *
          star (f (table j' k))) =
        if i' = j' then (Fintype.card G : ℂ) else 0 := by
    have hcard (k : Fin d.numClasses) :
        Fintype.card (d.classOf k).carrier = (d.classFinset k).card := by
      rw [← Nat.card_eq_fintype_card, ← d.card_classFinset]
    simp only [hcard]
    by_cases hij' : i' = j'
    · rw [ite_eq_left hij'] at hsum ⊢
      simpa only [map_sum, map_mul, map_natCast, hf] using hsum
    · rw [ite_eq_right hij'] at hsum ⊢
      simpa only [map_sum, map_mul, map_natCast, map_zero, hf] using hsum
  rw [hsum']
  have hij : i' = j' ↔ i = j :=
    (finCongr d.numClasses_eq_card_conjClasses).symm.injective.eq_iff
  rw [if_congr hij rfl rfl]
  split_ifs <;> simp [hG]

/-- **A certified exact table satisfies the complex character-table specification after mapping
through a star-preserving ring homomorphism.** -/
theorem isCharacterTableSpec (f : R →+* ℂ) (hf : ∀ x, f (conj x) = star (f x)) :
    IsCharacterTableSpec G (d.reindexTableOfMap f table) where
  exists_degree i := by
    let i' := (finCongr d.numClasses_eq_card_conjClasses).symm i
    refine ⟨degree i', h.degree_pos i', ?_, ?_⟩
    · rw [← d.classOf_index (1 : G),
        ← (finCongr d.numClasses_eq_card_conjClasses).apply_symm_apply i,
        d.reindexTableOfMap_apply_classOf, h.table_index_one, map_natCast]
    · simpa only [Nat.card_eq_fintype_card] using h.degree_dvd i'
  sum_degree_sq := by
    rw [@Nat.card_eq_fintype_card G, ← h.sum_degree_sq,
      ← (finCongr d.numClasses_eq_card_conjClasses).sum_comp]
    simp only [← d.classOf_index (1 : G), d.reindexTableOfMap_apply_classOf,
      h.table_index_one, map_natCast]
    exact_mod_cast rfl
  row_orthonormal := h.row_orthonormal_reindexTableOfMap f hf
  row_eigen i := by
    rw [h.centralCharacterRow_reindexTableOfMap f i]
    exact (d.isModularEigenrow_iff_isClassEigenrow _).mp
      (h.central_eigen_map f ((finCongr d.numClasses_eq_card_conjClasses).symm i))

end IsExactCharacterTableSpec

end ClassData

end TauCeti
