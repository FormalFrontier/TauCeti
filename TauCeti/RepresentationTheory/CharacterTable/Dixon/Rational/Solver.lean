/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.FinEnum
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.IntegerChecker
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.Basic

/-!
# The assembled rational Dixon--Schneider solver

This file assembles the integer-valued stage of the Burnside--Dixon--Schneider character-table
algorithm. Given executable conjugacy-class data and a prime, it performs the
modular common-eigenrow search, lifts the rows by signed least representatives, searches the
possible positive character degrees dividing the group order, and computes candidate integer
quotients for the ordinary table from the central-character table. The exact integer checker then
verifies the corresponding division-free equality, so the conversion is exact for accepted outputs.

The result is an `Option`: `none` honestly records that the character table is not integer-valued,
that the chosen residue window was too small, or that no ordering of the lifted rows passed the
checker. A successful result is certified by
`TauCeti.ClassData.isIntegerCharacterTableSpec_of_dixonRationalCharacterTable_eq_some` and hence,
after embedding in `ℂ`, by
`TauCeti.ClassData.isCharacterTableSpec_of_dixonRationalCharacterTable_eq_some`.

This is the first assembled solver promised by the rational-table stage of the character-theory
roadmap. The later general solver replaces signed integer lifting by the structured cyclotomic lift;
no claim about that later stage is made here.

## Main definitions

* `TauCeti.ClassData.IntegerCharacterTableData`: candidate numbered exact output data.
* `TauCeti.ClassData.dixonRationalCharacterTable?`: the executable rational-stage solver.

## Main results

* `TauCeti.ClassData.isSome_dixonRationalCharacterTable_iff`: the solver succeeds exactly when
  semantically admissible candidate data passes the integer character-table specification.
* `TauCeti.ClassData.mem_liftedCentralRows_of_dixonRationalCharacterTable_eq_some`: the rows of a
  successful output are lifted central-character rows.
* `TauCeti.ClassData.isIntegerCharacterTableSpec_of_dixonRationalCharacterTable_eq_some`: every
  successful output satisfies the exact integer specification.
* `TauCeti.ClassData.isCharacterTableSpec_of_dixonRationalCharacterTable_eq_some`: every successful
  output gives a complex character table up to row permutation.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, Journal of Symbolic Computation 9
  (1990), 601--606.
-/

public section

namespace TauCeti

open Matrix

namespace ClassData

universe u

variable {G : Type u} [Group G] (d : ClassData G)

/-- Candidate numbered data for the integer-valued Dixon--Schneider solver. Normalization,
positivity, and correctness hold only after the candidate passes `integerCharacterTableChecker`. -/
@[ext]
structure IntegerCharacterTableData where
  /-- A candidate central-character table. -/
  omega : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ
  /-- A candidate ordinary character table. -/
  table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ
  /-- Candidate character degrees. -/
  degree : Fin d.numClasses → ℕ

variable [Fintype G] [DecidableEq G]

/-- An executable list of the signed integral lifts of the modular central-character search. -/
private def liftedCentralRowsList (p : ℕ) [Fact p.Prime] [FinEnum (ZMod p)] :
    List (Fin d.numClasses → ℤ) :=
  ((FinEnum.toList (Fin d.numClasses → ZMod p)).filter fun row =>
    row ∈ d.centralCharacterSearch (F := ZMod p)).map fun row j => (row j).valMinAbs

/-- The executable lifted-row list enumerates exactly `liftedCentralRows`. -/
@[simp]
private theorem liftedCentralRowsList_toFinset (p : ℕ) [Fact p.Prime] [FinEnum (ZMod p)] :
    (d.liftedCentralRowsList p).toFinset = d.liftedCentralRows p := by
  ext row
  simp [liftedCentralRowsList, liftedCentralRows]

/-- A row is enumerated by `liftedCentralRowsList` exactly when it is a lifted central row. -/
@[simp]
private theorem mem_liftedCentralRowsList (p : ℕ) [Fact p.Prime] [FinEnum (ZMod p)]
    {row : Fin d.numClasses → ℤ} :
    row ∈ d.liftedCentralRowsList p ↔ row ∈ d.liftedCentralRows p := by
  rw [← List.mem_toFinset, liftedCentralRowsList_toFinset]

/-- Enumerate the candidate data inspected by the rational Dixon--Schneider solver: every
injective numbering of the lifted central rows, paired with every degree vector whose positive
entries divide `|G|` and whose squares sum to `|G|`. Ordinary-table entries are candidate integer
quotients; the checker later verifies that no truncation occurred. -/
private def dixonRationalCharacterTableCandidates (p : ℕ) [Fact p.Prime] :
    List d.IntegerCharacterTableData :=
  letI : FinEnum (ZMod p) :=
    FinEnum.ofEquiv (Fin p) (ZMod.finEquiv p).symm.toEquiv
  let liftedRows := d.liftedCentralRowsList p
  let rowAssignments :=
    (FinEnum.toList (Fin d.numClasses → {row // row ∈ liftedRows})).filter fun rows =>
      decide (Function.Injective rows)
  let Degree := {n : Fin (Fintype.card G + 1) // n ≠ 0 ∧ (n : ℕ) ∣ Fintype.card G}
  let degreeAssignments :=
    (FinEnum.toList (Fin d.numClasses → Degree)).filter fun degree =>
      decide (∑ i, (degree i : ℕ) ^ 2 = Fintype.card G)
  rowAssignments.flatMap fun rows => degreeAssignments.map fun degrees =>
    let omega : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ :=
      fun i => rows i
    let degree : Fin d.numClasses → ℕ := fun i => degrees i
    { omega := omega
      degree := degree
      table := fun i j =>
        (degree i : ℤ) * omega i j / (d.classFinset j).card }

/-- **Characterization of the candidates inspected by the rational solver.** Candidate data is
enumerated exactly when its rows are an injective numbering of the lifted central rows, its degrees
are positive divisors of `|G|` whose squares sum to `|G|`, and its table is the integer quotient
computed from the central-character table. -/
private theorem mem_dixonRationalCharacterTableCandidates_iff (p : ℕ) [Fact p.Prime]
    {output : d.IntegerCharacterTableData} :
    output ∈ d.dixonRationalCharacterTableCandidates p ↔
      (∀ i, output.omega i ∈ d.liftedCentralRows p) ∧ Function.Injective output.omega ∧
        (∀ i, 0 < output.degree i) ∧ (∀ i, output.degree i ∣ Fintype.card G) ∧
        ∑ i, output.degree i ^ 2 = Fintype.card G ∧
        ∀ i j, output.table i j =
          (output.degree i : ℤ) * output.omega i j / ((d.classFinset j).card : ℤ) := by
  -- the enumeration instance must be the one the definition installs, not a synthesized one
  let _ : FinEnum (ZMod p) := FinEnum.ofEquiv (Fin p) (ZMod.finEquiv p).symm.toEquiv
  simp only [dixonRationalCharacterTableCandidates, List.mem_flatMap, List.mem_map,
    List.mem_filter, FinEnum.mem_toList, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨rows, hrows, degrees, hdegrees, rfl⟩
    refine ⟨fun i => (mem_liftedCentralRowsList d p).mp (rows i).2, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun i j hij => hrows (Subtype.ext hij)
    · exact fun i => Nat.pos_of_ne_zero fun h => (degrees i).2.1 (Fin.val_eq_zero_iff.mp h)
    · exact fun i => (degrees i).2.2
    · exact hdegrees
    · exact fun i j => rfl
  · rintro ⟨hrow, hinj, hpos, hdvd, hsum, htable⟩
    have hlt : ∀ i, output.degree i < Fintype.card G + 1 := fun i =>
      Nat.lt_succ_of_le (Nat.le_of_dvd Fintype.card_pos (hdvd i))
    refine ⟨fun i => ⟨output.omega i, (mem_liftedCentralRowsList d p).mpr (hrow i)⟩,
      fun i j hij => hinj (congrArg Subtype.val hij),
      fun i => ⟨⟨output.degree i, hlt i⟩, Fin.val_ne_zero_iff.mp (hpos i).ne', hdvd i⟩,
      hsum, ?_⟩
    ext
    · rfl
    · exact (htable _ _).symm
    · rfl

private theorem IsIntegerCharacterTableSpec.omega_injective
    {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ}
    {degree : Fin d.numClasses → ℕ}
    (h : d.IsIntegerCharacterTableSpec omega table degree) : Function.Injective omega := by
  intro i j hij
  by_contra hne
  have hproportional (k : Fin d.numClasses) :
      (degree j : ℤ) * table i k = (degree i : ℤ) * table j k := by
    have hi := h.degree_mul_central i k
    have hj := h.degree_mul_central j k
    rw [hij] at hi
    have hcard : ((d.classFinset k).card : ℤ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr ⟨d.rep k, d.rep_mem_classFinset k⟩).ne'
    apply mul_left_cancel₀ hcard
    calc
      ((d.classFinset k).card : ℤ) * ((degree j : ℤ) * table i k) =
          (degree j : ℤ) * ((degree i : ℤ) * omega j k) := by rw [hi]; ring
      _ = (degree i : ℤ) * ((degree j : ℤ) * omega j k) := by ring
      _ = ((d.classFinset k).card : ℤ) * ((degree i : ℤ) * table j k) := by
        rw [hj]
        ring
  have hscaled :
      (degree j : ℤ) *
          ∑ k, (d.classFinset k).card * table i k * table i k =
        (degree i : ℤ) *
          ∑ k, (d.classFinset k).card * table i k * table j k := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    calc
      (degree j : ℤ) * ((d.classFinset k).card * table i k * table i k) =
          (d.classFinset k).card * table i k * ((degree j : ℤ) * table i k) := by ring
      _ = (d.classFinset k).card * table i k * ((degree i : ℤ) * table j k) := by
        rw [hproportional k]
      _ = (degree i : ℤ) * ((d.classFinset k).card * table i k * table j k) := by ring
  rw [h.row_orthogonal i i, ite_eq_left rfl, h.row_orthogonal i j, ite_eq_right hne,
    mul_zero] at hscaled
  exact (mul_ne_zero (by exact_mod_cast (h.degree_pos j).ne')
    (by exact_mod_cast Fintype.card_pos.ne')) hscaled

private theorem IsIntegerCharacterTableSpec.table_eq_integerQuotient
    {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ}
    {degree : Fin d.numClasses → ℕ}
    (h : d.IsIntegerCharacterTableSpec omega table degree) (i j : Fin d.numClasses) :
    table i j = (degree i : ℤ) * omega i j / ((d.classFinset j).card : ℤ) := by
  rw [h.degree_mul_central]
  exact (Int.mul_ediv_cancel_left (table i j) (by
    exact_mod_cast (Finset.card_pos.mpr ⟨d.rep j, d.rep_mem_classFinset j⟩).ne')).symm

/-- Run the integer-valued stage of the Dixon--Schneider character-table algorithm.

The modular search and signed lift determine an unordered finite set of candidate central-character
rows. The solver enumerates its injective row numberings and the degree vectors whose positive
entries divide `|G|` and whose squares sum to `|G|`; for each pair, the ordinary table is obtained
by integer quotient computation. `TauCeti.ClassData.integerCharacterTableChecker` verifies the
division-free conversion equality, making the quotient exact for every accepted output.

Soundness requires only that `p` is prime. A good-prime certificate is needed for completeness, not
for checking a candidate returned by this function. -/
def dixonRationalCharacterTable? (p : ℕ) [Fact p.Prime] :
    Option d.IntegerCharacterTableData :=
  (d.dixonRationalCharacterTableCandidates p).find? fun output =>
    d.integerCharacterTableChecker output.omega output.table output.degree

/-- The rational solver succeeds exactly when lifted central rows can be assembled into data
satisfying the integer character-table specification. -/
theorem isSome_dixonRationalCharacterTable_iff (p : ℕ) [Fact p.Prime] :
    (d.dixonRationalCharacterTable? p).isSome ↔
      ∃ output : d.IntegerCharacterTableData,
        (∀ i, output.omega i ∈ d.liftedCentralRows p) ∧
        d.IsIntegerCharacterTableSpec output.omega output.table output.degree := by
  rw [dixonRationalCharacterTable?, List.find?_isSome]
  simp only [d.integerCharacterTableChecker_eq_true_iff]
  constructor
  · rintro ⟨output, hcandidates, hspec⟩
    exact ⟨output, (mem_dixonRationalCharacterTableCandidates_iff d p).mp hcandidates |>.1, hspec⟩
  · rintro ⟨output, hrows, hspec⟩
    refine ⟨output, (mem_dixonRationalCharacterTableCandidates_iff d p).mpr ?_, hspec⟩
    exact ⟨hrows, hspec.omega_injective, hspec.degree_pos, hspec.degree_dvd,
      hspec.sum_degree_sq, hspec.table_eq_integerQuotient⟩

/-- The rows of a successful rational Dixon--Schneider output are lifted central-character rows,
so the returned data is one of the numberings produced by the modular search. -/
theorem mem_liftedCentralRows_of_dixonRationalCharacterTable_eq_some
    {d : ClassData G} (p : ℕ) [Fact p.Prime] {output : d.IntegerCharacterTableData}
    (h : d.dixonRationalCharacterTable? p = some output) (i : Fin d.numClasses) :
    output.omega i ∈ d.liftedCentralRows p := by
  simp only [dixonRationalCharacterTable?] at h
  exact ((mem_dixonRationalCharacterTableCandidates_iff d p).mp (List.mem_of_find?_eq_some h)).1 i

/-- Every successful rational Dixon--Schneider output passes the exact integer character-table
specification. -/
theorem isIntegerCharacterTableSpec_of_dixonRationalCharacterTable_eq_some
    {d : ClassData G} (p : ℕ) [Fact p.Prime] {output : d.IntegerCharacterTableData}
    (h : d.dixonRationalCharacterTable? p = some output) :
    d.IsIntegerCharacterTableSpec output.omega output.table output.degree := by
  simp only [dixonRationalCharacterTable?] at h
  have hcheck := List.find?_some h
  exact (d.integerCharacterTableChecker_eq_true_iff _ _ _).mp hcheck

/-- Every successful rational Dixon--Schneider output, cast to `ℂ` and reindexed by conjugacy
classes, satisfies the complex character-table specification. -/
theorem isCharacterTableSpec_of_dixonRationalCharacterTable_eq_some
    {d : ClassData G} (p : ℕ) [Fact p.Prime] {output : d.IntegerCharacterTableData}
    (h : d.dixonRationalCharacterTable? p = some output) :
    IsCharacterTableSpec G (d.complexTableOfInteger output.table) :=
  (d.isIntegerCharacterTableSpec_of_dixonRationalCharacterTable_eq_some p h).isCharacterTableSpec

end ClassData

end TauCeti
