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
possible positive character degrees dividing the group order, and reconstructs the ordinary table
from the central-character table. It returns the first candidate accepted by the exact integer
checker.

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
* `TauCeti.ClassData.liftedCentralRowsList`: an executable enumeration of the existing lifted-row
  finset.
* `TauCeti.ClassData.dixonRationalCharacterTable?`: the executable rational-stage solver.

## Main results

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

/-- An executable list of the signed integral lifts of the modular central-character search. Its
body is exposed so downstream acceptance examples can check the concrete enumeration. -/
@[expose] def liftedCentralRowsList (p : ℕ) [Fact p.Prime] [FinEnum (ZMod p)] :
    List (Fin d.numClasses → ℤ) :=
  ((FinEnum.toList (Fin d.numClasses → ZMod p)).filter fun row =>
    row ∈ d.centralCharacterSearch (F := ZMod p)).map fun row j => (row j).valMinAbs

/-- The executable lifted-row list enumerates exactly `liftedCentralRows`. -/
@[simp]
theorem liftedCentralRowsList_toFinset (p : ℕ) [Fact p.Prime] [FinEnum (ZMod p)] :
    (d.liftedCentralRowsList p).toFinset = d.liftedCentralRows p := by
  ext row
  simp [liftedCentralRowsList, liftedCentralRows]

/-- Enumerate the candidate data inspected by the rational Dixon--Schneider solver. Its body is
exposed so downstream acceptance examples can exhibit a successful candidate. -/
@[expose] def dixonRationalCharacterTableCandidates (p : ℕ) [Fact p.Prime] :
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

/-- Run the integer-valued stage of the Dixon--Schneider character-table algorithm.

The modular search and signed lift determine an unordered finite set of candidate central-character
rows. The solver enumerates its injective row numberings and the degree vectors whose positive
entries divide `|G|` and whose squares sum to `|G|`; for each pair, the ordinary table is obtained
by exact integer division and checked by `TauCeti.ClassData.integerCharacterTableChecker`.

Soundness requires only that `p` is prime. A good-prime certificate is needed for completeness, not
for checking a candidate returned by this function. -/
def dixonRationalCharacterTable? (p : ℕ) [Fact p.Prime] :
    Option d.IntegerCharacterTableData :=
  (d.dixonRationalCharacterTableCandidates p).find? fun output =>
    d.integerCharacterTableChecker output.omega output.table output.degree

/-- The rational solver succeeds exactly when its candidate list contains data satisfying the
integer character-table specification. -/
theorem isSome_dixonRationalCharacterTable_iff (p : ℕ) [Fact p.Prime] :
    (d.dixonRationalCharacterTable? p).isSome ↔
      ∃ output ∈ d.dixonRationalCharacterTableCandidates p,
        d.IsIntegerCharacterTableSpec output.omega output.table output.degree := by
  rw [dixonRationalCharacterTable?, List.find?_isSome]
  simp only [d.integerCharacterTableChecker_eq_true_iff]

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
