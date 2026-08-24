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
algorithm. Given executable conjugacy-class data and a certified Dixon prime, it performs the
modular common-eigenrow search, lifts the rows by signed least representatives, searches the
possible positive character degrees dividing the group order, and reconstructs the ordinary table
from the central-character table. It returns the first candidate accepted by the exact integer
checker.

The result is an `Option`: `none` honestly records that the character table is not integer-valued,
that the chosen residue window was too small, or that no ordering of the lifted rows passed the
checker. A successful result is certified by
`TauCeti.ClassData.isIntegerCharacterTableSpec_of_rationalCharacterTableDixon_eq_some` and hence,
after embedding in `ℂ`, by
`TauCeti.ClassData.isCharacterTableSpec_of_rationalCharacterTableDixon_eq_some`.

This is the first assembled solver promised by the rational-table stage of the character-theory
roadmap. The later general solver replaces signed integer lifting by the structured cyclotomic lift;
no claim about that later stage is made here.

## Main definitions

* `TauCeti.ClassData.IntegerCharacterTable`: the numbered exact output data.
* `TauCeti.ClassData.rationalCharacterTableDixon`: the executable rational-stage solver.

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

variable {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable (d : ClassData G)

/-- The three exact numbered arrays produced by the integer-valued Dixon--Schneider solver: the
central-character table, the ordinary character table, and the character degrees. -/
@[ext]
structure IntegerCharacterTable where
  /-- The normalized central-character table. -/
  omega : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ
  /-- The ordinary character table. -/
  table : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ
  /-- The positive character degrees. -/
  degree : Fin d.numClasses → ℕ
deriving DecidableEq

variable {d}

/-- Run the integer-valued stage of the Dixon--Schneider character-table algorithm.

The modular search and signed lift determine an unordered finite set of candidate central-character
rows. The solver enumerates its injective row numberings and the degree vectors whose positive
entries divide `|G|` and whose squares sum to `|G|`; for each pair, the ordinary table is obtained
by exact integer division and checked by `TauCeti.ClassData.integerCharacterTableChecker`. -/
@[expose] def rationalCharacterTableDixon (q : DixonPrimeData G) :
    Option d.IntegerCharacterTable :=
  letI : Fact q.p.Prime := q.fact_prime
  letI : FinEnum (ZMod q.p) :=
    FinEnum.ofEquiv (Fin q.p) (ZMod.finEquiv q.p).symm.toEquiv
  let searchedRows := d.centralCharacterSearch (F := ZMod q.p)
  -- `Finset.toList` is noncomputable. Enumerating the finite row type and retaining exactly the
  -- members of the already-computed search gives its rows a deterministic executable order.
  let modularRows : List (Fin d.numClasses → ZMod q.p) :=
    (FinEnum.toList (Fin d.numClasses → ZMod q.p)).filter fun row =>
      row ∈ searchedRows
  let liftedRows : List (Fin d.numClasses → ℤ) :=
    modularRows.map fun row j => (row j).valMinAbs
  let rowAssignments :=
    (FinEnum.toList (Fin d.numClasses → {row // row ∈ liftedRows})).filter fun rows =>
      decide (Function.Injective rows)
  let Degree := {n : Fin (Fintype.card G + 1) // n ≠ 0 ∧ (n : ℕ) ∣ Fintype.card G}
  let degreeAssignments :=
    (FinEnum.toList (Fin d.numClasses → Degree)).filter fun degree =>
      decide (∑ i, (degree i : ℕ) ^ 2 = Fintype.card G)
  let candidates : List d.IntegerCharacterTable :=
    rowAssignments.flatMap fun rows => degreeAssignments.map fun degrees =>
      let omega : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ :=
        fun i => rows i
      let degree : Fin d.numClasses → ℕ := fun i => degrees i
      { omega := omega
        degree := degree
        table := fun i j =>
          (degree i : ℤ) * omega i j / (d.classFinset j).card }
  candidates.find? fun output =>
    d.integerCharacterTableChecker output.omega output.table output.degree

/-- Every successful rational Dixon--Schneider output passes the exact integer character-table
specification. -/
theorem isIntegerCharacterTableSpec_of_rationalCharacterTableDixon_eq_some
    (q : DixonPrimeData G) {output : d.IntegerCharacterTable}
    (h : d.rationalCharacterTableDixon q = some output) :
    d.IsIntegerCharacterTableSpec output.omega output.table output.degree := by
  simp only [rationalCharacterTableDixon] at h
  have hcheck := List.find?_some h
  exact (d.integerCharacterTableChecker_eq_true_iff _ _ _).mp hcheck

/-- Every successful rational Dixon--Schneider output, cast to `ℂ` and reindexed by conjugacy
classes, satisfies the complex character-table specification. -/
theorem isCharacterTableSpec_of_rationalCharacterTableDixon_eq_some
    (q : DixonPrimeData G) {output : d.IntegerCharacterTable}
    (h : d.rationalCharacterTableDixon q = some output) :
    IsCharacterTableSpec G (d.complexTableOfInteger output.table) :=
  (d.isIntegerCharacterTableSpec_of_rationalCharacterTableDixon_eq_some q h).isCharacterTableSpec

end ClassData

end TauCeti
