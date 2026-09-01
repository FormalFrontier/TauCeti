/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.FinEnum
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Checker
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Lift

/-!
# The assembled cyclotomic Dixon--Schneider solver

The modular phase of the Burnside--Dixon--Schneider algorithm returns the unordered set of
central-character rows over `ZMod p`.  For a character table with values in
`TauCeti.Cyclotomic e`, reconstructing one exact entry needs its residues at every conjugate
primitive `e`-th root modulo `p`, not just at one root.  Each conjugate of an exact central
character is again a central character, so every one of those residue rows belongs to the same
modular search.

This file performs the missing assembly.  For `q : TauCeti.DixonPrimeData G`, it enumerates the
possible alignments of the modular rows at all conjugate roots.  It numbers the searched rows once
and represents each conjugate slice by a permutation of that numbering.  It applies
`TauCeti.Cyclotomic.lift` entrywise to obtain
candidate exact central-character rows, enumerates the possible positive degree vectors, and
computes the candidate ordinary table by coefficientwise exact division.  The executable
cyclotomic checker is the final gate: a candidate is returned only when the division-free
central-to-ordinary identity and all other character-table identities hold.

The result is deliberately an `Option`.  `none` records that no alignment and degree vector passes
the exact checker; no unverified coefficient bound is used to claim success.  Soundness is
unconditional: every returned table satisfies `TauCeti.IsCharacterTableSpec` after the distinguished
embedding into `ℂ`.  Completeness of the search at a sufficiently large Dixon prime additionally
needs the coefficient bound discussed in the cyclotomic-lift module.

## Main definitions

* `TauCeti.ClassData.CyclotomicCharacterTableData`: numbered exact cyclotomic output data.
* `TauCeti.ClassData.dixonCyclotomicCharacterTable?`: the executable exact-cyclotomic solver.

## Main results

* `conjugateResidueRow_mem_centralCharacterSearch_of_dixonCyclotomicCharacterTable?_eq_some`:
  every conjugate residue row of a returned central table comes from the modular search.
* `TauCeti.ClassData.isCyclotomicCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some`:
  every returned output passes the exact cyclotomic certificate.
* `TauCeti.ClassData.isCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some`: after
  embedding, every returned table satisfies the complex character-table specification.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik **10** (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, Journal of Symbolic Computation
  **9** (1990), 601--606.
* The character-theory roadmap, Layer 6, “The assembled solver”.
-/

public section

namespace TauCeti

open Matrix

namespace ClassData

universe u

variable {G : Type u} [Group G] (d : ClassData G)

/-- Candidate numbered data for the exact-cyclotomic Dixon--Schneider solver.  The fields are
certified only after the candidate passes `cyclotomicCharacterTableChecker`. -/
@[ext]
structure CyclotomicCharacterTableData (e : ℕ) where
  /-- A candidate exact central-character table. -/
  omega : Matrix (Fin d.numClasses) (Fin d.numClasses)
    (Cyclotomic e)
  /-- A candidate exact ordinary character table. -/
  table : Matrix (Fin d.numClasses) (Fin d.numClasses)
    (Cyclotomic e)
  /-- Candidate character degrees. -/
  degree : Fin d.numClasses → ℕ

variable [Fintype G] [DecidableEq G]

/-- The modular central-character rows as an executable list. -/
private def modularCentralRowsList (q : DixonPrimeData G) :
    List (Fin d.numClasses → ZMod q.p) :=
  letI : FinEnum (ZMod q.p) :=
    FinEnum.ofEquiv (Fin q.p) (ZMod.finEquiv q.p).symm.toEquiv
  let searchedRows : Finset (Fin d.numClasses → ZMod q.p) :=
    d.centralCharacterSearch
  (FinEnum.toList (Fin d.numClasses → ZMod q.p)).filter fun row ↦
    decide (row ∈ searchedRows)

/-- Membership in the executable row list is membership in the modular search. -/
@[simp]
private theorem mem_modularCentralRowsList (q : DixonPrimeData G)
    {row : Fin d.numClasses → ZMod q.p} :
    row ∈ d.modularCentralRowsList q ↔ row ∈ d.centralCharacterSearch := by
  let _ : FinEnum (ZMod q.p) :=
    FinEnum.ofEquiv (Fin q.p) (ZMod.finEquiv q.p).symm.toEquiv
  simp [modularCentralRowsList]

/-- The executable modular-row list has one row for each conjugacy class at a Dixon prime. -/
private theorem length_modularCentralRowsList (q : DixonPrimeData G) :
    (d.modularCentralRowsList q).length = d.numClasses := by
  let _ : FinEnum (ZMod q.p) :=
    FinEnum.ofEquiv (Fin q.p) (ZMod.finEquiv q.p).symm.toEquiv
  have hnodup : (d.modularCentralRowsList q).Nodup := by
    rw [modularCentralRowsList]
    exact FinEnum.nodup_toList.filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  have hrows : (d.modularCentralRowsList q).toFinset =
      d.centralCharacterSearch := by
    ext row
    simp [mem_modularCentralRowsList]
  rw [hrows, d.card_centralCharacterSearch_of_isGoodDixonPrime q.isGoodDixonPrime]

/-- The canonical numbering of the modular central-character rows.  The default branch of
`List.getD` is unreachable because the row list has exactly `d.numClasses` entries. -/
private def canonicalModularRow (q : DixonPrimeData G)
    (i : Fin d.numClasses) : Fin d.numClasses → ZMod q.p :=
  (d.modularCentralRowsList q).getD i 0

/-- Every canonically numbered modular row belongs to the central-character search. -/
private theorem canonicalModularRow_mem (q : DixonPrimeData G) (i : Fin d.numClasses) :
    d.canonicalModularRow q i ∈ d.centralCharacterSearch := by
  rw [canonicalModularRow, List.getD_eq_getElem _ _
    (by simp [length_modularCentralRowsList d q, i.isLt])]
  exact (mem_modularCentralRowsList d q).mp (List.getElem_mem _)

/-- Divide every power-basis coordinate by a positive integer.  Candidate ordinary-character
entries use this computable quotient; the exact checker subsequently verifies that the division
was exact, so truncating integer division can never enter a returned result. -/
private def cyclotomicQuotient (e : ℕ) (x : Cyclotomic e) (n : ℕ) : Cyclotomic e :=
  Cyclotomic.ofCoeffList e (x.coeffs.map fun c ↦ c / (n : ℤ))

/-- Enumerate the exact-cyclotomic candidates inspected by the solver.

For every Galois-conjugate root, a permutation chooses how its modular rows align with the
canonical numbering.  The first conjugate uses the identity permutation, removing the irrelevant
simultaneous permutation of the output rows. -/
private def dixonCyclotomicCharacterTableCandidates (e : ℕ)
    (he : e = Monoid.exponent G) (q : DixonPrimeData G) :
    List (d.CyclotomicCharacterTableData e) :=
  let firstConjugate : Fin e.totient :=
    ⟨0, Nat.totient_pos.mpr (Nat.pos_of_ne_zero (he ▸ Monoid.exponent_ne_zero_of_finite))⟩
  let modularRows := d.modularCentralRowsList q
  let canonicalRows := Array.ofFn fun i : Fin d.numClasses ↦ modularRows.getD i 0
  let residuePermutations :=
    (FinEnum.toList (Fin e.totient → Fin d.numClasses → Fin d.numClasses)).filter fun perms ↦
      decide ((∀ i, perms firstConjugate i = i) ∧
        ∀ j, Function.Injective (perms j))
  let Degree :=
    {n : Fin (Fintype.card G + 1) // n ≠ 0 ∧ (n : ℕ) ∣ Fintype.card G}
  let degreeAssignments :=
    (FinEnum.toList (Fin d.numClasses → Degree)).filter fun degree ↦
      decide (∑ i, (degree i : ℕ) ^ 2 = Fintype.card G)
  residuePermutations.flatMap fun perms ↦
    let omegaEntries := Array.ofFn fun i ↦ Array.ofFn fun k ↦
      Cyclotomic.lift e q.root fun j ↦
        (canonicalRows[(perms j i).val]'(by simp [canonicalRows])) k
    let omega : Matrix (Fin d.numClasses) (Fin d.numClasses)
        (Cyclotomic e) :=
      fun i k ↦
        (omegaEntries[i.val]'(by simp [omegaEntries]))[k.val]'(by simp [omegaEntries])
    degreeAssignments.map fun degrees ↦
      let degree : Fin d.numClasses → ℕ := fun i ↦ degrees i
      let table : Matrix (Fin d.numClasses) (Fin d.numClasses)
          (Cyclotomic e) :=
        fun i k ↦ cyclotomicQuotient e
          ((degree i : Cyclotomic e) * omega i k)
          (d.classFinset k).card
      { omega := omega, table := table, degree := degree }

/-- Every conjugate residue row of an enumerated candidate belongs to the modular
central-character search. -/
private theorem conjugateResidueRow_mem_of_mem_candidates (e : ℕ) (he : e = Monoid.exponent G)
    (q : DixonPrimeData G) {output : d.CyclotomicCharacterTableData e}
    (houtput : output ∈ d.dixonCyclotomicCharacterTableCandidates e he q)
    (i : Fin d.numClasses) (j : Fin e.totient) :
    (fun k ↦ Cyclotomic.conjugateResidues q.root (output.omega i k) j) ∈
      d.centralCharacterSearch := by
  let _ : FinEnum (ZMod q.p) :=
    FinEnum.ofEquiv (Fin q.p) (ZMod.finEquiv q.p).symm.toEquiv
  simp only [dixonCyclotomicCharacterTableCandidates, List.mem_flatMap, List.mem_map,
    List.mem_filter, FinEnum.mem_toList, true_and, decide_eq_true_eq] at houtput
  obtain ⟨perms, _, degrees, _, rfl⟩ := houtput
  have hrow :
      (fun k ↦ Cyclotomic.conjugateResidues q.root
        (Cyclotomic.lift e q.root fun l ↦
          d.canonicalModularRow q (perms l i) k) j) =
        d.canonicalModularRow q (perms j i) := by
    funext k
    have hroot : IsPrimitiveRoot q.root e := by simpa [he] using q.isPrimitiveRoot_root
    exact congrFun
      (Cyclotomic.conjugateResidues_lift hroot
        (fun l ↦ d.canonicalModularRow q (perms l i) k)) j
  simp only [canonicalModularRow] at hrow
  simp only [Array.getElem_ofFn, Fin.eta]
  rw [hrow]
  simpa only [canonicalModularRow] using canonicalModularRow_mem d q (perms j i)

/-- Run the exact-cyclotomic stage of the Dixon--Schneider character-table algorithm.

The function aligns the modular rows at all conjugate roots, applies the structured cyclotomic
lift, searches the possible character degrees, computes candidate ordinary-character entries,
and returns the first candidate accepted by the exact cyclotomic checker.  The conductor `e` is
passed explicitly, together with its equality to the group exponent, so evaluating the solver
does not attempt to compute Mathlib's noncomputable `Monoid.exponent`. -/
def dixonCyclotomicCharacterTable? (e : ℕ) (he : e = Monoid.exponent G)
    (q : DixonPrimeData G) :
    Option (d.CyclotomicCharacterTableData e) :=
  (d.dixonCyclotomicCharacterTableCandidates e he q).find? fun output ↦
    d.cyclotomicCharacterTableChecker e
      output.omega output.table output.degree

/-- Every conjugate residue row of a successful exact-cyclotomic output is one of the rows
returned by the modular central-character search. -/
theorem conjugateResidueRow_mem_centralCharacterSearch_of_dixonCyclotomicCharacterTable?_eq_some
    {d : ClassData G} (e : ℕ) (he : e = Monoid.exponent G) (q : DixonPrimeData G)
    {output : d.CyclotomicCharacterTableData e}
    (h : d.dixonCyclotomicCharacterTable? e he q = some output)
    (i : Fin d.numClasses) (j : Fin e.totient) :
    (fun k ↦ Cyclotomic.conjugateResidues q.root (output.omega i k) j) ∈
      d.centralCharacterSearch := by
  simp only [dixonCyclotomicCharacterTable?] at h
  exact conjugateResidueRow_mem_of_mem_candidates d e he q (List.mem_of_find?_eq_some h) i j

/-- Every successful exact-cyclotomic Dixon--Schneider output passes the exact cyclotomic
character-table specification. -/
theorem isCyclotomicCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some
    {d : ClassData G} (e : ℕ) (he : e = Monoid.exponent G) (q : DixonPrimeData G)
    {output : d.CyclotomicCharacterTableData e}
    (h : d.dixonCyclotomicCharacterTable? e he q = some output) :
    d.IsCyclotomicCharacterTableSpec e
      output.omega output.table output.degree := by
  simp only [dixonCyclotomicCharacterTable?] at h
  have hcheck := List.find?_some h
  exact (d.cyclotomicCharacterTableChecker_eq_true_iff
    e output.omega output.table output.degree).mp hcheck

/-- Every successful exact-cyclotomic Dixon--Schneider output, embedded in `ℂ` and reindexed by
conjugacy classes, satisfies the complex character-table specification. -/
theorem isCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some
    {d : ClassData G} (e : ℕ) [NeZero e] (he : e = Monoid.exponent G) (q : DixonPrimeData G)
    {output : d.CyclotomicCharacterTableData e}
    (h : d.dixonCyclotomicCharacterTable? e he q = some output) :
    IsCharacterTableSpec G
      (d.complexTableOfCyclotomic e output.table) :=
  (d.isCyclotomicCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some
    e he q h).isCharacterTableSpec

end ClassData

end TauCeti
