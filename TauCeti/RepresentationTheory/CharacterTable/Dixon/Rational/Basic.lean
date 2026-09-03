/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.ValMinAbs
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount

/-!
# Rational lifting of modular central-character rows

This file contains the group-independent bookkeeping for the last step of the rational instances of
the Dixon--Schneider character-table computation: recovering a displayed integral matrix entrywise
with `ZMod.valMinAbs`, once the modular search is known to return exactly the reductions of its
rows and every entry lies in the signed least-residue range.

The earlier steps live upstream: the reduced candidate rows are collected by
`TauCeti.ClassData.rowsOfMap`, in
`TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic`, and
`TauCeti.ClassData.centralCharacterSearch_eq_rowsOfMap_of_isGoodDixonPrime` identifies
them with the complete modular search at a good Dixon prime, in
`TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount`; the
hypothesis of the theorem below is stated in terms of them.

## Main definitions

* `TauCeti.ClassData.liftedCentralRows`: signed least representatives of the modular search.

## Main results

* `TauCeti.ClassData.liftedCentralRows_eq_image_of_centralCharacterSearch_eq`: a displayed integral
  matrix is recovered from the modular search when all its entries lie in the signed residue range.

## References

This is shared infrastructure for the rational-table milestone in Layer 6 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).
-/

public section

namespace TauCeti

namespace ClassData

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable (d : ClassData G)

/-- The signed integral rows obtained by applying `ZMod.valMinAbs` to the output of the modular
central-character search. -/
@[expose] def liftedCentralRows (p : ℕ) [Fact p.Prime] :
    Finset (Fin d.numClasses → ℤ) :=
  (d.centralCharacterSearch (F := ZMod p)).image fun a j => (a j).valMinAbs

/-- A lifted row occurs exactly when it is obtained entrywise from a row in the modular search. -/
@[simp]
theorem mem_liftedCentralRows_iff {p : ℕ} [Fact p.Prime]
    {a : Fin d.numClasses → ℤ} :
    a ∈ d.liftedCentralRows p ↔
      ∃ b ∈ d.centralCharacterSearch (F := ZMod p), (fun j => (b j).valMinAbs) = a := by
  simp [liftedCentralRows]

/-- **Signed least representatives recover a displayed integral matrix from the modular search**
when each entry lies in the signed least-residue range. -/
theorem liftedCentralRows_eq_image_of_centralCharacterSearch_eq
    {p : ℕ} [Fact p.Prime]
    (M : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    (hsearch : d.centralCharacterSearch (F := ZMod p) =
      d.rowsOfMap (fun x : ℤ => (x : ZMod p)) M)
    (hbound : ∀ i j, 2 * (M i j).natAbs < p) :
    d.liftedCentralRows p = Finset.univ.image fun i => M i := by
  rw [liftedCentralRows, hsearch, rowsOfMap, Finset.image_image]
  apply Finset.image_congr
  intro i _
  funext j
  exact ZMod.valMinAbs_intCast_of_two_mul_natAbs_lt (hbound i j)

end ClassData

end TauCeti
