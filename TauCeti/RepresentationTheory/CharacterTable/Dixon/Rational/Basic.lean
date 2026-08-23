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

This file contains the group-independent bookkeeping used by rational instances of the
Dixon--Schneider character-table computation. A displayed integral matrix supplies candidate
rows. They are reduced modulo a good Dixon prime, identified with the complete modular search by
the good-prime count, and then recovered entrywise with `ZMod.valMinAbs` when every entry lies in
the signed least-residue range.

## Main definitions

* `TauCeti.ClassData.modularCentralRows`: the reductions of the rows of an integral matrix.
* `TauCeti.ClassData.liftedCentralRows`: signed least representatives of the modular search.

## Main results

* `TauCeti.ClassData.centralCharacterSearch_eq_modularCentralRows_of_isGoodDixonPrime`: candidate
  normalized eigenrows exhaust the modular search when they have the good-prime row count.
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

/-- The rows of an integral matrix, reduced modulo `p` and collected without an ordering. -/
@[expose] def modularCentralRows (p : ℕ)
    (M : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ) :
    Finset (Fin d.numClasses → ZMod p) :=
  Finset.univ.image fun i j => (M i j : ZMod p)

omit [Fintype G] [DecidableEq G] in
/-- A modular row is displayed exactly when it is the reduction of a row of the integral matrix. -/
@[simp]
theorem mem_modularCentralRows_iff {p : ℕ}
    (M : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    {a : Fin d.numClasses → ZMod p} :
    a ∈ d.modularCentralRows p M ↔ ∃ i, (fun j => (M i j : ZMod p)) = a := by
  simp [modularCentralRows]

/-- **Displayed normalized eigenrows exhaust the modular central-character search at a good Dixon
prime** when the displayed set has the required number of rows. -/
theorem centralCharacterSearch_eq_modularCentralRows_of_isGoodDixonPrime
    {p : ℕ} [Fact p.Prime] (hp : IsGoodDixonPrime G p)
    (M : Matrix (Fin d.numClasses) (Fin d.numClasses) ℤ)
    (hone : ∀ i, (M i (d.index 1) : ZMod p) = 1)
    (heig : ∀ i, d.IsModularEigenrow (fun j => (M i j : ZMod p)))
    (hcard : (d.modularCentralRows p M).card = d.numClasses) :
    d.centralCharacterSearch (F := ZMod p) = d.modularCentralRows p M := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · rw [modularCentralRows, Finset.image_subset_iff]
    intro i _
    rw [d.mem_centralCharacterSearch]
    exact ⟨hone i, heig i⟩
  · rw [d.card_centralCharacterSearch_of_isGoodDixonPrime hp, hcard]

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
    (hsearch : d.centralCharacterSearch (F := ZMod p) = d.modularCentralRows p M)
    (hbound : ∀ i j, 2 * (M i j).natAbs < p) :
    d.liftedCentralRows p = Finset.univ.image fun i => M i := by
  rw [liftedCentralRows, hsearch, modularCentralRows, Finset.image_image]
  apply Finset.image_congr
  intro i _
  funext j
  exact ZMod.valMinAbs_intCast_of_two_mul_natAbs_lt (hbound i j)

end ClassData

end TauCeti
