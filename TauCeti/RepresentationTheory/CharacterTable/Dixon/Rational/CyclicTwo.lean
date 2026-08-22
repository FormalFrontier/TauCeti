/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Cyclic

/-!
# The rational Dixon computation for the cyclic group of order two

This file runs the rational stage of the Dixon--Schneider character-table algorithm for
`Multiplicative (ZMod 2)`.  The two conjugacy classes are the identity singleton and the singleton
containing the nontrivial element, in that order, as numbered by `TauCeti.cyclicClassData 2`.

The certified Dixon prime is `3`: it does not divide the group order, the exponent `2` divides
`3 - 1`, and the discrete size bound is `2 * Nat.sqrt 2 = 2 < 3`.  The element `-1` is the
required primitive square root of unity modulo `3`.

The simultaneous eigenvector search over the certified Dixon prime `3` returns exactly the
reductions of the two displayed central-character rows.  Signed least representatives lift those
rows back to the integers.  Since every class is a singleton and both displayed degrees are one,
the ordinary table is set equal entrywise to the central-character table.  Identifying its rows
with the group's irreducible characters is not formalized here.

Completeness does not rely on evaluating the entire search.  Each displayed row is checked against
the class-algebra equations, and the good-prime structure theorem proves that the search has exactly
two outputs.

## Main definitions

* `TauCeti.cyclicGroupTwoDixonPrimeData`: the prime `3` and its primitive square root `-1`.
* `TauCeti.cyclicGroupTwoCentralCharacterTable`: the two integral central-character rows.
* `TauCeti.cyclicGroupTwoModularCentralRows`: their reductions modulo `3`.
* `TauCeti.cyclicGroupTwoCharacterTable`: the resulting ordinary integral character table.

## Main results

* `TauCeti.cyclicGroupTwo_centralCharacterSearch`: the modular search returns exactly the two
  displayed reductions.
* `TauCeti.cyclicGroupTwo_liftedCentralRows`: signed least representatives recover the displayed
  integral rows.
* `TauCeti.cyclicGroupTwo_degree_mul_centralCharacterTable`: the division-free conversion to the
  ordinary character table.

## References

This implements cyclic `C₂` in “Rational tables (first executable milestone)” in Layer 6 of the
[character theory roadmap][roadmap].  Connecting this exact output to the general table checker
remains part of the assembled solver target.

The worked computation follows
`TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.DihedralFour`; the prime certificate
follows `TauCeti.RepresentationTheory.CharacterTable.Dixon.Dihedral`.

[roadmap]: https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601--606.
-/

public section

namespace TauCeti

open Matrix

/-- **`3` is a good Dixon prime for the cyclic group of order two**: `3 ∤ 2`, the exponent `2`
divides `2 = 3 - 1`, and `2⌊√2⌋ = 2 < 3`. -/
theorem isGoodDixonPrime_cyclicGroup_two_three :
    IsGoodDixonPrime (Multiplicative (ZMod 2)) 3 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · simp
  · simp
  · norm_num

/-- Dixon prime data for the cyclic group of order two: the prime `3`, with `-1` as its primitive
square root of unity. -/
@[expose] def cyclicGroupTwoDixonPrimeData :
    DixonPrimeData (Multiplicative (ZMod 2)) where
  p := 3
  root := -1
  isGoodDixonPrime := isGoodDixonPrime_cyclicGroup_two_three
  isPrimitiveRoot_root := by
    simpa using (IsPrimitiveRoot.neg_one (R := ZMod 3) 3 (by decide))

/-- The prime carried by `TauCeti.cyclicGroupTwoDixonPrimeData` is `3`. -/
@[simp]
theorem cyclicGroupTwoDixonPrimeData_p : cyclicGroupTwoDixonPrimeData.p = 3 := rfl

/-- The primitive square root carried by `TauCeti.cyclicGroupTwoDixonPrimeData` is `-1`. -/
@[simp]
theorem cyclicGroupTwoDixonPrimeData_root : cyclicGroupTwoDixonPrimeData.root = -1 := rfl

/-- The numbered conjugacy classes of the cyclic group of order two. -/
abbrev CyclicGroupTwoClassIndex := Fin (cyclicClassData 2).numClasses

/-- **The integral central-character table of the cyclic group of order two.** Columns are the
identity class and the nontrivial class, in the order fixed by `TauCeti.cyclicClassData 2`. -/
def cyclicGroupTwoCentralCharacterTable :
    Matrix CyclicGroupTwoClassIndex CyclicGroupTwoClassIndex ℤ :=
  !![1,  1;
     1, -1]

/-- The entries of the integral central-character table. -/
@[simp]
theorem cyclicGroupTwoCentralCharacterTable_apply (i j : CyclicGroupTwoClassIndex) :
    cyclicGroupTwoCentralCharacterTable i j =
      !![1,  1;
         1, -1] i j := by
  rfl

/-- The displayed central-character rows reduced modulo the certified Dixon prime `3`. -/
def cyclicGroupTwoModularCentralRows :
    Finset (CyclicGroupTwoClassIndex → ZMod 3) :=
  Finset.univ.image fun i j => (cyclicGroupTwoCentralCharacterTable i j : ZMod 3)

/-- A modular row is displayed exactly when it is the reduction of a row of the integral table. -/
@[simp]
theorem mem_cyclicGroupTwoModularCentralRows_iff
    {a : CyclicGroupTwoClassIndex → ZMod 3} :
    a ∈ cyclicGroupTwoModularCentralRows ↔
      ∃ i, (fun j => (cyclicGroupTwoCentralCharacterTable i j : ZMod 3)) = a := by
  simp [cyclicGroupTwoModularCentralRows]

/-- Every displayed integral row satisfies the numbered class-algebra eigenrow equations. -/
theorem isModularEigenrow_cyclicGroupTwoCentralCharacterTable_int
    (i : CyclicGroupTwoClassIndex) :
    (cyclicClassData 2).IsModularEigenrow
      (fun j => cyclicGroupTwoCentralCharacterTable i j) := by
  rw [(cyclicClassData 2).isModularEigenrow_iff]
  fin_cases i <;> decide

/-- Reindexing a displayed integral row by the actual conjugacy classes gives a class-algebra
eigenrow. -/
theorem isClassEigenrow_cyclicGroupTwoCentralCharacterTable
    (i : CyclicGroupTwoClassIndex) :
    IsClassEigenrow ((cyclicClassData 2).reindexModularRow
      fun j => cyclicGroupTwoCentralCharacterTable i j) :=
  ((cyclicClassData 2).isModularEigenrow_iff_isClassEigenrow _).mp
    (isModularEigenrow_cyclicGroupTwoCentralCharacterTable_int i)

/-- The explicit set of modular rows has two elements. -/
@[simp]
theorem card_cyclicGroupTwoModularCentralRows :
    cyclicGroupTwoModularCentralRows.card = 2 := by
  decide

/-- **The executable modular central-character search returns precisely the two reductions in
`TauCeti.cyclicGroupTwoCentralCharacterTable`.** -/
theorem cyclicGroupTwo_centralCharacterSearch :
    (cyclicClassData 2).centralCharacterSearch (F := ZMod 3) =
      cyclicGroupTwoModularCentralRows := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · rw [cyclicGroupTwoModularCentralRows, Finset.image_subset_iff]
    intro i _
    rw [(cyclicClassData 2).mem_centralCharacterSearch]
    exact ⟨by fin_cases i <;> decide,
      by
        simpa using ClassData.IsModularEigenrow.map (d := cyclicClassData 2)
          (Int.castRingHom (ZMod 3))
          (isModularEigenrow_cyclicGroupTwoCentralCharacterTable_int i)⟩
  · rw [(cyclicClassData 2).card_centralCharacterSearch_of_isGoodDixonPrime
      isGoodDixonPrime_cyclicGroup_two_three,
      card_cyclicGroupTwoModularCentralRows, numClasses_cyclicClassData]

/-- **Signed least representatives modulo `3` recover every entry of the integral
central-character table.** -/
theorem cyclicGroupTwo_valMinAbs_centralCharacterTable
    (i j : CyclicGroupTwoClassIndex) :
    ((cyclicGroupTwoCentralCharacterTable i j : ZMod 3)).valMinAbs =
      cyclicGroupTwoCentralCharacterTable i j := by
  rw [cyclicGroupTwoCentralCharacterTable_apply]
  apply ZMod.valMinAbs_intCast_of_two_mul_natAbs_lt
  fin_cases i <;> fin_cases j <;> decide

/-- The signed integral rows obtained from the modular search. -/
def cyclicGroupTwoLiftedCentralRows :
    Finset (CyclicGroupTwoClassIndex → ℤ) :=
  ((cyclicClassData 2).centralCharacterSearch (F := ZMod 3)).image
    fun a j => (a j).valMinAbs

/-- **The rational lift of the modular search is exactly the displayed integral
central-character table, up to row order.** -/
theorem cyclicGroupTwo_liftedCentralRows :
    cyclicGroupTwoLiftedCentralRows =
      Finset.univ.image fun i => cyclicGroupTwoCentralCharacterTable i := by
  rw [cyclicGroupTwoLiftedCentralRows, cyclicGroupTwo_centralCharacterSearch,
    cyclicGroupTwoModularCentralRows, Finset.image_image]
  apply Finset.image_congr
  intro i _
  funext j
  exact cyclicGroupTwo_valMinAbs_centralCharacterTable i j

/-- A lifted row occurs exactly when it is a row of the displayed integral table. -/
@[simp]
theorem mem_cyclicGroupTwoLiftedCentralRows_iff
    {a : CyclicGroupTwoClassIndex → ℤ} :
    a ∈ cyclicGroupTwoLiftedCentralRows ↔
      ∃ i, cyclicGroupTwoCentralCharacterTable i = a := by
  rw [cyclicGroupTwo_liftedCentralRows]
  simp

/-- The degrees attached to the two central-character rows. -/
def cyclicGroupTwoCharacterDegrees : CyclicGroupTwoClassIndex → ℕ :=
  fun _ => 1

/-- Both displayed degrees are `1`. -/
@[simp]
theorem cyclicGroupTwoCharacterDegrees_eq_one (i : CyclicGroupTwoClassIndex) :
    cyclicGroupTwoCharacterDegrees i = 1 := by
  rfl

/-- **The integral character table produced by the rational Dixon computation for the cyclic
group of order two.** -/
def cyclicGroupTwoCharacterTable :
    Matrix CyclicGroupTwoClassIndex CyclicGroupTwoClassIndex ℤ :=
  cyclicGroupTwoCentralCharacterTable

/-- The entries of the ordinary integral character table. -/
theorem cyclicGroupTwoCharacterTable_apply (i j : CyclicGroupTwoClassIndex) :
    cyclicGroupTwoCharacterTable i j =
      !![1,  1;
         1, -1] i j := by
  exact cyclicGroupTwoCentralCharacterTable_apply i j

/-- The displayed ordinary and central-character tables agree entrywise for `C₂`. -/
@[simp]
theorem cyclicGroupTwoCharacterTable_eq_centralCharacterTable :
    cyclicGroupTwoCharacterTable = cyclicGroupTwoCentralCharacterTable := by
  rfl

/-- **Division-free conversion from central characters to ordinary characters.** For every row
`i` and class `j`, `degree i * omega i j = |K_j| * chi i j`. -/
theorem cyclicGroupTwo_degree_mul_centralCharacterTable
    (i j : CyclicGroupTwoClassIndex) :
    (cyclicGroupTwoCharacterDegrees i : ℤ) *
        cyclicGroupTwoCentralCharacterTable i j =
      ((cyclicClassData 2).classFinset j).card * cyclicGroupTwoCharacterTable i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The displayed degrees are positive and divide the order of the cyclic group. -/
theorem cyclicGroupTwo_characterDegrees_pos_and_dvd (i : CyclicGroupTwoClassIndex) :
    0 < cyclicGroupTwoCharacterDegrees i ∧
      cyclicGroupTwoCharacterDegrees i ∣ Nat.card (Multiplicative (ZMod 2)) := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  fin_cases i <;> decide

/-- The squares of the displayed degrees sum to the group order. -/
theorem cyclicGroupTwo_sum_characterDegrees_sq :
    ∑ i, cyclicGroupTwoCharacterDegrees i ^ 2 = Nat.card (Multiplicative (ZMod 2)) := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  decide

/-- The displayed ordinary character rows satisfy the class-size weighted orthogonality
relations. -/
theorem cyclicGroupTwo_characterTable_orthogonal (i j : CyclicGroupTwoClassIndex) :
    ∑ k, ((cyclicClassData 2).classFinset k).card *
        cyclicGroupTwoCharacterTable i k * cyclicGroupTwoCharacterTable j k =
      if i = j then Nat.card (Multiplicative (ZMod 2)) else 0 := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  fin_cases i <;> fin_cases j <;> decide

end TauCeti
