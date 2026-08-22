/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.ValMinAbs
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Quaternion
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Quaternion

/-!
# The rational Dixon computation for the quaternion group of order eight

This file runs the rational stage of the Dixon--Schneider character-table algorithm for
`QuaternionGroup 2`.  Its five numbered conjugacy classes have sizes `[1, 1, 2, 2, 2]`.
Reducing modulo the certified good prime `5`, the simultaneous eigenrow search returns exactly
the reductions of the five rows displayed in `TauCeti.quaternionGroupTwoCentralCharacterTable`.

Each displayed row is checked against the computed structure constants, while the good-prime
count theorem supplies completeness of the modular search.  Signed least representatives modulo
`5` then recover the integral central-character rows.  Degree recovery converts these to the
ordinary table, which is the same matrix as the table of `DihedralGroup 4`, the classical example
of nonisomorphic groups with equal character tables.

## Main definitions

* `TauCeti.quaternionGroupTwoCentralCharacterTable`: the five integral central-character rows.
* `TauCeti.quaternionGroupTwoModularCentralRows`: their reductions modulo `5`.
* `TauCeti.quaternionGroupTwoCharacterTable`: the resulting ordinary integral character table.

## Main results

* `TauCeti.quaternionGroupTwo_centralCharacterSearch`: the modular search returns exactly the
  displayed reductions.
* `TauCeti.quaternionGroupTwo_valMinAbs_centralCharacterTable`: signed least representatives lift
  every modular entry to the displayed integer.
* `TauCeti.quaternionGroupTwo_degree_mul_centralCharacterTable`: the division-free conversion to
  the ordinary character table.

## References

This closes the `Q₈ = QuaternionGroup 2` part of "Rational tables (first executable milestone)"
in Layer 6 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601--606.
-/

public section

namespace TauCeti

open Matrix

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The numbered conjugacy classes of the quaternion group of order eight. -/
abbrev QuaternionGroupTwoClassIndex := Fin (quaternionClassData 2).numClasses

/-- **The integral central-character table of the quaternion group of order eight.** Columns
follow `TauCeti.quaternionClassData 2`: the identity, the central element of order two, and the
three classes consisting of a pair of quaternion units. -/
def quaternionGroupTwoCentralCharacterTable :
    Matrix QuaternionGroupTwoClassIndex QuaternionGroupTwoClassIndex ℤ :=
  !![1,  1,  2,  2,  2;
     1,  1,  2, -2, -2;
     1,  1, -2,  2, -2;
     1,  1, -2, -2,  2;
     1, -1,  0,  0,  0]

/-- The quaternion and dihedral groups of order eight have the same central-character matrix in
their respective class numberings. -/
@[simp]
theorem quaternionGroupTwoCentralCharacterTable_apply
    (i j : QuaternionGroupTwoClassIndex) :
    quaternionGroupTwoCentralCharacterTable i j =
      !![1,  1,  2,  2,  2;
         1,  1,  2, -2, -2;
         1,  1, -2,  2, -2;
         1,  1, -2, -2,  2;
         1, -1,  0,  0,  0] i j := by
  rfl

/-- The five central-character rows reduced modulo the certified Dixon prime `5`. -/
def quaternionGroupTwoModularCentralRows :
    Finset (QuaternionGroupTwoClassIndex → ZMod 5) :=
  Finset.univ.image fun i j => (quaternionGroupTwoCentralCharacterTable i j : ZMod 5)

/-- A modular row is displayed exactly when it is the reduction of a row of the integral table. -/
@[simp]
theorem mem_quaternionGroupTwoModularCentralRows_iff
    {a : QuaternionGroupTwoClassIndex → ZMod 5} :
    a ∈ quaternionGroupTwoModularCentralRows ↔
      ∃ i, (fun j => (quaternionGroupTwoCentralCharacterTable i j : ZMod 5)) = a := by
  simp [quaternionGroupTwoModularCentralRows]

/-- Each integral row is a simultaneous eigenrow of the integral class-multiplication matrices. -/
theorem isModularEigenrow_quaternionGroupTwoCentralCharacterTable_int
    (i : QuaternionGroupTwoClassIndex) :
    (quaternionClassData 2).IsModularEigenrow
      (fun j => quaternionGroupTwoCentralCharacterTable i j) := by
  rw [(quaternionClassData 2).isModularEigenrow_iff]
  simp only [quaternionGroupTwoCentralCharacterTable_apply]
  fin_cases i <;> decide

/-- Reindexing an integral row by the actual conjugacy classes gives a class-algebra eigenrow. -/
theorem isClassEigenrow_quaternionGroupTwoCentralCharacterTable
    (i : QuaternionGroupTwoClassIndex) :
    IsClassEigenrow ((quaternionClassData 2).reindexModularRow
      fun j => quaternionGroupTwoCentralCharacterTable i j) :=
  ((quaternionClassData 2).isModularEigenrow_iff_isClassEigenrow _).mp
    (isModularEigenrow_quaternionGroupTwoCentralCharacterTable_int i)

/-- Every displayed reduction is a simultaneous eigenrow over `ZMod 5`. -/
theorem isModularEigenrow_quaternionGroupTwoCentralCharacterTable_zmod
    (i : QuaternionGroupTwoClassIndex) :
    (quaternionClassData 2).IsModularEigenrow
      (fun j => (quaternionGroupTwoCentralCharacterTable i j : ZMod 5)) := by
  rw [(quaternionClassData 2).isModularEigenrow_iff]
  simp only [quaternionGroupTwoCentralCharacterTable_apply]
  fin_cases i <;> decide

/-- The explicit set of modular rows has five elements. -/
@[simp]
theorem card_quaternionGroupTwoModularCentralRows :
    quaternionGroupTwoModularCentralRows.card = 5 := by
  decide

/-- **The executable modular central-character search for `QuaternionGroup 2` returns precisely
the five displayed reductions.** -/
theorem quaternionGroupTwo_centralCharacterSearch :
    (quaternionClassData 2).centralCharacterSearch (F := ZMod 5) =
      quaternionGroupTwoModularCentralRows := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · rw [quaternionGroupTwoModularCentralRows, Finset.image_subset_iff]
    intro i _
    rw [(quaternionClassData 2).mem_centralCharacterSearch]
    exact ⟨by fin_cases i <;> decide,
      isModularEigenrow_quaternionGroupTwoCentralCharacterTable_zmod i⟩
  · rw [(quaternionClassData 2).card_centralCharacterSearch_of_isGoodDixonPrime
      isGoodDixonPrime_quaternionGroup_two_five,
      card_quaternionGroupTwoModularCentralRows, numClasses_quaternionClassData_two]

/-- **Signed least representatives modulo `5` recover the integral central-character table.** -/
theorem quaternionGroupTwo_valMinAbs_centralCharacterTable
    (i j : QuaternionGroupTwoClassIndex) :
    ((quaternionGroupTwoCentralCharacterTable i j : ZMod 5)).valMinAbs =
      quaternionGroupTwoCentralCharacterTable i j := by
  rw [quaternionGroupTwoCentralCharacterTable_apply]
  apply ZMod.valMinAbs_intCast_of_two_mul_natAbs_lt
  fin_cases i <;> fin_cases j <;> decide

/-- The signed integral rows obtained from the output of the modular search. -/
def quaternionGroupTwoLiftedCentralRows :
    Finset (QuaternionGroupTwoClassIndex → ℤ) :=
  ((quaternionClassData 2).centralCharacterSearch (F := ZMod 5)).image
    fun a j => (a j).valMinAbs

/-- **The rational lift is exactly the displayed integral central-character table, up to row
order.** -/
theorem quaternionGroupTwo_liftedCentralRows :
    quaternionGroupTwoLiftedCentralRows =
      Finset.univ.image fun i => quaternionGroupTwoCentralCharacterTable i := by
  rw [quaternionGroupTwoLiftedCentralRows, quaternionGroupTwo_centralCharacterSearch,
    quaternionGroupTwoModularCentralRows, Finset.image_image]
  apply Finset.image_congr
  intro i _
  funext j
  exact quaternionGroupTwo_valMinAbs_centralCharacterTable i j

/-- A lifted row occurs exactly when it is a row of the displayed integral table. -/
@[simp]
theorem mem_quaternionGroupTwoLiftedCentralRows_iff
    {a : QuaternionGroupTwoClassIndex → ℤ} :
    a ∈ quaternionGroupTwoLiftedCentralRows ↔
      ∃ i, quaternionGroupTwoCentralCharacterTable i = a := by
  rw [quaternionGroupTwo_liftedCentralRows]
  simp

/-- The degrees attached to the five central-character rows. -/
def quaternionGroupTwoCharacterDegrees : QuaternionGroupTwoClassIndex → ℕ :=
  ![1, 1, 1, 1, 2]

/-- The quaternion and dihedral groups of order eight have the same degree vector. -/
@[simp]
theorem quaternionGroupTwoCharacterDegrees_apply (i : QuaternionGroupTwoClassIndex) :
    quaternionGroupTwoCharacterDegrees i = ![1, 1, 1, 1, 2] i := by
  rfl

/-- **The integral character table produced by the rational Dixon computation for the quaternion
group of order eight.** -/
def quaternionGroupTwoCharacterTable :
    Matrix QuaternionGroupTwoClassIndex QuaternionGroupTwoClassIndex ℤ :=
  !![1,  1,  1,  1,  1;
     1,  1,  1, -1, -1;
     1,  1, -1,  1, -1;
     1,  1, -1, -1,  1;
     2, -2,  0,  0,  0]

/-- **The quaternion and dihedral groups of order eight have the same ordinary character matrix**
in their respective class numberings. -/
@[simp]
theorem quaternionGroupTwoCharacterTable_apply (i j : QuaternionGroupTwoClassIndex) :
    quaternionGroupTwoCharacterTable i j =
      !![1,  1,  1,  1,  1;
         1,  1,  1, -1, -1;
         1,  1, -1,  1, -1;
         1,  1, -1, -1,  1;
         2, -2,  0,  0,  0] i j := by
  rfl

/-- **Division-free conversion from central characters to ordinary characters.** For every row
`i` and numbered conjugacy class `j`, `degree i * omega i j = |K_j| * chi i j`. -/
theorem quaternionGroupTwo_degree_mul_centralCharacterTable
    (i j : QuaternionGroupTwoClassIndex) :
    (quaternionGroupTwoCharacterDegrees i : ℤ) *
        quaternionGroupTwoCentralCharacterTable i j =
      ((quaternionClassData 2).classFinset j).card * quaternionGroupTwoCharacterTable i j := by
  simp only [quaternionGroupTwoCharacterDegrees_apply,
    quaternionGroupTwoCentralCharacterTable_apply, quaternionGroupTwoCharacterTable_apply]
  fin_cases i <;> fin_cases j <;> decide

/-- The displayed degrees are positive and divide the order of `QuaternionGroup 2`. -/
theorem quaternionGroupTwo_characterDegrees_pos_and_dvd (i : QuaternionGroupTwoClassIndex) :
    0 < quaternionGroupTwoCharacterDegrees i ∧
      quaternionGroupTwoCharacterDegrees i ∣ Nat.card (QuaternionGroup 2) := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  simp only [quaternionGroupTwoCharacterDegrees_apply]
  fin_cases i <;> decide

/-- The squares of the displayed degrees sum to the group order. -/
theorem quaternionGroupTwo_sum_characterDegrees_sq :
    ∑ i, quaternionGroupTwoCharacterDegrees i ^ 2 = Nat.card (QuaternionGroup 2) := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  simp only [quaternionGroupTwoCharacterDegrees_apply]
  decide

/-- The ordinary character rows satisfy the class-size weighted orthogonality relations. -/
theorem quaternionGroupTwo_characterTable_orthogonal (i j : QuaternionGroupTwoClassIndex) :
    ∑ k, ((quaternionClassData 2).classFinset k).card *
        quaternionGroupTwoCharacterTable i k * quaternionGroupTwoCharacterTable j k =
      if i = j then Nat.card (QuaternionGroup 2) else 0 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  simp only [quaternionGroupTwoCharacterTable_apply]
  fin_cases i <;> fin_cases j <;> decide

end TauCeti
