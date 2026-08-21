/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ZMod.ValMinAbs
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Dihedral
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Dihedral

/-!
# The rational Dixon computation for the dihedral group of order six

This file runs the rational stage of the Dixon--Schneider character-table algorithm for
`DihedralGroup 3`, which is isomorphic to the symmetric group on three letters. The class data are
numbered by `TauCeti.dihedralClassData 3`; its three classes have sizes `1`, `2`, and `3`,
represented by the identity, a nontrivial rotation, and a reflection.

The simultaneous eigenvector search is carried out over `ZMod 7`, using the certified Dixon prime
`TauCeti.dihedralGroupThreeDixonPrimeData`. Its three output rows are proved to be exactly the
reductions of the displayed integral central-character table. Applying `ZMod.valMinAbs` recovers
those rows over the integers, and the central-to-ordinary conversion gives the usual character
table with degrees `1`, `1`, and `2`.

Completeness is proved without evaluating the whole search: the displayed rows satisfy the
class-algebra equations, and the good-prime structure theorem says that the search has exactly
three outputs.

## Main definitions

* `TauCeti.dihedralGroupThreeCentralCharacterTable`: the three integral central-character rows.
* `TauCeti.dihedralGroupThreeModularCentralRows`: their reductions modulo `7`.
* `TauCeti.dihedralGroupThreeCharacterTable`: the resulting ordinary integral character table.

## Main results

* `TauCeti.dihedralGroupThree_centralCharacterSearch`: the modular search returns exactly the
  displayed reductions.
* `TauCeti.dihedralGroupThree_liftedCentralRows`: signed least representatives recover exactly the
  integral central-character rows.
* `TauCeti.dihedralGroupThree_degree_mul_centralCharacterTable`: the division-free conversion to
  the ordinary character table.

## References

This implements the `S₃ ≅ DihedralGroup 3` computation in "Rational tables (first executable
milestone)" in Layer 6 of the [character theory roadmap][roadmap]. Connecting the exact output to
the general table checker remains part of the assembled solver target.

[roadmap]: https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601--606.
-/

public section

namespace TauCeti

open Matrix

local instance dihedralGroupThreeFactPrime : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The numbered conjugacy classes of the dihedral group of order six. -/
abbrev DihedralGroupThreeClassIndex := Fin (dihedralClassData 3).numClasses

/-- **The dihedral group of order six has three conjugacy classes.** -/
@[simp]
theorem numClasses_dihedralClassData_three : (dihedralClassData 3).numClasses = 3 := by
  decide

/-- **The numbered conjugacy classes have sizes `1`, `2`, and `3`.** They are the identity,
the two nontrivial rotations, and the three reflections. -/
theorem card_classFinset_dihedralClassData_three :
    (dihedralClassData 3).classes.map Finset.card = [1, 2, 3] := by
  decide

/-- **The structure constants of the dihedral group of order six.** This is the complete integral
input to its Dixon--Schneider computation, evaluated by the kernel. -/
theorem structureConstantTable_dihedralClassData_three :
    (dihedralClassData 3).structureConstantTable =
      [[[1, 0, 0], [0, 1, 0], [0, 0, 1]],
       [[0, 1, 0], [2, 1, 0], [0, 0, 2]],
       [[0, 0, 1], [0, 0, 2], [3, 3, 0]]] := by
  decide

/-- **The integral central-character table of the dihedral group of order six.** Columns follow
the class numbering above: identity, nontrivial rotations, and reflections. -/
def dihedralGroupThreeCentralCharacterTable :
    Matrix DihedralGroupThreeClassIndex DihedralGroupThreeClassIndex ℤ :=
  !![1,  2,  3;
     1,  2, -3;
     1, -1,  0]

/-- The entries of the integral central-character table. -/
@[simp]
theorem dihedralGroupThreeCentralCharacterTable_apply
    (i j : DihedralGroupThreeClassIndex) :
    dihedralGroupThreeCentralCharacterTable i j =
      !![1,  2,  3;
         1,  2, -3;
         1, -1,  0] i j := by
  rfl

/-- The displayed central-character rows reduced modulo the certified Dixon prime `7`. -/
def dihedralGroupThreeModularCentralRows :
    Finset (DihedralGroupThreeClassIndex → ZMod 7) :=
  Finset.univ.image fun i j => (dihedralGroupThreeCentralCharacterTable i j : ZMod 7)

/-- A modular row is displayed exactly when it is the reduction of a row of the integral table. -/
@[simp]
theorem mem_dihedralGroupThreeModularCentralRows_iff
    {a : DihedralGroupThreeClassIndex → ZMod 7} :
    a ∈ dihedralGroupThreeModularCentralRows ↔
      ∃ i, (fun j => (dihedralGroupThreeCentralCharacterTable i j : ZMod 7)) = a := by
  simp [dihedralGroupThreeModularCentralRows]

/-- Every displayed integral row satisfies the numbered class-algebra eigenrow equations. -/
theorem isModularEigenrow_dihedralGroupThreeCentralCharacterTable_int
    (i : DihedralGroupThreeClassIndex) :
    (dihedralClassData 3).IsModularEigenrow
      (fun j => dihedralGroupThreeCentralCharacterTable i j) := by
  rw [(dihedralClassData 3).isModularEigenrow_iff]
  fin_cases i <;> decide

/-- Reindexing a displayed integral row by the actual conjugacy classes gives a class-algebra
eigenrow. -/
theorem isClassEigenrow_dihedralGroupThreeCentralCharacterTable
    (i : DihedralGroupThreeClassIndex) :
    IsClassEigenrow ((dihedralClassData 3).reindexModularRow
      fun j => dihedralGroupThreeCentralCharacterTable i j) :=
  ((dihedralClassData 3).isModularEigenrow_iff_isClassEigenrow _).mp
    (isModularEigenrow_dihedralGroupThreeCentralCharacterTable_int i)

/-- Every displayed reduction is a simultaneous eigenrow of the reduced class-multiplication
matrices. -/
theorem isModularEigenrow_dihedralGroupThreeCentralCharacterTable_zmod
    (i : DihedralGroupThreeClassIndex) :
    (dihedralClassData 3).IsModularEigenrow
      (fun j => (dihedralGroupThreeCentralCharacterTable i j : ZMod 7)) := by
  rw [(dihedralClassData 3).isModularEigenrow_iff]
  fin_cases i <;> decide

/-- The explicit set of modular rows has three elements. -/
@[simp]
theorem card_dihedralGroupThreeModularCentralRows :
    dihedralGroupThreeModularCentralRows.card = 3 := by
  decide

/-- **The executable modular central-character search returns precisely the three reductions in
`TauCeti.dihedralGroupThreeCentralCharacterTable`.** -/
theorem dihedralGroupThree_centralCharacterSearch :
    (dihedralClassData 3).centralCharacterSearch (F := ZMod 7) =
      dihedralGroupThreeModularCentralRows := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · rw [dihedralGroupThreeModularCentralRows, Finset.image_subset_iff]
    intro i _
    rw [(dihedralClassData 3).mem_centralCharacterSearch]
    exact ⟨by fin_cases i <;> decide,
      isModularEigenrow_dihedralGroupThreeCentralCharacterTable_zmod i⟩
  · rw [(dihedralClassData 3).card_centralCharacterSearch_of_isGoodDixonPrime
      isGoodDixonPrime_dihedralGroup_three_seven,
      card_dihedralGroupThreeModularCentralRows, numClasses_dihedralClassData_three]

/-- **Signed least representatives modulo `7` recover every entry of the integral
central-character table.** -/
theorem dihedralGroupThree_valMinAbs_centralCharacterTable
    (i j : DihedralGroupThreeClassIndex) :
    ((dihedralGroupThreeCentralCharacterTable i j : ZMod 7)).valMinAbs =
      dihedralGroupThreeCentralCharacterTable i j := by
  rw [dihedralGroupThreeCentralCharacterTable_apply]
  apply ZMod.valMinAbs_intCast_of_two_mul_natAbs_lt
  fin_cases i <;> fin_cases j <;> decide

/-- The signed integral rows obtained from the modular search. -/
def dihedralGroupThreeLiftedCentralRows :
    Finset (DihedralGroupThreeClassIndex → ℤ) :=
  ((dihedralClassData 3).centralCharacterSearch (F := ZMod 7)).image
    fun a j => (a j).valMinAbs

/-- **The rational lift of the modular search is exactly the displayed integral
central-character table, up to row order.** -/
theorem dihedralGroupThree_liftedCentralRows :
    dihedralGroupThreeLiftedCentralRows =
      Finset.univ.image fun i => dihedralGroupThreeCentralCharacterTable i := by
  rw [dihedralGroupThreeLiftedCentralRows, dihedralGroupThree_centralCharacterSearch,
    dihedralGroupThreeModularCentralRows, Finset.image_image]
  apply Finset.image_congr
  intro i _
  funext j
  exact dihedralGroupThree_valMinAbs_centralCharacterTable i j

/-- A lifted row occurs exactly when it is a row of the displayed integral table. -/
@[simp]
theorem mem_dihedralGroupThreeLiftedCentralRows_iff
    {a : DihedralGroupThreeClassIndex → ℤ} :
    a ∈ dihedralGroupThreeLiftedCentralRows ↔
      ∃ i, dihedralGroupThreeCentralCharacterTable i = a := by
  rw [dihedralGroupThree_liftedCentralRows]
  simp

/-- The degrees attached to the three central-character rows. -/
def dihedralGroupThreeCharacterDegrees : DihedralGroupThreeClassIndex → ℕ :=
  ![1, 1, 2]

/-- The degrees attached to the central-character rows, entrywise. -/
@[simp]
theorem dihedralGroupThreeCharacterDegrees_apply (i : DihedralGroupThreeClassIndex) :
    dihedralGroupThreeCharacterDegrees i = ![1, 1, 2] i := by
  rfl

/-- **The integral character table produced by the rational Dixon computation for the dihedral
group of order six.** -/
def dihedralGroupThreeCharacterTable :
    Matrix DihedralGroupThreeClassIndex DihedralGroupThreeClassIndex ℤ :=
  !![1,  1,  1;
     1,  1, -1;
     2, -1,  0]

/-- The entries of the ordinary integral character table. -/
@[simp]
theorem dihedralGroupThreeCharacterTable_apply (i j : DihedralGroupThreeClassIndex) :
    dihedralGroupThreeCharacterTable i j =
      !![1,  1,  1;
         1,  1, -1;
         2, -1,  0] i j := by
  rfl

/-- **Division-free conversion from central characters to ordinary characters.** For every row
`i` and class `j`, `degree i * omega i j = |K_j| * chi i j`. -/
theorem dihedralGroupThree_degree_mul_centralCharacterTable
    (i j : DihedralGroupThreeClassIndex) :
    (dihedralGroupThreeCharacterDegrees i : ℤ) *
        dihedralGroupThreeCentralCharacterTable i j =
      ((dihedralClassData 3).classFinset j).card * dihedralGroupThreeCharacterTable i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The displayed degrees are positive and divide the order of `DihedralGroup 3`. -/
theorem dihedralGroupThree_characterDegrees_pos_and_dvd (i : DihedralGroupThreeClassIndex) :
    0 < dihedralGroupThreeCharacterDegrees i ∧
      dihedralGroupThreeCharacterDegrees i ∣ Nat.card (DihedralGroup 3) := by
  rw [DihedralGroup.nat_card]
  fin_cases i <;> decide

/-- The squares of the displayed degrees sum to the group order. -/
theorem dihedralGroupThree_sum_characterDegrees_sq :
    ∑ i, dihedralGroupThreeCharacterDegrees i ^ 2 = Nat.card (DihedralGroup 3) := by
  rw [DihedralGroup.nat_card]
  decide

/-- The displayed ordinary character rows satisfy the class-size weighted orthogonality
relations. -/
theorem dihedralGroupThree_characterTable_orthogonal (i j : DihedralGroupThreeClassIndex) :
    ∑ k, ((dihedralClassData 3).classFinset k).card *
        dihedralGroupThreeCharacterTable i k * dihedralGroupThreeCharacterTable j k =
      if i = j then Nat.card (DihedralGroup 3) else 0 := by
  rw [DihedralGroup.nat_card]
  fin_cases i <;> fin_cases j <;> decide

end TauCeti
