/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Dihedral
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Dihedral
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.Basic

/-!
# The rational Dixon computation for the dihedral group of order six

This file runs the rational stage of the Dixon--Schneider character-table algorithm for
`DihedralGroup 3`, which is isomorphic to the symmetric group on three letters. The class data are
numbered by `TauCeti.dihedralClassData 3`; its three classes have sizes `1`, `2`, and `3`,
represented by the identity, a nontrivial rotation, and a reflection. Their class count, sizes, and
structure constants are evaluated in
`TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Dihedral`.

The simultaneous eigenvector search is carried out over `ZMod 7`, using
`TauCeti.isGoodDixonPrime_dihedralGroup_three_seven`; the corresponding prime and certificate are
bundled by `TauCeti.dihedralGroupThreeDixonPrimeData`. Its three output rows are proved to be
exactly the reductions of the displayed integral central-character table. Applying `ZMod.valMinAbs`
recovers those rows over the integers. The displayed degrees and ordinary table are checked against
this output by the degree identity, degree-square sum, and weighted row orthogonality. This file
does not identify the displayed rows with `TauCeti.characterTable` or prove
`TauCeti.IsCharacterTableSpec`.

Completeness is proved without evaluating the whole search: the displayed rows satisfy the
class-algebra equations, and the good-prime structure theorem says that the search has exactly
three outputs.

## Main definitions

* `TauCeti.dihedralGroupThreeCentralCharacterTable`: the three integral central-character rows.
* `TauCeti.dihedralGroupThreeCharacterDegrees`: the displayed degrees `1`, `1`, and `2`.
* `TauCeti.dihedralGroupThreeCharacterTable`: the displayed ordinary integral table.

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

/-- The numbered conjugacy classes of the dihedral group of order six. -/
abbrev DihedralGroupThreeClassIndex := Fin (dihedralClassData 3).numClasses

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

/-- Every displayed integral row satisfies the numbered class-algebra eigenrow equations. In
particular, its modular reduction below comes from a characteristic-zero central character rather
than being an eigenrow created by reduction. -/
theorem isModularEigenrow_dihedralGroupThreeCentralCharacterTable_int
    (i : DihedralGroupThreeClassIndex) :
    (dihedralClassData 3).IsModularEigenrow
      (fun j => dihedralGroupThreeCentralCharacterTable i j) := by
  rw [(dihedralClassData 3).isModularEigenrow_iff]
  fin_cases i <;> decide

/-- Every displayed reduction is a simultaneous eigenrow of the reduced class-multiplication
matrices. -/
theorem isModularEigenrow_dihedralGroupThreeCentralCharacterTable_zmod
    (i : DihedralGroupThreeClassIndex) :
    (dihedralClassData 3).IsModularEigenrow
      (fun j => (dihedralGroupThreeCentralCharacterTable i j :
        ZMod dihedralGroupThreeDixonPrimeData.p)) :=
  (isModularEigenrow_dihedralGroupThreeCentralCharacterTable_int i).map
    (Int.castRingHom (ZMod dihedralGroupThreeDixonPrimeData.p))

/-- The explicit set of modular rows has three elements. -/
@[simp]
theorem card_dihedralGroupThreeModularCentralRows :
    ((dihedralClassData 3).rowsOfMap (fun x : ℤ => (x : ZMod 7))
      dihedralGroupThreeCentralCharacterTable).card = (dihedralClassData 3).numClasses := by
  decide

/-- **The executable modular central-character search returns precisely the three reductions in
`TauCeti.dihedralGroupThreeCentralCharacterTable`.** -/
theorem dihedralGroupThree_centralCharacterSearch :
    (dihedralClassData 3).centralCharacterSearch
        (F := ZMod dihedralGroupThreeDixonPrimeData.p) =
      (dihedralClassData 3).rowsOfMap
        (fun x : ℤ => (x : ZMod dihedralGroupThreeDixonPrimeData.p))
        dihedralGroupThreeCentralCharacterTable :=
  (dihedralClassData 3).centralCharacterSearch_eq_rowsOfMap_of_isGoodDixonPrime
    dihedralGroupThreeDixonPrimeData.isGoodDixonPrime
    (fun x : ℤ => (x : ZMod dihedralGroupThreeDixonPrimeData.p))
    dihedralGroupThreeCentralCharacterTable
    (by intro i; fin_cases i <;> decide)
    isModularEigenrow_dihedralGroupThreeCentralCharacterTable_zmod
    (by
      have hcard := card_dihedralGroupThreeModularCentralRows
      rw [← dihedralGroupThreeDixonPrimeData_p] at hcard
      exact hcard)

/-- **The rational lift of the modular search is exactly the displayed integral
central-character table, up to row order.** -/
theorem dihedralGroupThree_liftedCentralRows :
    (dihedralClassData 3).liftedCentralRows dihedralGroupThreeDixonPrimeData.p =
      Finset.univ.image fun i => dihedralGroupThreeCentralCharacterTable i := by
  apply (dihedralClassData 3).liftedCentralRows_eq_image_of_centralCharacterSearch_eq
    dihedralGroupThreeCentralCharacterTable dihedralGroupThree_centralCharacterSearch
  intro i j
  rw [dihedralGroupThreeDixonPrimeData_p, dihedralGroupThreeCentralCharacterTable_apply]
  fin_cases i <;> fin_cases j <;> decide

/-- The displayed degrees attached to the three central-character rows. -/
def dihedralGroupThreeCharacterDegrees : DihedralGroupThreeClassIndex → ℕ :=
  ![1, 1, 2]

/-- The degrees attached to the central-character rows, entrywise. -/
@[simp]
theorem dihedralGroupThreeCharacterDegrees_apply (i : DihedralGroupThreeClassIndex) :
    dihedralGroupThreeCharacterDegrees i = ![1, 1, 2] i := by
  rfl

/-- **The displayed integral ordinary table for the dihedral group of order six.** Its consistency
with the lifted central-character rows is checked below; this definition is not itself derived from
the search or identified here with `TauCeti.characterTable`. -/
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

/-- **The displayed central-character and ordinary tables satisfy the division-free conversion
identity.** For every row `i` and class `j`, `degree i * omega i j = |K_j| * chi i j`. -/
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
