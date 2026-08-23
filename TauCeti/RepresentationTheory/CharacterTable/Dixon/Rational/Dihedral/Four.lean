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
# The rational Dixon computation for the dihedral group of order eight

This file runs the rational stage of the Dixon--Schneider character-table algorithm for
`DihedralGroup 4`.  The class data are numbered by `TauCeti.dihedralClassData 4`, whose class sizes
are `[1, 1, 2, 2, 2]`.  Reducing modulo the certified good prime `5`, the simultaneous eigenvector
search returns exactly the reductions of the five rows displayed in
`TauCeti.dihedralGroupFourCentralCharacterTable`.

Completeness is not established by evaluating the exponentially sized search.  Each displayed row
is verified against the structure constants, while
`TauCeti.ClassData.card_centralCharacterSearch_of_isGoodDixonPrime` proves that the search has only
five elements.  Equality follows from those two facts.  The entries lie strictly between
`-5 / 2` and `5 / 2`, so `ZMod.valMinAbs` reconstructs the displayed integral rows without any
cyclotomic ambiguity.  Dividing by the class sizes and multiplying by the degrees gives the usual
displayed ordinary table of the dihedral group of order eight. This file checks its degree identity,
degree-square sum, and weighted row orthogonality, but does not identify it with
`TauCeti.characterTable` or prove `TauCeti.IsCharacterTableSpec`.

## Main definitions

* `TauCeti.dihedralGroupFourCentralCharacterTable`: the five integral central-character rows.
* `TauCeti.dihedralGroupFourCharacterDegrees`: the displayed degrees `1`, `1`, `1`, `1`, and `2`.
* `TauCeti.dihedralGroupFourCharacterTable`: the displayed ordinary integral table.

## Main results

* `TauCeti.dihedralGroupFour_centralCharacterSearch`: the modular search returns exactly the five
  displayed reductions.
* `TauCeti.dihedralGroupFour_liftedCentralRows`: signed least representatives recover exactly the
  integral central-character rows.
* `TauCeti.dihedralGroupFour_degree_mul_centralCharacterTable`: the division-free conversion from
  the central-character table to the ordinary character table.

## References

This closes the `D₄ = DihedralGroup 4` part of “Rational tables (first executable milestone)” in
Layer 6 of the
[character theory roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/CharacterTheory/README.md).

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, J. Symbolic Comput. 9 (1990),
  601--606.
-/

public section

namespace TauCeti

open Matrix

/-- The numbered conjugacy classes of the dihedral group of order eight. -/
abbrev DihedralGroupFourClassIndex := Fin (dihedralClassData 4).numClasses

/-- **The integral central-character table of the dihedral group of order eight.** Columns follow
the numbering of `TauCeti.dihedralClassData 4`: identity, central rotation, one reflection class,
the rotations of order four, and the other reflection class. -/
def dihedralGroupFourCentralCharacterTable :
    Matrix DihedralGroupFourClassIndex DihedralGroupFourClassIndex ℤ :=
  !![1,  1,  2,  2,  2;
     1,  1,  2, -2, -2;
     1,  1, -2,  2, -2;
     1,  1, -2, -2,  2;
     1, -1,  0,  0,  0]

/-- The entries of the integral central-character table. -/
@[simp]
theorem dihedralGroupFourCentralCharacterTable_apply (i j : DihedralGroupFourClassIndex) :
    dihedralGroupFourCentralCharacterTable i j =
      !![1,  1,  2,  2,  2;
         1,  1,  2, -2, -2;
         1,  1, -2,  2, -2;
         1,  1, -2, -2,  2;
         1, -1,  0,  0,  0] i j := by
  rfl

/-- Every displayed integral row is a simultaneous eigenrow of the integral class-multiplication
matrices.  In particular, the modular verification below is the reduction of an honest
characteristic-zero central character, rather than an eigenrow created by reduction. -/
theorem isModularEigenrow_dihedralGroupFourCentralCharacterTable_int
    (i : DihedralGroupFourClassIndex) :
    (dihedralClassData 4).IsModularEigenrow
      (fun j => dihedralGroupFourCentralCharacterTable i j) := by
  rw [(dihedralClassData 4).isModularEigenrow_iff]
  fin_cases i <;> decide

/-- Reindexing a displayed integral row by the actual conjugacy classes gives a class-algebra
eigenrow. -/
theorem isClassEigenrow_dihedralGroupFourCentralCharacterTable
    (i : DihedralGroupFourClassIndex) :
    IsClassEigenrow ((dihedralClassData 4).reindexModularRow
      fun j => dihedralGroupFourCentralCharacterTable i j) :=
  ((dihedralClassData 4).isModularEigenrow_iff_isClassEigenrow _).mp
    (isModularEigenrow_dihedralGroupFourCentralCharacterTable_int i)

/-- Every displayed reduction is a simultaneous eigenrow of the reduced class-multiplication
matrices. -/
theorem isModularEigenrow_dihedralGroupFourCentralCharacterTable_zmod
    (i : DihedralGroupFourClassIndex) :
    (dihedralClassData 4).IsModularEigenrow
      (fun j => (dihedralGroupFourCentralCharacterTable i j :
        ZMod dihedralGroupFourDixonPrimeData.p)) :=
  (isModularEigenrow_dihedralGroupFourCentralCharacterTable_int i).map
    (Int.castRingHom (ZMod dihedralGroupFourDixonPrimeData.p))

/-- The explicit set of modular rows has five elements. -/
@[simp]
theorem card_dihedralGroupFourModularCentralRows :
    ((dihedralClassData 4).modularCentralRows 5
      dihedralGroupFourCentralCharacterTable).card = (dihedralClassData 4).numClasses := by
  decide

/-- **The executable modular central-character search for `DihedralGroup 4` returns precisely the
five reductions in `TauCeti.dihedralGroupFourCentralCharacterTable`.** -/
theorem dihedralGroupFour_centralCharacterSearch :
    (dihedralClassData 4).centralCharacterSearch
        (F := ZMod dihedralGroupFourDixonPrimeData.p) =
      (dihedralClassData 4).modularCentralRows dihedralGroupFourDixonPrimeData.p
        dihedralGroupFourCentralCharacterTable :=
  (dihedralClassData 4).centralCharacterSearch_eq_modularCentralRows_of_isGoodDixonPrime
    dihedralGroupFourDixonPrimeData.isGoodDixonPrime dihedralGroupFourCentralCharacterTable
    (by intro i; fin_cases i <;> decide)
    isModularEigenrow_dihedralGroupFourCentralCharacterTable_zmod
    (by simpa only [dihedralGroupFourDixonPrimeData_p] using
      card_dihedralGroupFourModularCentralRows)

/-- **The rational lift of the modular search is exactly the displayed integral central-character
table, up to the irrelevant order of its rows.** -/
theorem dihedralGroupFour_liftedCentralRows :
    (dihedralClassData 4).liftedCentralRows dihedralGroupFourDixonPrimeData.p =
      Finset.univ.image fun i => dihedralGroupFourCentralCharacterTable i := by
  apply (dihedralClassData 4).liftedCentralRows_eq_image_of_centralCharacterSearch_eq
    dihedralGroupFourCentralCharacterTable dihedralGroupFour_centralCharacterSearch
  intro i j
  rw [dihedralGroupFourDixonPrimeData_p, dihedralGroupFourCentralCharacterTable_apply]
  fin_cases i <;> fin_cases j <;> decide

/-- The displayed degrees attached to the five central-character rows. -/
def dihedralGroupFourCharacterDegrees : DihedralGroupFourClassIndex → ℕ :=
  ![1, 1, 1, 1, 2]

/-- The degrees attached to the central-character rows, entrywise. -/
@[simp]
theorem dihedralGroupFourCharacterDegrees_apply (i : DihedralGroupFourClassIndex) :
    dihedralGroupFourCharacterDegrees i = ![1, 1, 1, 1, 2] i := by
  rfl

/-- **The displayed integral ordinary table for the dihedral group of order eight.** The columns
use the same class numbering as `TauCeti.dihedralGroupFourCentralCharacterTable`. Its consistency
with the lifted central-character rows is checked below; this definition is not itself derived from
the search or identified here with `TauCeti.characterTable`. -/
def dihedralGroupFourCharacterTable :
    Matrix DihedralGroupFourClassIndex DihedralGroupFourClassIndex ℤ :=
  !![1,  1,  1,  1,  1;
     1,  1,  1, -1, -1;
     1,  1, -1,  1, -1;
     1,  1, -1, -1,  1;
     2, -2,  0,  0,  0]

/-- The entries of the ordinary integral character table. -/
@[simp]
theorem dihedralGroupFourCharacterTable_apply (i j : DihedralGroupFourClassIndex) :
    dihedralGroupFourCharacterTable i j =
      !![1,  1,  1,  1,  1;
         1,  1,  1, -1, -1;
         1,  1, -1,  1, -1;
         1,  1, -1, -1,  1;
         2, -2,  0,  0,  0] i j := by
  rfl

/-- **The displayed central-character and ordinary tables satisfy the division-free conversion
identity.** For every row `i` and numbered conjugacy class `j`,
`degree i * omega i j = |K_j| * chi i j`. -/
theorem dihedralGroupFour_degree_mul_centralCharacterTable
    (i j : DihedralGroupFourClassIndex) :
    (dihedralGroupFourCharacterDegrees i : ℤ) *
        dihedralGroupFourCentralCharacterTable i j =
      ((dihedralClassData 4).classFinset j).card * dihedralGroupFourCharacterTable i j := by
  fin_cases i <;> fin_cases j <;> decide

/-- The displayed degrees are positive and divide the order of `DihedralGroup 4`. -/
theorem dihedralGroupFour_characterDegrees_pos_and_dvd (i : DihedralGroupFourClassIndex) :
    0 < dihedralGroupFourCharacterDegrees i ∧
      dihedralGroupFourCharacterDegrees i ∣ Nat.card (DihedralGroup 4) := by
  rw [DihedralGroup.nat_card]
  fin_cases i <;> decide

/-- The squares of the displayed degrees sum to the group order. -/
theorem dihedralGroupFour_sum_characterDegrees_sq :
    ∑ i, dihedralGroupFourCharacterDegrees i ^ 2 = Nat.card (DihedralGroup 4) := by
  rw [DihedralGroup.nat_card]
  decide

/-- The displayed ordinary character rows satisfy the class-size weighted orthogonality
relations. -/
theorem dihedralGroupFour_characterTable_orthogonal (i j : DihedralGroupFourClassIndex) :
    ∑ k, ((dihedralClassData 4).classFinset k).card *
        dihedralGroupFourCharacterTable i k * dihedralGroupFourCharacterTable j k =
      if i = j then Nat.card (DihedralGroup 4) else 0 := by
  rw [DihedralGroup.nat_card]
  fin_cases i <;> fin_cases j <;> decide

end TauCeti
