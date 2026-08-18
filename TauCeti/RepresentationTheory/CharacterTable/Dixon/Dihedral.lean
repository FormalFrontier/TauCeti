/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.CentralCharacterCount
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Dihedral

/-!
# Dixon prime data for the small dihedral groups

The Burnside--Dixon--Schneider algorithm is meant to run, so the groups it is run on are handed a
prime by hand rather than by the existence theorem `TauCeti.exists_isGoodDixonPrime`, whose witness
is noncomputable. This file certifies the two worked examples: `5` for the dihedral group of order
`8`, with `2` as its primitive fourth root of unity, and `7` for the dihedral group of order `6`,
with `3` as its primitive sixth root.

## Main definitions

* `TauCeti.dihedralGroupFourDixonPrimeData`: Dixon prime data for `DihedralGroup 4`.
* `TauCeti.dihedralGroupThreeDixonPrimeData`: Dixon prime data for `DihedralGroup 3`.
* `TauCeti.card_centralCharacterSearch_dihedralClassData_four`: the modular central-character
  search for the dihedral group of order `8` returns exactly five rows at the certified prime `5`.

## References

* The roadmap `RepresentationTheory/CharacterTheory`, Layer 6, "Certified Dixon prime data".
-/

public section

namespace TauCeti

/-- **`5` is a good Dixon prime for the dihedral group of order `8`**, the worked example of the
character-table algorithm: `5 ∤ 8`, the exponent `4` divides `4 = 5 - 1`, and
`2⌊√8⌋ = 4 < 5`. -/
theorem isGoodDixonPrime_dihedralGroup_four_five : IsGoodDixonPrime (DihedralGroup 4) 5 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [DihedralGroup.nat_card]; decide
  · rw [exponent_dihedralGroup_four]
  · rw [DihedralGroup.nat_card]
    have h : Nat.sqrt (2 * 4) < 3 := Nat.sqrt_lt.2 (by norm_num)
    omega

/-- Dixon prime data for the dihedral group of order `8`: the prime `5`, with `2` as the primitive
fourth root of unity modulo `5`. -/
@[expose] def dihedralGroupFourDixonPrimeData : DixonPrimeData (DihedralGroup 4) where
  p := 5
  root := 2
  isGoodDixonPrime := isGoodDixonPrime_dihedralGroup_four_five
  isPrimitiveRoot_root := by
    rw [exponent_dihedralGroup_four]
    exact .mk_of_lt 2 (by norm_num) (by decide) fun l hl0 hl4 => by interval_cases l <;> decide

/-- The prime carried by `TauCeti.dihedralGroupFourDixonPrimeData` is `5`. -/
@[simp]
theorem dihedralGroupFourDixonPrimeData_p : dihedralGroupFourDixonPrimeData.p = 5 := rfl

/-- The primitive fourth root of unity carried by `TauCeti.dihedralGroupFourDixonPrimeData` is
`2`. -/
@[simp]
theorem dihedralGroupFourDixonPrimeData_root : dihedralGroupFourDixonPrimeData.root = 2 := rfl

/-- **`7` is a good Dixon prime for the dihedral group of order `6`**: `7 ∤ 6`, the exponent `6`
divides `6 = 7 - 1`, and `2⌊√6⌋ = 4 < 7`. -/
theorem isGoodDixonPrime_dihedralGroup_three_seven : IsGoodDixonPrime (DihedralGroup 3) 7 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [DihedralGroup.nat_card]; decide
  · rw [exponent_dihedralGroup_three]
  · rw [DihedralGroup.nat_card]
    have h : Nat.sqrt (2 * 3) < 3 := Nat.sqrt_lt.2 (by norm_num)
    omega

/-- Dixon prime data for the dihedral group of order `6`: the prime `7`, with `3` as the primitive
sixth root of unity modulo `7`. -/
@[expose] def dihedralGroupThreeDixonPrimeData : DixonPrimeData (DihedralGroup 3) where
  p := 7
  root := 3
  isGoodDixonPrime := isGoodDixonPrime_dihedralGroup_three_seven
  isPrimitiveRoot_root := by
    rw [exponent_dihedralGroup_three]
    exact .mk_of_lt 3 (by norm_num) (by decide) fun l hl0 hl6 => by interval_cases l <;> decide

/-- The prime carried by `TauCeti.dihedralGroupThreeDixonPrimeData` is `7`. -/
@[simp]
theorem dihedralGroupThreeDixonPrimeData_p : dihedralGroupThreeDixonPrimeData.p = 7 := rfl

/-- The primitive sixth root of unity carried by `TauCeti.dihedralGroupThreeDixonPrimeData` is
`3`. -/
@[simp]
theorem dihedralGroupThreeDixonPrimeData_root : dihedralGroupThreeDixonPrimeData.root = 3 := rfl

/-! ### The central-character search acceptance test -/

/-- **The modular central-character search for the dihedral group of order `8` returns exactly five
rows**, one for each of its five conjugacy classes, at the certified good Dixon prime `5`.

Since the rows of the search are exactly the normalized common left eigenrows
(`TauCeti.ClassData.mem_centralCharacterSearch`), this says that the five characters of
`Z(ZMod 5 [D₄])` are all found: none of them is lost to the reduction modulo `5`, and no spurious
row is returned. It is the acceptance test the roadmap asks for at this stage of the algorithm.

The statement supplies `Fact (Nat.Prime 5)` locally because `ZMod 5` is a field only in the
presence of that instance. -/
theorem card_centralCharacterSearch_dihedralClassData_four :
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    ((dihedralClassData 4).centralCharacterSearch (F := ZMod 5)).card = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [(dihedralClassData 4).card_centralCharacterSearch_of_isGoodDixonPrime
    isGoodDixonPrime_dihedralGroup_four_five, numClasses_dihedralClassData_four]

end TauCeti
