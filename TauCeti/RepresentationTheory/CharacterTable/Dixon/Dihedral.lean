/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Prime

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

## References

* The roadmap `RepresentationTheory/CharacterTheory`, Layer 6, "Certified Dixon prime data".
-/

public section

namespace TauCeti

/-- The dihedral group of order `8` has exponent `4`. -/
@[simp]
theorem exponent_dihedralGroup_four : Monoid.exponent (DihedralGroup 4) = 4 := by
  rw [DihedralGroup.exponent]
  decide

/-- **`5` is a good Dixon prime for the dihedral group of order `8`**, the worked example of the
character-table algorithm: `5 ∤ 8`, the exponent `4` divides `4 = 5 - 1`, and
`2⌊√8⌋ = 4 < 5`. -/
theorem isGoodDixonPrime_dihedralGroup_four : IsGoodDixonPrime (DihedralGroup 4) 5 := by
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
  isGoodDixonPrime := isGoodDixonPrime_dihedralGroup_four
  isPrimitiveRoot_root := by
    rw [exponent_dihedralGroup_four]
    have h : orderOf (2 : ZMod 5) = 4 :=
      orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide) fun q hq hq4 => by
        have h2 := hq.two_le
        have h4 := Nat.le_of_dvd (by norm_num) hq4
        interval_cases q <;> revert hq4 <;> decide
    exact h ▸ IsPrimitiveRoot.orderOf (2 : ZMod 5)

/-- The prime carried by `TauCeti.dihedralGroupFourDixonPrimeData` is `5`. -/
@[simp]
theorem dihedralGroupFourDixonPrimeData_p : dihedralGroupFourDixonPrimeData.p = 5 := rfl

/-- The primitive fourth root of unity carried by `TauCeti.dihedralGroupFourDixonPrimeData` is
`2`. -/
@[simp]
theorem dihedralGroupFourDixonPrimeData_root : dihedralGroupFourDixonPrimeData.root = 2 := rfl

/-- The dihedral group of order `6`, the symmetric group on three letters, has exponent `6`. -/
@[simp]
theorem exponent_dihedralGroup_three : Monoid.exponent (DihedralGroup 3) = 6 := by
  rw [DihedralGroup.exponent]
  decide

/-- **`7` is a good Dixon prime for the dihedral group of order `6`**: `7 ∤ 6`, the exponent `6`
divides `6 = 7 - 1`, and `2⌊√6⌋ = 4 < 7`. -/
theorem isGoodDixonPrime_dihedralGroup_three : IsGoodDixonPrime (DihedralGroup 3) 7 := by
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
  isGoodDixonPrime := isGoodDixonPrime_dihedralGroup_three
  isPrimitiveRoot_root := by
    rw [exponent_dihedralGroup_three]
    have h : orderOf (3 : ZMod 7) = 6 :=
      orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide) fun q hq hq6 => by
        have h2 := hq.two_le
        have h6 := Nat.le_of_dvd (by norm_num) hq6
        interval_cases q <;> revert hq6 <;> decide
    exact h ▸ IsPrimitiveRoot.orderOf (3 : ZMod 7)

/-- The prime carried by `TauCeti.dihedralGroupThreeDixonPrimeData` is `7`. -/
@[simp]
theorem dihedralGroupThreeDixonPrimeData_p : dihedralGroupThreeDixonPrimeData.p = 7 := rfl

/-- The primitive sixth root of unity carried by `TauCeti.dihedralGroupThreeDixonPrimeData` is
`3`. -/
@[simp]
theorem dihedralGroupThreeDixonPrimeData_root : dihedralGroupThreeDixonPrimeData.root = 3 := rfl

end TauCeti
