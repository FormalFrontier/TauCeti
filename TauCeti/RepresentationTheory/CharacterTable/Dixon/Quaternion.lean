/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Quaternion
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Prime

/-!
# Dixon prime data for the quaternion group of order eight

The executable Dixon--Schneider algorithm receives a certified prime rather than searching for
one noncomputably.  This file certifies `5` for `QuaternionGroup 2`, together with `2` as a
primitive fourth root of unity modulo `5`.

## Main definitions

* `TauCeti.quaternionGroupTwoDixonPrimeData`: Dixon prime data for `QuaternionGroup 2`.

## References

* The roadmap `RepresentationTheory/CharacterTheory`, Layer 6, "Certified Dixon prime data".
-/

public section

namespace TauCeti

/-- **`5` is a good Dixon prime for the quaternion group of order eight**: `5 ∤ 8`, its
exponent `4` divides `5 - 1`, and `2⌊√8⌋ = 4 < 5`. -/
theorem isGoodDixonPrime_quaternionGroup_two_five : IsGoodDixonPrime (QuaternionGroup 2) 5 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    decide
  · rw [exponent_quaternionGroup_two]
  · rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
    have h : Nat.sqrt (4 * 2) < 3 := Nat.sqrt_lt.2 (by norm_num)
    omega

/-- Dixon prime data for `QuaternionGroup 2`: the prime `5`, with `2` as the primitive fourth
root of unity modulo `5`. -/
@[expose] def quaternionGroupTwoDixonPrimeData : DixonPrimeData (QuaternionGroup 2) where
  p := 5
  root := 2
  isGoodDixonPrime := isGoodDixonPrime_quaternionGroup_two_five
  isPrimitiveRoot_root := by
    rw [exponent_quaternionGroup_two]
    exact .mk_of_lt 2 (by norm_num) (by decide) fun l hl0 hl4 => by interval_cases l <;> decide

/-- The prime carried by `TauCeti.quaternionGroupTwoDixonPrimeData` is `5`. -/
@[simp]
theorem quaternionGroupTwoDixonPrimeData_p : quaternionGroupTwoDixonPrimeData.p = 5 := rfl

/-- The primitive fourth root carried by `TauCeti.quaternionGroupTwoDixonPrimeData` is `2`. -/
@[simp]
theorem quaternionGroupTwoDixonPrimeData_root : quaternionGroupTwoDixonPrimeData.root = 2 := rfl

end TauCeti
