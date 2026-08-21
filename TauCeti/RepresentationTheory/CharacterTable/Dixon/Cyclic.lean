/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Prime

/-!
# Dixon prime data for the cyclic group of order two

The rational Dixon--Schneider computation for `Multiplicative (ZMod 2)` runs over `ZMod 3`.
The prime `3` does not divide the group order, the exponent `2` divides `3 - 1`, and Dixon's size
bound is `2 * sqrt(2) = 2 < 3`.  The element `-1` is the required primitive square root of unity
modulo `3`.

## Main definitions

* `TauCeti.cyclicGroupTwoDixonPrimeData`: the prime `3` and its primitive square root `-1`.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* The character theory roadmap, Layer 6, “Certified Dixon prime data”.
-/

public section

namespace TauCeti

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

end TauCeti
