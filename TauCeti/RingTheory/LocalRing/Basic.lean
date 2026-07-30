/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Idempotents of a local ring

A local ring has no idempotents besides `0` and `1`: splitting `1 = a + (1 - a)` makes one of the
two summands a unit, and an idempotent unit is `1`.

## Main result

* `TauCeti.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem`: an idempotent of a local ring is `0`
  or `1`.
-/

public section

namespace TauCeti

/-- An idempotent of a local ring is `0` or `1`. Mathlib's
`IsLocalRing.isUnit_or_isUnit_one_sub_self` is stated over a commutative ring, so the splitting of
`1 = a + (1 - a)` is taken here from `IsLocalRing.isUnit_or_isUnit_of_isUnit_add`, which holds over
any semiring. -/
theorem IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem {R : Type*} [Ring R] [IsLocalRing R]
    {a : R} (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
  have hsum : IsUnit (a + (1 - a)) := by simp
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum with hu | hu
  · exact Or.inr (hu.mul_left_cancel (by rw [ha, mul_one]))
  · refine Or.inl ?_
    have hidem : IsIdempotentElem (1 - a) := IsIdempotentElem.one_sub ha
    have hone : (1 : R) - a = 1 := hu.mul_left_cancel (by rw [hidem, mul_one])
    exact sub_eq_self.mp hone

end TauCeti
