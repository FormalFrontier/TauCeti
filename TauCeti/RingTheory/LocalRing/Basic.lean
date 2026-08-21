/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Local rings that are not commutative

Mathlib develops local rings mostly over a commutative base. This file records the two facts about
a possibly noncommutative local ring that the Krull-Schmidt theorem needs of the endomorphism ring
of an indecomposable module: it has no idempotents besides `0` and `1` (splitting `1 = a + (1 - a)`
makes one of the two summands a unit, and an idempotent unit is `1`), and locality transfers along a
ring equivalence.

## Main results

* `TauCeti.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem`: an idempotent of a local ring is `0`
  or `1`.
* `TauCeti.IsLocalRing.of_ringEquiv`: a semiring equivalent to a local semiring is local.
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

/-- A semiring equivalent to a local semiring is local. Mathlib's `RingEquiv.isLocalRing` asks the
source to be commutative, since it goes through `IsLocalRing.of_surjective`; transporting the
defining condition on a pair of elements summing to a unit needs no commutativity. -/
theorem IsLocalRing.of_ringEquiv {R S : Type*} [Semiring R] [Semiring S] [IsLocalRing R]
    (e : R ≃+* S) : IsLocalRing S := by
  have := e.symm.toEquiv.nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add fun a b hab ↦ ?_
  have hsum : IsUnit (e.symm a + e.symm b) := by simpa using hab.map e.symm
  exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum).imp (fun hu ↦ by simpa using hu.map e)
    fun hu ↦ by simpa using hu.map e

end TauCeti
