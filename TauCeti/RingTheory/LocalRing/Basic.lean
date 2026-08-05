/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.RingTheory.LocalRing.Basic

/-!
# Idempotents and finite sums in a local ring

A local ring has no idempotents besides `0` and `1`: splitting `1 = a + (1 - a)` makes one of the
two summands a unit, and an idempotent unit is `1`. The same splitting, iterated along a `Finset`,
shows that a finite sum can only be a unit if one of its terms already is.

## Main results

* `TauCeti.IsLocalRing.eq_zero_or_eq_one_of_isIdempotentElem`: an idempotent of a local ring is `0`
  or `1`.
* `TauCeti.IsLocalRing.exists_isUnit_of_isUnit_sum`: if a finite sum in a local ring is a unit,
  then so is one of its terms.
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

/-- **A finite sum in a local ring is a unit only if one of its terms is.** The non-units of a local
ring are closed under addition, and this is that closure read along a `Finset`; the empty sum is
excluded because `0` is not a unit in a nontrivial ring. -/
theorem IsLocalRing.exists_isUnit_of_isUnit_sum {R : Type*} [Semiring R] [IsLocalRing R]
    {ι : Type*} {s : Finset ι} {f : ι → R} (h : IsUnit (∑ i ∈ s, f i)) :
    ∃ i ∈ s, IsUnit (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty, isUnit_zero_iff] at h; exact absurd h zero_ne_one
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at h
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with hu | hu
    · exact ⟨a, Finset.mem_insert_self a s, hu⟩
    · obtain ⟨i, hi, hui⟩ := ih hu
      exact ⟨i, Finset.mem_insert_of_mem hi, hui⟩

end TauCeti
