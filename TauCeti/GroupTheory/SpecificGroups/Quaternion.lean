/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# A computable enumeration of the quaternion groups

Mathlib equips `QuaternionGroup n` with a `Fintype` instance when `n` is nonzero, but converting
that instance to a list is noncomputable.  The Dixon--Schneider character-table algorithm needs a
list whose reduction can be evaluated by the kernel.  `TauCeti.quaternionElements` lists the two
constructors at every index and `TauCeti.mem_quaternionElements` proves that the list is exhaustive.

The file also records the exponent of `QuaternionGroup 2`, the quaternion group of order eight,
in the form used by its explicit Dixon-prime certificate.

## Main definitions

* `TauCeti.quaternionElements`: a computable enumeration of `QuaternionGroup n`.

## Main results

* `TauCeti.mem_quaternionElements`: the enumeration contains every group element.
* `TauCeti.exponent_quaternionGroup_two`: `QuaternionGroup 2` has exponent four.
-/

public section

namespace TauCeti

/-- The elements `a 0, xa 0, ..., a (2n-1), xa (2n-1)` of `QuaternionGroup n`.  For nonzero
`n` this lists all `4 * n` elements.  The body is exposed so downstream class-data computations
can reduce it in the kernel. -/
@[expose] def quaternionElements (n : ℕ) : List (QuaternionGroup n) :=
  (List.range (2 * n)).flatMap fun i : ℕ =>
    [QuaternionGroup.a (i : ZMod (2 * n)), QuaternionGroup.xa (i : ZMod (2 * n))]

/-- The enumeration `TauCeti.quaternionElements` exhausts `QuaternionGroup n` when `n` is
nonzero. -/
theorem mem_quaternionElements {n : ℕ} [NeZero n] (g : QuaternionGroup n) :
    g ∈ quaternionElements n := by
  have hmem : ∀ i : ZMod (2 * n), i.val ∈ List.range (2 * n) :=
    fun i => List.mem_range.mpr (ZMod.val_lt i)
  cases g with
  | a i =>
      refine List.mem_flatMap.mpr ⟨i.val, hmem i, ?_⟩
      rw [ZMod.natCast_rightInverse i]
      simp
  | xa i =>
      refine List.mem_flatMap.mpr ⟨i.val, hmem i, ?_⟩
      rw [ZMod.natCast_rightInverse i]
      simp

/-- The quaternion group of order eight has exponent four. -/
@[simp]
theorem exponent_quaternionGroup_two : Monoid.exponent (QuaternionGroup 2) = 4 := by
  rw [QuaternionGroup.exponent]
  decide

end TauCeti
