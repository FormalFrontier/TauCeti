/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Counting occurrences modulo two

This file records that a list concatenated with itself contains every element an even number of
times, in the form that the count vanishes in `ZMod 2`.
-/

public section

namespace TauCeti

/-- A list concatenated with itself contains every element an even number of times, so the count
of any element vanishes in `ZMod 2`. -/
theorem natCast_count_append_self {α : Type*} [BEq α] (t : α) (l : List α) :
    (((l ++ l).count t : ℕ) : ZMod 2) = 0 := by
  rw [List.count_append, Nat.cast_add]
  generalize ((l.count t : ℕ) : ZMod 2) = x
  revert x
  decide

end TauCeti
