/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Swapping two entries of an additive family

This file records the elementary identity expressing a transposition of an additive family as a
reflection. It is shared by coordinate and type-`A` root-datum constructions.
-/

public section

namespace TauCeti

/-- Transposing a family along `Equiv.swap a b` subtracts the corresponding multiple of
`f a - f b`. This is the elementary identity behind coordinate reflection formulas. -/
theorem apply_swap_eq {ι M : Type*} [DecidableEq ι] [AddCommGroup M] (f : ι → M)
    (a b c : ι) :
    f (_root_.Equiv.swap a b c) =
      f c - ((if c = a then 1 else 0) - (if c = b then (1 : ℤ) else 0)) • (f a - f b) := by
  rcases eq_or_ne c a with rfl | hca
  · rcases eq_or_ne c b with rfl | hcb
    · simp
    · simp [_root_.Equiv.swap_apply_left, hcb]
  · rcases eq_or_ne c b with rfl | hcb
    · simp [_root_.Equiv.swap_apply_right, hca]
    · simp [_root_.Equiv.swap_apply_of_ne_of_ne hca hcb, hca, hcb]

end TauCeti
