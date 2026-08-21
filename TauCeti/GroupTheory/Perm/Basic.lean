/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Support

/-!
# Elementary facts about permutations

This file records general-purpose identities between transpositions.
-/

public section

namespace TauCeti

/-- For three distinct points, the transpositions `(a b)` and `(b c)` satisfy the braid
relation. -/
theorem swap_braid {α : Type*} [DecidableEq α] {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (hcb : c ≠ b) :
    Equiv.swap a b * Equiv.swap b c * Equiv.swap a b =
      Equiv.swap b c * Equiv.swap a b * Equiv.swap b c :=
  calc Equiv.swap a b * Equiv.swap b c * Equiv.swap a b
      = Equiv.swap b a * Equiv.swap c b * Equiv.swap b a := by
        rw [Equiv.swap_comm a b, Equiv.swap_comm b c]
    _ = Equiv.swap a c := Equiv.swap_mul_swap_mul_swap hcb (Ne.symm hac)
    _ = Equiv.swap c a := Equiv.swap_comm a c
    _ = Equiv.swap b c * Equiv.swap a b * Equiv.swap b c :=
        (Equiv.swap_mul_swap_mul_swap hab hac).symm

end TauCeti
