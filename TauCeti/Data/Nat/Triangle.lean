/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Basic

/-!
# Addition of triangular numbers

This file records the standard decomposition of the triangular number of a sum into the two
individual triangular numbers and the cross term.

## Main results

* `TauCeti.Nat.triangle_add`
-/

public section

namespace TauCeti

namespace Nat

/-- The triangular number of `m + n` is the sum of the triangular numbers of `m` and `n`, plus
the cross term `m * n`. -/
theorem triangle_add (m n : ℕ) :
    (m + n) * (m + n - 1) / 2 =
      m * (m - 1) / 2 + n * (n - 1) / 2 + m * n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, Nat.triangle_succ, Nat.triangle_succ, ih]
      simp [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

end Nat

end TauCeti
