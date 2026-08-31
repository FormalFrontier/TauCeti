/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Data.Nat.Factorial.SuperFactorial

/-!
# Positivity of the superfactorial

`Nat.superFactorial n = 0! · 1! ⋯ n!` is Mathlib's superfactorial, and
`Nat.prod_range_succ_factorial` is its expansion as a product of factorials.  Mathlib does not
record the immediate consequence that the value is positive, which is what lets the superfactorial
be cancelled from an identity over `ℕ`.

## Main results

* `TauCeti.Nat.superFactorial_pos`: the superfactorial is positive.
-/

public section

namespace TauCeti

namespace Nat

/-- **The superfactorial is positive**, being a product of factorials. -/
theorem superFactorial_pos (n : ℕ) : 0 < n.superFactorial := by
  rw [← Nat.prod_range_succ_factorial n]
  exact Nat.prod_factorial_pos _ id

end Nat

end TauCeti
