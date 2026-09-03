/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Complements on the multiplicative monoid of ideals

This file collects general facts about the multiplication of ideals of a commutative semiring,
complementing `Mathlib/RingTheory/Ideal/Operations.lean`.

## Main results

* `Ideal.eq_one_of_mul_eq_one`: the only factorization of the unit ideal is the trivial one, so a
  factor of `1` is `1`. This is the ideal-theoretic cancellation step behind the fact that the
  divisor antidiagonal of the unit ideal is a singleton.
* `Ideal.pow_mul_pow_le_pow_succ`: the square of `I ^ n` lands one step further down the
  `I`-adic filtration, for `n ≠ 0`.
-/

public section

namespace Ideal

variable {R : Type*} [CommSemiring R] {I J : Ideal R}

/-- If two ideals multiply to the unit ideal, then the first ideal is the unit ideal. -/
theorem eq_one_of_mul_eq_one (h : I * J = 1) : I = 1 := by
  have hle : (1 : Ideal R) ≤ I := by
    rw [← h]
    exact Ideal.mul_le_left
  rw [Ideal.one_eq_top, eq_top_iff]
  simpa [Ideal.one_eq_top] using hle

/-- For `n ≠ 0` the product `I ^ n * I ^ n` is contained in `I ^ (n + 1)`, since `n + 1 ≤ 2 * n`.
This is the hypothesis under which `u ↦ u - 1` is additive on `1 + I ^ n` modulo `I ^ (n + 1)`. -/
theorem pow_mul_pow_le_pow_succ (I : Ideal R) {n : ℕ} (hn : n ≠ 0) :
    I ^ n * I ^ n ≤ I ^ (n + 1) := by
  rw [← pow_add]
  exact Ideal.pow_le_pow_right (by omega)

end Ideal

end
