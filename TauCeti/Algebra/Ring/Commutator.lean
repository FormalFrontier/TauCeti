/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Commutators in associative rings

This file records identities for moving elements past powers when their ring commutator is a
scalar multiple of one of the elements.

## Main results

* `TauCeti.Associative.mul_pow_eq_pow_mul_add_zsmul`: moving an element past a power of an
  integer-eigenvector for its commutator.
* `TauCeti.Associative.mul_pow_eq_pow_mul_add_intCast`: the same identity in shifted-factor form.
-/

public section

namespace TauCeti.Associative

variable {A : Type*} [Ring A] {x y : A} {c : ℤ}

/-- If `y` has integer eigenvalue `c` for commutation with `x`, then moving `x` past `yⁿ`
adds `n * c` copies of `yⁿ`. -/
theorem mul_pow_eq_pow_mul_add_zsmul (hxy : x * y - y * x = c • y) (n : ℕ) :
    x * y ^ n = y ^ n * x + ((n : ℤ) * c) • y ^ n := by
  have hy : x * y = y * x + c • y := by
    rw [← hxy]
    abel
  induction n with
  | zero => simp
  | succ n ih =>
    calc x * y ^ (n + 1) = x * y ^ n * y := by rw [pow_succ, ← mul_assoc]
      _ = (y ^ n * x + ((n : ℤ) * c) • y ^ n) * y := by rw [ih]
      _ = y ^ n * (x * y) + ((n : ℤ) * c) • y ^ (n + 1) := by
          rw [add_mul, mul_assoc, smul_mul_assoc, ← pow_succ]
      _ = y ^ n * (y * x + c • y) + ((n : ℤ) * c) • y ^ (n + 1) := by rw [hy]
      _ = y ^ (n + 1) * x + (c + (n : ℤ) * c) • y ^ (n + 1) := by
          rw [mul_add, ← mul_assoc, ← pow_succ, mul_smul_comm, ← pow_succ, add_assoc, ← add_smul]
      _ = y ^ (n + 1) * x + (((n + 1 : ℕ) : ℤ) * c) • y ^ (n + 1) := by
          push_cast
          ring_nf

/-- The shifted-factor form of `mul_pow_eq_pow_mul_add_zsmul`. -/
theorem mul_pow_eq_pow_mul_add_intCast (hxy : x * y - y * x = c • y) (n : ℕ) :
    x * y ^ n = y ^ n * (x + (c : A) * (n : A)) := by
  rw [mul_pow_eq_pow_mul_add_zsmul hxy, zsmul_eq_mul', mul_add, Int.cast_mul,
    Int.cast_natCast, (Nat.cast_commute n (c : A)).eq]

end TauCeti.Associative
