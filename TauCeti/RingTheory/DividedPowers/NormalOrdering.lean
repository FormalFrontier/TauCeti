/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RingTheory.DividedPowers.Associative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module

/-!
# Normal ordering divided powers with a central commutator

Let `x`, `y`, and `z` belong to an associative algebra over `ℚ`, with
`x * y - y * x = z`. When `z` commutes with both `x` and `y`, the divided powers admit the
coefficient-one normal-ordering formula

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ k ≤ min(m,n), y⁽ⁿ⁻ᵏ⁾ z⁽ᵏ⁾ x⁽ᵐ⁻ᵏ⁾.
```

This is the class-two case of the straightening relations used in a Kostant integral form. For a
Chevalley basis it applies whenever `[x, y]` is a root vector and both further brackets with `x`
and `y` vanish; in particular it covers the noncommuting root-vector pairs in a simply-laced root
system. The coefficient-one form is the integral content: reordering the rational divided powers
introduces no rational structure constants.

The preliminary one-sided formula only needs `z` to commute with `y`. The full formula additionally
needs `z` to commute with `x`, because its normal form places all powers of `z` between those of `y`
and `x`.

## Main results

* `TauCeti.Associative.mul_dividedPower_of_commutator_eq`: move one element across a divided power
  when its commutator with the base commutes with that base.
* `TauCeti.Associative.dividedPower_mul_dividedPower_of_commutator_eq`: the coefficient-one
  normal-ordering formula for two divided powers with central commutator.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative

open Finset

variable {A : Type*} [Ring A]

/-- Moving one element across an ordinary power when its commutator commutes with the element being
powered. This is kept private because the divided-power form below is the integral interface used by
normal ordering. -/
private theorem mul_pow_of_commutator_eq {x y z : A} (hxy : x * y - y * x = z)
    (hyz : Commute y z) (n : ℕ) :
    x * y ^ n = y ^ n * x + n • (y ^ (n - 1) * z) := by
  have hxy' : x * y = y * x + z := (sub_eq_iff_eq_add.mp hxy).trans (add_comm _ _)
  induction n with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simpa using hxy'
      | succ n =>
          simp only [Nat.add_sub_cancel] at ih ⊢
          rw [pow_succ, ← mul_assoc, ih, add_mul, mul_assoc (y ^ (n + 1)) x y,
            hxy', mul_add, nsmul_eq_mul, mul_assoc (↑(n + 1) : A) (y ^ n * z) y,
            mul_assoc (y ^ n) z y,
            ← hyz.eq, ← mul_assoc (y ^ n), ← pow_succ]
          rw [← nsmul_eq_mul]
          simp only [← mul_assoc, add_nsmul, one_nsmul, add_comm]
          abel

variable [Algebra ℚ A]

/-- **First-order divided-power normal ordering.** If `x * y - y * x = z` and `z` commutes
with `y`, then

```text
x y⁽ⁿ⁺¹⁾ = y⁽ⁿ⁺¹⁾ x + y⁽ⁿ⁾ z.
```

Unlike the corresponding ordinary-power identity, the divided-power identity has coefficient one.
No commutation hypothesis between `x` and `z` is needed for this one-sided formula. -/
theorem mul_dividedPower_of_commutator_eq {x y z : A} (hxy : x * y - y * x = z)
    (hyz : Commute y z) (n : ℕ) :
    x * dividedPower (n + 1) y =
      dividedPower (n + 1) y * x + dividedPower n y * z := by
  simp only [dividedPower_def]
  rw [mul_smul_comm, smul_mul_assoc, mul_pow_of_commutator_eq hxy hyz, smul_add]
  simp only [Nat.add_sub_cancel]
  congr 1
  rw [smul_mul_assoc, ← Nat.cast_smul_eq_nsmul ℚ, ← mul_smul]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

-- This weighted-sum identity is the bookkeeping behind the induction in the normal-ordering
-- theorem. The first sum records the term in which `x` passes through `y`; the second records the
-- commutator term and is shifted by one.
private theorem sum_sub_nsmul_add_succ_nsmul (u : ℕ → A) {M C : ℕ} (hMC : M ≤ C) :
    (∑ k ∈ range (M + 1), (C - k) • u k) +
        ∑ k ∈ range M, (k + 1) • u (k + 1) =
      C • ∑ k ∈ range (M + 1), u k := by
  induction M with
  | zero => simp
  | succ M ih =>
      have hM : M ≤ C := le_trans (Nat.le_succ M) hMC
      have hih := ih hM
      have hcoeff := Nat.sub_add_cancel hMC
      have hcoeffQ : ((C - (M + 1) : ℕ) : ℚ) + (M + 1 : ℕ) = C := by
        exact_mod_cast hcoeff
      simp only [Finset.sum_range_succ] at hih ⊢
      simp_rw [← Nat.cast_smul_eq_nsmul ℚ] at hih ⊢
      calc
        _ = ((∑ k ∈ range M, ((C - k : ℕ) : ℚ) • u k) + ((C - M : ℕ) : ℚ) • u M +
              ∑ k ∈ range M, ((k + 1 : ℕ) : ℚ) • u (k + 1)) +
            (((C - (M + 1) : ℕ) : ℚ) • u (M + 1) +
              ((M + 1 : ℕ) : ℚ) • u (M + 1)) := by
              module
        _ = (C : ℚ) • (∑ k ∈ range M, u k + u M) + (C : ℚ) • u (M + 1) := by
              rw [hih]
              rw [← add_smul, hcoeffQ]
        _ = _ := by rw [← smul_add]

-- Multiplying one normal-ordered summand by `x` either lengthens its final `x`-power or uses
-- the commutator and lengthens its middle `z`-power. These are the two adjacent contributions
-- combined by `sum_sub_nsmul_add_succ_nsmul`.
private theorem mul_normalOrderTerm {x y z : A} (hxy : x * y - y * x = z)
    (hxz : Commute x z) (hyz : Commute y z) {m n k : ℕ} (hkm : k ≤ m) (hkn : k < n) :
    x * (dividedPower (n - k) y * dividedPower k z * dividedPower (m - k) x) =
      (m + 1 - k) •
          (dividedPower (n - k) y * dividedPower k z * dividedPower (m + 1 - k) x) +
        (k + 1) •
          (dividedPower (n - (k + 1)) y * dividedPower (k + 1) z *
            dividedPower (m + 1 - (k + 1)) x) := by
  have hnk : n - k = (n - (k + 1)) + 1 := by omega
  have hmk : m + 1 - k = (m - k) + 1 := by omega
  have hmk' : m + 1 - (k + 1) = m - k := by omega
  have hxzk : Commute x (dividedPower k z) := by
    simpa using commute_dividedPower_dividedPower hxz 1 k
  rw [mul_assoc (dividedPower (n - k) y) (dividedPower k z),
    ← mul_assoc x (dividedPower (n - k) y), hnk,
    mul_dividedPower_of_commutator_eq hxy hyz, add_mul]
  rw [← hnk]
  congr 1
  · rw [mul_assoc (dividedPower (n - k) y) x,
      ← mul_assoc x (dividedPower k z), hxzk.eq,
      mul_assoc (dividedPower k z) x, ← mul_assoc (dividedPower (n - k) y),
      self_mul_dividedPower, ← Nat.cast_smul_eq_nsmul ℚ, mul_smul_comm,
      Nat.cast_smul_eq_nsmul, hmk]
  · rw [mul_assoc (dividedPower (n - (k + 1)) y) z,
      ← mul_assoc z (dividedPower k z), self_mul_dividedPower,
      ← Nat.cast_smul_eq_nsmul ℚ, smul_mul_assoc, mul_smul_comm,
      Nat.cast_smul_eq_nsmul, hmk', ← mul_assoc]

-- At the last summand `k = n`, no commutator term remains because the `y`-power is zero.
private theorem mul_normalOrderLast {x z : A} (hxz : Commute x z) {m n : ℕ} (hnm : n ≤ m) :
    x * (dividedPower n z * dividedPower (m - n) x) =
      (m + 1 - n) • (dividedPower n z * dividedPower (m + 1 - n) x) := by
  have hmn : m + 1 - n = (m - n) + 1 := by omega
  have hxzn : Commute x (dividedPower n z) := by
    simpa using commute_dividedPower_dividedPower hxz 1 n
  rw [← mul_assoc, hxzn.eq, mul_assoc, self_mul_dividedPower,
    ← Nat.cast_smul_eq_nsmul ℚ, mul_smul_comm, Nat.cast_smul_eq_nsmul, hmn]

/-- **Coefficient-one normal ordering for divided powers with central commutator.** Suppose
`x * y - y * x = z`, and `z` commutes with both `x` and `y`. Then

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ k ≤ min(m,n), y⁽ⁿ⁻ᵏ⁾ z⁽ᵏ⁾ x⁽ᵐ⁻ᵏ⁾.
```

The summation is written as `range (min m n + 1)`, so every displayed subtraction is exact. This is
the integral normal-ordering rule: every coefficient in the divided-power basis is `1`. -/
theorem dividedPower_mul_dividedPower_of_commutator_eq {x y z : A}
    (hxy : x * y - y * x = z) (hxz : Commute x z) (hyz : Commute y z) (m n : ℕ) :
    dividedPower m x * dividedPower n y =
      ∑ k ∈ range (min m n + 1),
        dividedPower (n - k) y * dividedPower k z * dividedPower (m - k) x := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm : (m + 1 : ℚ) ≠ 0 := by positivity
      rw [← inv_smul_smul₀ hm (dividedPower (m + 1) x * dividedPower n y),
        ← inv_smul_smul₀ hm
          (∑ k ∈ range (min (m + 1) n + 1),
            dividedPower (n - k) y * dividedPower k z * dividedPower (m + 1 - k) x)]
      congr 1
      rw [← smul_mul_assoc, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_smul_eq_nsmul,
        ← self_mul_dividedPower, mul_assoc, ih, Finset.mul_sum]
      by_cases hnm : n ≤ m
      · have hmin : min m n = n := min_eq_right hnm
        have hmin' : min (m + 1) n = n := min_eq_right (le_trans hnm (Nat.le_succ m))
        rw [hmin, hmin', Finset.sum_range_succ]
        rw [Finset.sum_congr rfl fun k hk ↦
          mul_normalOrderTerm hxy hxz hyz
            (le_trans (Nat.le_of_lt (Finset.mem_range.mp hk)) hnm) (Finset.mem_range.mp hk)]
        simp only [Nat.sub_self, dividedPower_zero, one_mul]
        rw [mul_normalOrderLast hxz hnm, Finset.sum_add_distrib]
        have hsum := sum_sub_nsmul_add_succ_nsmul
            (u := fun k ↦ dividedPower (n - k) y * dividedPower k z *
              dividedPower (m + 1 - k) x)
            (M := n) (C := m + 1) (Nat.le_succ_of_le hnm)
        conv_rhs => rw [Finset.sum_range_succ]
        simp only [Finset.sum_range_succ, Nat.sub_self, dividedPower_zero, one_mul] at hsum ⊢
        simp_rw [← Nat.cast_smul_eq_nsmul ℚ] at hsum ⊢
        rw [← hsum]
        abel
      · have hmn : m < n := Nat.lt_of_not_ge hnm
        have hmin : min m n = m := min_eq_left hmn.le
        have hmin' : min (m + 1) n = m + 1 := min_eq_left hmn
        rw [hmin, hmin']
        rw [Finset.sum_congr rfl fun k hk ↦
          mul_normalOrderTerm hxy hxz hyz (Finset.mem_range_succ_iff.mp hk)
            (lt_of_le_of_lt (Finset.mem_range_succ_iff.mp hk) hmn)]
        rw [Finset.sum_add_distrib]
        simpa only [Finset.sum_range_succ, Nat.sub_self, zero_nsmul, add_zero,
          Nat.cast_smul_eq_nsmul] using
          sum_sub_nsmul_add_succ_nsmul
            (u := fun k ↦ dividedPower (n - k) y * dividedPower k z *
              dividedPower (m + 1 - k) x)
            (M := m + 1) (C := m + 1) le_rfl

end TauCeti.Associative
