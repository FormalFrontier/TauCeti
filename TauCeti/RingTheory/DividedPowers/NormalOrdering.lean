/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import TauCeti.RingTheory.DividedPowers.Associative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Normal ordering divided powers with a central commutator

Let `x`, `y`, and `z` belong to an associative algebra over `ℚ`, with
`x * y = y * x + z`. When `z` commutes with both `x` and `y`, the divided powers admit the
coefficient-one normal-ordering formula

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ k ≤ min(m,n), y⁽ⁿ⁻ᵏ⁾ z⁽ᵏ⁾ x⁽ᵐ⁻ᵏ⁾.
```

This is the class-two case of the straightening relations used in a Kostant integral form. For a
Chevalley basis it applies whenever `[x, y]` is a root vector and both further brackets with `x`
and `y` vanish; in particular it covers non-opposite roots `α` and `β` in a simply-laced root
system when `α + β` is a root. The coefficient-one form is the integral content: reordering the
rational divided powers introduces no rational structure constants.

The preliminary one-sided formula only needs `z` to commute with `y`. The full formula additionally
needs `z` to commute with `x`, because its normal form places all powers of `z` between those of `y`
and `x`.

Both are instances of one rule without any class-two restriction. Whenever a sequence `d : ℕ → A`
behaves like the divided powers `(ad x)ᵏ(d 0) / k!` of the inner derivation, in the sense that
`x * d k = d k * x + (k + 1) • d (k + 1)`, one gets

```text
x⁽ᵐ⁾ * d 0 = ∑ k ≤ m, d k * x⁽ᵐ⁻ᵏ⁾,
```

again with every coefficient equal to `1`. All of the structure constants of a longer root string
are carried by the sequence `d`, so the rule stays integral exactly when its terms are. The
class-two formula is the case `d k = y⁽ⁿ⁻ᵏ⁾ z⁽ᵏ⁾`, truncated to zero beyond `k = n`.

## Main results

* `TauCeti.Associative.mul_dividedPower_of_commutator_eq`: move one element across a divided power
  when its commutator with the base commutes with that base.
* `TauCeti.Associative.mul_dividedPower_of_commutator_eq'`: the same identity for an exponent that
  is not syntactically a successor.
* `TauCeti.Associative.dividedPower_mul_of_ad_dividedPower_series`: coefficient-one normal ordering
  against an arbitrary divided-power series for the inner derivation.
* `TauCeti.Associative.dividedPower_mul_dividedPower_of_commutator_eq`: the coefficient-one
  normal-ordering formula for two divided powers with central commutator.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative

open Finset

variable {A : Type*} [Semiring A]

/-- Moving one element across an ordinary power when its commutator commutes with the element being
powered. This is kept private because the divided-power form below is the integral interface used by
normal ordering. -/
private theorem mul_pow_of_commutator_eq {x y z : A} (hxy : x * y = y * x + z)
    (hyz : Commute y z) (n : ℕ) :
    x * y ^ n = y ^ n * x + n • (y ^ (n - 1) * z) := by
  induction n with
  | zero => simp
  | succ n ih =>
      cases n with
      | zero => simpa using hxy
      | succ n =>
          simp only [Nat.add_sub_cancel] at ih ⊢
          rw [pow_succ, ← mul_assoc, ih, add_mul, mul_assoc (y ^ (n + 1)) x y,
            hxy, mul_add]
          -- Expose the final successor separately: rewriting `add_nsmul` on `n + 2` directly
          -- would split the coefficient as `n` and `2`, rather than the required `n + 1` and `1`.
          rw [show n + 2 = (n + 1) + 1 by omega, add_nsmul, one_nsmul]
          noncomm_ring [hyz.eq, pow_succ]
          simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat, mul_one]
          noncomm_ring

variable [Algebra ℚ A]

/-- **First-order divided-power normal ordering.** If `x * y = y * x + z` and `z` commutes
with `y`, then

```text
x y⁽ⁿ⁺¹⁾ = y⁽ⁿ⁺¹⁾ x + y⁽ⁿ⁾ z.
```

Unlike the corresponding ordinary-power identity, the divided-power identity has coefficient one.
No commutation hypothesis between `x` and `z` is needed for this one-sided formula. -/
theorem mul_dividedPower_of_commutator_eq {x y z : A} (hxy : x * y = y * x + z)
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

/-- The form of `mul_dividedPower_of_commutator_eq` for an exponent that is not syntactically a
successor: the commutator term is present exactly when the exponent is positive. This is the shape
needed when the exponent is a summation variable. -/
theorem mul_dividedPower_of_commutator_eq' {x y z : A} (hxy : x * y = y * x + z)
    (hyz : Commute y z) (n : ℕ) :
    x * dividedPower n y =
      dividedPower n y * x + if 0 < n then dividedPower (n - 1) y * z else 0 := by
  cases n with
  | zero => simp
  | succ n => simpa using mul_dividedPower_of_commutator_eq hxy hyz n

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

/-! ## Normal ordering against a divided-power series for the inner derivation -/

/-- **Coefficient-one normal ordering against a divided-power series.** Let `d : ℕ → A` satisfy

```text
x * d k = d k * x + (k + 1) • d (k + 1)
```

for every `k`, which is what the sequence `k ↦ (ad x)ᵏ (d 0) / k!` does. Then

```text
x⁽ᵐ⁾ * d 0 = ∑ k ≤ m, d k * x⁽ᵐ⁻ᵏ⁾.
```

Every coefficient is `1`: the sequence `d` carries all of the structure constants, so the rule is
integral precisely when its terms are. The class-two formula
`dividedPower_mul_dividedPower_of_commutator_eq` below is derived from this one as the case
`d k = y⁽ⁿ⁻ᵏ⁾ z⁽ᵏ⁾`, truncated to zero beyond `k = n`; the chain `β`, `α + β`, `2α + β` needs a
longer sequence and nothing else. -/
theorem dividedPower_mul_of_ad_dividedPower_series {x : A} {d : ℕ → A}
    (hd : ∀ k, x * d k = d k * x + (k + 1) • d (k + 1)) (m : ℕ) :
    dividedPower m x * d 0 = ∑ k ∈ range (m + 1), d k * dividedPower (m - k) x := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hm : (((m + 1 : ℕ) : ℚ)) ≠ 0 := by positivity
      -- Each summand splits into the term that lengthens the `x`-power and the term that
      -- advances the series; the two are the adjacent contributions of the weighted sum below.
      have hstep : ∀ k ∈ range (m + 1),
          x * (d k * dividedPower (m - k) x) =
            (m + 1 - k) • (d k * dividedPower (m + 1 - k) x) +
              (k + 1) • (d (k + 1) * dividedPower (m + 1 - (k + 1)) x) := by
        intro k hk
        have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        have h1 : m - k + 1 = m + 1 - k := by omega
        have h2 : m - k = m + 1 - (k + 1) := by omega
        calc x * (d k * dividedPower (m - k) x)
            = x * d k * dividedPower (m - k) x := by rw [mul_assoc]
          _ = d k * (x * dividedPower (m - k) x) +
                (k + 1) • (d (k + 1) * dividedPower (m - k) x) := by
              rw [hd k, add_mul, mul_assoc, smul_mul_assoc]
          _ = (m - k + 1) • (d k * dividedPower (m - k + 1) x) +
                (k + 1) • (d (k + 1) * dividedPower (m - k) x) := by
              rw [self_mul_dividedPower, mul_smul_comm]
          _ = _ := by rw [h1, ← h2]
      rw [← inv_smul_smul₀ hm (dividedPower (m + 1) x * d 0),
        ← inv_smul_smul₀ hm (∑ k ∈ range (m + 1 + 1), d k * dividedPower (m + 1 - k) x)]
      congr 1
      simp only [Nat.cast_smul_eq_nsmul]
      rw [succ_nsmul_dividedPower_succ_mul, ih, Finset.mul_sum,
        Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
      have hsum := sum_sub_nsmul_add_succ_nsmul
          (u := fun k ↦ d k * dividedPower (m + 1 - k) x) (M := m + 1) (C := m + 1) le_rfl
      rw [← hsum, Finset.sum_range_succ (n := m + 1)]
      simp

/-! ## The class-two case -/

/-- **Coefficient-one normal ordering for divided powers with central commutator.** Suppose
`x * y = y * x + z`, and `z` commutes with both `x` and `y`. Then

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ k ≤ min(m,n), y⁽ⁿ⁻ᵏ⁾ z⁽ᵏ⁾ x⁽ᵐ⁻ᵏ⁾.
```

The summation is written as `range (min m n + 1)`, so every displayed subtraction is exact. This is
the integral normal-ordering rule: every coefficient in the divided-power basis is `1`.

This is the case `d k = y⁽ⁿ⁻ᵏ⁾ z⁽ᵏ⁾` of `dividedPower_mul_of_ad_dividedPower_series`: the
class-two hypotheses make that truncated sequence a divided-power series for the inner derivation
of `x`, and its vanishing beyond `k = n` is what stops the sum at `min m n`. -/
theorem dividedPower_mul_dividedPower_of_commutator_eq {x y z : A}
    (hxy : x * y = y * x + z) (hxz : Commute x z) (hyz : Commute y z) (m n : ℕ) :
    dividedPower m x * dividedPower n y =
      ∑ k ∈ range (min m n + 1),
        dividedPower (n - k) y * dividedPower k z * dividedPower (m - k) x := by
  -- The divided powers `(ad x)ᵏ (y⁽ⁿ⁾) / k!` of the inner derivation are `y⁽ⁿ⁻ᵏ⁾ z⁽ᵏ⁾` for
  -- `k ≤ n`, and vanish beyond that because `x` commutes with every `z⁽ᵏ⁾`.
  set d : ℕ → A := fun k ↦ if k ≤ n then dividedPower (n - k) y * dividedPower k z else 0
    with hd_def
  have hval : ∀ k, k ≤ n → d k = dividedPower (n - k) y * dividedPower k z := by
    intro k hk
    simp [hd_def, hk]
  have hvanish : ∀ k, n < k → d k = 0 := by
    intro k hk
    simp [hd_def, Nat.not_le.mpr hk]
  have hxzk : ∀ k, Commute x (dividedPower k z) := fun k ↦ by
    simpa using commute_dividedPower_dividedPower hxz 1 k
  have hd : ∀ k, x * d k = d k * x + (k + 1) • d (k + 1) := by
    intro k
    rcases lt_trichotomy k n with hkn | hkn | hkn
    · -- Both terms are present: `x` either passes through the `y`-power or produces one `z`.
      have hnk : n - k = (n - (k + 1)) + 1 := by omega
      have hstep : x * dividedPower (n - k) y =
          dividedPower (n - k) y * x + dividedPower (n - (k + 1)) y * z := by
        rw [hnk]
        exact mul_dividedPower_of_commutator_eq hxy hyz _
      rw [hval k hkn.le, hval (k + 1) hkn]
      calc x * (dividedPower (n - k) y * dividedPower k z)
          = x * dividedPower (n - k) y * dividedPower k z := by rw [mul_assoc]
        _ = dividedPower (n - k) y * (x * dividedPower k z) +
              dividedPower (n - (k + 1)) y * (z * dividedPower k z) := by
            rw [hstep, add_mul, mul_assoc, mul_assoc]
        _ = _ := by
            rw [(hxzk k).eq, ← mul_assoc, self_mul_dividedPower, mul_smul_comm]
    · -- At `k = n` the `y`-power is empty, so no commutator term survives.
      have hnk : n - k = 0 := by omega
      rw [hval k hkn.le, hvanish (k + 1) (by omega), hnk, dividedPower_zero, one_mul, smul_zero,
        add_zero]
      exact (hxzk k).eq
    · -- Past `k = n` the sequence has run out.
      rw [hvanish k hkn, hvanish (k + 1) (by omega), mul_zero, zero_mul, smul_zero, add_zero]
  have hd0 : d 0 = dividedPower n y := by
    rw [hval 0 (Nat.zero_le n), Nat.sub_zero, dividedPower_zero, mul_one]
  have hmain := dividedPower_mul_of_ad_dividedPower_series hd m
  rw [hd0] at hmain
  -- The summands beyond `k = min m n` vanish, which truncates the sum of the general rule.
  have hzero : ∀ k ∈ range (m + 1), k ∉ range (min m n + 1) →
      d k * dividedPower (m - k) x = 0 := by
    intro k hk hk'
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk'
    rw [hvanish k (by omega), zero_mul]
  rw [hmain,
    ← Finset.sum_subset (Finset.range_subset_range.mpr (by omega : min m n + 1 ≤ m + 1)) hzero]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [hval k (le_trans hk (min_le_right m n))]

end TauCeti.Associative
