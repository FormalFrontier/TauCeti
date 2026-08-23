/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
# Commutators in associative semirings and rings

This file records identities for moving elements past powers when the two elements almost commute.

Over a semiring the hypothesis is written as a relation, `x * y = y * x + z`, since there is no
subtraction to form a commutator with: the power identities need only that `z` commutes with the
element being powered, and the nilpotency results additionally need a `ℚ`-algebra structure, to
divide by the multiplicity a power releases. Over a ring the same `z` is the commutator
`x * y - y * x`, which is the form the integer-eigenvector results take.

## Main results

* `TauCeti.Associative.mul_pow_eq_pow_mul_add_zsmul`: moving an element past a power of an
  integer-eigenvector for its commutator.
* `TauCeti.Associative.mul_pow_eq_pow_mul_add_intCast`: the same identity in shifted-factor form.
* `TauCeti.Associative.mul_pow_eq_pow_mul_add_nsmul_of_commutator_eq`: moving an element across a
  power releases that many copies of the correction term, when that term commutes with the element
  being powered.
* `TauCeti.Associative.pow_mul_eq_mul_pow_add_nsmul_of_commutator_eq`: the mirrored orientation,
  moving an element across a power standing to its left.
* `TauCeti.Associative.isNilpotent_of_commutator_eq`: a commutator commuting with both of its
  arguments is nilpotent as soon as one of them is.
* `TauCeti.Associative.isNilpotent_of_commutator_eq_nsmul`: the same conclusion when the
  commutator is a nonzero natural multiple of the element.
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

section PowerCommutator

variable {A : Type*} [Semiring A]

/-- **Moving an element across a power releases that many copies of the correction term.** If
`x * y = y * x + z` and `z` commutes with `y`, then `x * y ^ n` is `y ^ n * x` plus `n` copies of
`y ^ (n - 1) * z`. -/
theorem mul_pow_eq_pow_mul_add_nsmul_of_commutator_eq {x y z : A} (hxy : x * y = y * x + z)
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


/-- **Moving `y` past a power of `x` releases that many copies of the correction term.** If
`x * y = y * x + z` and `z` commutes with `x`, then `x ^ n * y` is `y * x ^ n` plus `n` copies of
`x ^ (n - 1) * z`. -/
theorem pow_mul_eq_mul_pow_add_nsmul_of_commutator_eq {x y z : A}
    (hxy : x * y = y * x + z)
    (hxz : Commute x z) (n : ℕ) :
    x ^ n * y = y * x ^ n + n • (x ^ (n - 1) * z) := by
  -- the same identity read in the opposite semiring, where `x` and `y` exchange roles; going
  -- through `MulOpposite` rather than negating `z` is what keeps this off `Ring`
  have hop : MulOpposite.op y * MulOpposite.op x
      = MulOpposite.op x * MulOpposite.op y + MulOpposite.op z := by
    simpa [MulOpposite.op_mul] using congrArg MulOpposite.op hxy
  have hcop : Commute (MulOpposite.op x) (MulOpposite.op z) := by
    simpa [Commute, SemiconjBy, ← MulOpposite.op_mul] using congrArg MulOpposite.op hxz.eq.symm
  have h := congrArg MulOpposite.unop
    (mul_pow_eq_pow_mul_add_nsmul_of_commutator_eq hop hcop n)
  simp only [MulOpposite.unop_mul, MulOpposite.unop_pow, MulOpposite.unop_add,
    MulOpposite.unop_op, MulOpposite.unop_smul] at h
  rwa [← (hxz.pow_left (n - 1)).eq] at h

end PowerCommutator

section CentralCommutator

variable {A : Type*} [Semiring A] [Algebra ℚ A] {x y z : A}

/-- **Extracting one copy of a central commutator trades a power of `x` for a power of `z`.** If
`x ^ (m + 1)` annihilates `z ^ k` on the left, then `x ^ m` annihilates `z ^ (k + 1)`. -/
private theorem pow_mul_pow_succ_eq_zero_of_pow_succ_mul_pow_eq_zero (hxy : x * y = y * x + z)
    (hxz : Commute x z) (hyz : Commute y z) {m k : ℕ} (h : x ^ (m + 1) * z ^ k = 0) :
    x ^ m * z ^ (k + 1) = 0 := by
  -- Pushing `y` to the right kills the product outright.
  have hA : x ^ (m + 1) * y * z ^ k = 0 := by
    rw [mul_assoc, ← (hyz.symm.pow_left k).eq, ← mul_assoc, h, zero_mul]
  -- Pushing it to the left leaves the released copies of `z`.
  have hB : x ^ (m + 1) * y * z ^ k = (m + 1) • (x ^ m * z ^ (k + 1)) := by
    rw [pow_mul_eq_mul_pow_add_nsmul_of_commutator_eq hxy hxz (m + 1), Nat.add_sub_cancel, add_mul,
      mul_assoc, h, mul_zero, zero_add, smul_mul_assoc, mul_assoc, ← pow_succ']
  have hkey : ((m + 1 : ℕ) : ℚ) • (x ^ m * z ^ (k + 1)) = 0 := by
    rw [Nat.cast_smul_eq_nsmul ℚ, ← hB]
    exact hA
  have hc : (((m + 1 : ℕ) : ℚ))⁻¹ • (((m + 1 : ℕ) : ℚ) • (x ^ m * z ^ (k + 1))) = 0 := by
    rw [hkey, smul_zero]
  rwa [inv_smul_smul₀ (Nat.cast_ne_zero.mpr m.succ_ne_zero)] at hc

/-- **Nilpotency of a central commutator.** If `x * y = y * x + z` with `z` commuting with both `x`
and `y`, then `z` is nilpotent as soon as `x` is, with the same nilpotency exponent. -/
theorem isNilpotent_of_commutator_eq (hxy : x * y = y * x + z) (hxz : Commute x z)
    (hyz : Commute y z) (hx : IsNilpotent x) : IsNilpotent z := by
  obtain ⟨n, hn⟩ := hx
  -- Peel the powers of `x` off one at a time, trading each for a power of `z`.
  have hpeel : ∀ k ≤ n, x ^ (n - k) * z ^ k = 0 := by
    intro k
    induction k with
    | zero => intro _; simpa using hn
    | succ k ih =>
      intro hk
      have heq : n - k = n - (k + 1) + 1 := by omega
      exact pow_mul_pow_succ_eq_zero_of_pow_succ_mul_pow_eq_zero hxy hxz hyz
        (by rw [← heq]; exact ih (by omega))
  exact ⟨n, by simpa using hpeel n le_rfl⟩

/-- If `x * y = y * x + n • z` for a nonzero natural number `n`, with `z` commuting with `x`
and `y`, then `z` is nilpotent whenever `x` is. -/
theorem isNilpotent_of_commutator_eq_nsmul {n : ℕ} (hn : n ≠ 0)
    (hxy : x * y = y * x + n • z) (hxz : Commute x z) (hyz : Commute y z)
    (hx : IsNilpotent x) : IsNilpotent z := by
  have hnQ : ((n : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnil := (isNilpotent_of_commutator_eq hxy (hxz.smul_right n)
    (hyz.smul_right n) hx).smul ((n : ℚ)⁻¹)
  simpa only [← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ hnQ] using hnil

end CentralCommutator

end TauCeti.Associative
