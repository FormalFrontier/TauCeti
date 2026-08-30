/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-!
# Stabilization of the powers of an ideal

Two facts about when the powers of an ideal `I` become constant.

The first is general: if `I ^ (n + 1) = I ^ n`, then `I ^ k = I ^ n` for every `k ≥ n`. Nothing
about the ring beyond `Semiring` is used, and no annihilator appears.

The second is the conditional stabilization criterion: if some `i ∈ I` is such that `1 + i`
annihilates `I ^ n`, then `I ^ (n + 1) = I ^ n`, and hence the powers are constant from `n` on.
The annihilating element is a **hypothesis** here, and neither statement needs commutativity.

Finite generation of `I`, and the localization at `1 + I` that produces such an `i` in Wedhorn's
proof of Proposition 7.49(2), are deliberately **outside** this module: nothing below mentions a
localization, and no theorem here derives the annihilator.

## Main results

* `Ideal.pow_eq_pow_of_pow_succ_eq_pow`: `I ^ (n + 1) = I ^ n` propagates to all `k ≥ n`.
* `Ideal.pow_succ_eq_pow_of_forall_mul_eq_zero`: an `i ∈ I` whose `1 + i` annihilates `I ^ n`
  gives `I ^ (n + 1) = I ^ n`.
* `Ideal.pow_eq_pow_of_forall_mul_eq_zero`: hence `I ^ k = I ^ n` for all `k ≥ n`.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], proof of Proposition 7.49(2), where the conditional
  criterion is the closing step.
-/

public section

namespace Ideal

section Semiring

variable {R : Type*} [Semiring R]

/-- Once the powers of an ideal repeat once, they are constant from that point on. -/
theorem pow_eq_pow_of_pow_succ_eq_pow {I : _root_.Ideal R} {n : ℕ} (h : I ^ (n + 1) = I ^ n)
    {k : ℕ} (hk : n ≤ k) : I ^ k = I ^ n := by
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ m _ ih =>
    have hstep : I ^ (m + 1) = I ^ (n + 1) := by rw [Submodule.pow_succ, Submodule.pow_succ, ih]
    rw [hstep, h]

end Semiring

section Ring

variable {B : Type*} [Ring B]

/-- If some `i ∈ I` is such that `1 + i` annihilates `I ^ n`, then `I ^ (n + 1) = I ^ n`.

Commutativity is not needed. -/
theorem pow_succ_eq_pow_of_forall_mul_eq_zero {I : _root_.Ideal B} {i : B} (hi : i ∈ I) {n : ℕ}
    (h : ∀ x ∈ I ^ n, (1 + i) * x = 0) : I ^ (n + 1) = I ^ n := by
  -- The two cases are genuinely different: for `n ≥ 1` the element `i * x` lands in
  -- `I * I ^ n = I ^ (n + 1)`, whereas at `n = 0` that identity fails for a left ideal, and the
  -- conclusion `I = ⊤` comes instead from `1 + i` annihilating `1`.
  refine le_antisymm (_root_.Ideal.pow_le_pow_right (Nat.le_succ n)) fun x hx ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hone : (1 : B) + i = 0 := by
      simpa using h 1 (by rw [Submodule.pow_zero, Ideal.one_eq_top]; trivial)
    have h1 : (1 : B) ∈ I := by
      rw [eq_neg_iff_add_eq_zero.mpr hone]
      exact neg_mem hi
    rw [Submodule.pow_one, (eq_top_iff_one I).mpr h1]
    trivial
  · have hx0 : x = -(i * x) := by
      have hxx : (1 + i) * x = 0 := h x hx
      have hsum : i * x + x = 0 := by rw [← hxx, add_mul, one_mul, add_comm]
      exact eq_neg_of_add_eq_zero_right hsum
    rw [I.pow_succ' hn.ne', hx0]
    exact neg_mem (mul_mem_mul hi hx)

/-- Under the same hypothesis, the powers of `I` are constant from `n` on. -/
theorem pow_eq_pow_of_forall_mul_eq_zero {I : _root_.Ideal B} {i : B} (hi : i ∈ I) {n : ℕ}
    (h : ∀ x ∈ I ^ n, (1 + i) * x = 0) {k : ℕ} (hk : n ≤ k) : I ^ k = I ^ n :=
  pow_eq_pow_of_pow_succ_eq_pow (pow_succ_eq_pow_of_forall_mul_eq_zero hi h) hk

end Ring

end Ideal
