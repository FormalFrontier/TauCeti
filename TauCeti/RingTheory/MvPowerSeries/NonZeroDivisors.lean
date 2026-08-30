/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-!
# The difference of two variables is a non-zero-divisor

Mathlib shows that a *single* variable is a non-zero-divisor over an arbitrary semiring
(`MvPowerSeries.X_mem_nonzeroDivisors`), and that `MvPowerSeries σ R` inherits `NoZeroDivisors`
from `R`. Between those lies a gap: over a ring that *has* zero divisors, is `X i - X j` still
regular? It is, and this file proves it.

## Main results

* `MvPowerSeries.X_sub_X_mem_nonZeroDivisors`: for `i ≠ j`, the difference `X i - X j` is a
  non-zero-divisor of `MvPowerSeries σ R` over an arbitrary commutative ring.

## Implementation notes

The proof is a coefficient recursion rather than a cancellation in `R`, which is what lets the
hypotheses on `R` drop. Reading `f * (X i - X j) = 0` at the exponent `d + single i 1` gives
`coeff d f = coeff (d + single i 1 - single j 1) f` when `d j ≠ 0`, and `coeff d f = 0` when
`d j = 0`, since the `X j` term is then absent for degree reasons. Each step lowers the
`j`-exponent by one, so induction on `d j` walks every coefficient down to that base case.
-/

public section

namespace MvPowerSeries

open Finsupp nonZeroDivisors

variable {σ R : Type*} [CommRing R]

/-- **The difference of two distinct variables is a non-zero-divisor**, over an arbitrary
commutative ring: `f * (X i - X j) = 0` forces `f = 0`, with no hypothesis on `R`.

Compare `MvPowerSeries.X_mem_nonzeroDivisors`, the same statement for a single variable, and the
`NoZeroDivisors (MvPowerSeries σ R)` instance, which requires `R` to have no zero divisors. -/
theorem X_sub_X_mem_nonZeroDivisors {i j : σ} (hij : i ≠ j) :
    X i - X j ∈ (MvPowerSeries σ R)⁰ := by
  classical
  have main : ∀ f : MvPowerSeries σ R, f * (X i - X j) = 0 → f = 0 := by
    intro f hf
    suffices H : ∀ n (d : σ →₀ ℕ), d j = n → coeff d f = 0 by
      ext d
      simpa using H (d j) d rfl
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro d hd
      have hji : single j 1 ≤ d + single i 1 ↔ d j ≠ 0 := by
        simp [Finsupp.single_le_iff, Finsupp.single_eq_of_ne (Ne.symm hij), Nat.one_le_iff_ne_zero]
      have key := congr(coeff (d + single i 1) $hf)
      rw [mul_sub, map_sub, X, X, coeff_mul_monomial, coeff_mul_monomial, map_zero] at key
      simp only [le_add_self, ite_true, add_tsub_cancel_right, mul_one] at key
      rcases Nat.eq_zero_or_pos n with hn | hn
      · have hcond : ¬ single j 1 ≤ d + single i 1 := by simp [hji, hd, hn]
        simpa [hcond] using key
      · have hcond : single j 1 ≤ d + single i 1 := hji.mpr (by omega)
        simp only [hcond, ite_true, sub_eq_zero] at key
        refine key.trans (ih (n - 1) (by omega) _ ?_)
        simp [Finsupp.tsub_apply, Finsupp.single_eq_of_ne (Ne.symm hij), hd]
  rw [mem_nonZeroDivisors_iff]
  exact ⟨fun x hx ↦ main x (by rwa [mul_comm]), main⟩

end MvPowerSeries
