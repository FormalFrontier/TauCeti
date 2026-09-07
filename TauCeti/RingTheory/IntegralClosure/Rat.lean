/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.GCDMonoid.IntegrallyClosed

/-!
# Rational algebraic integers

`ℤ` is integrally closed in `ℚ`, so an algebraic integer that happens to be rational is an
integer. This file records the numerical reading of that fact: an identity `n · z = m` between an
algebraic integer `z` and two natural numbers is a divisibility `n ∣ m`. It holds over an
arbitrary field of characteristic zero, `z = m / n` being the image of a rational number there and
integrality descending along `algebraMap ℚ k`.

## Main results

* `TauCeti.dvd_of_isIntegral_of_natCast_mul_eq`: if `(n : k) * z = m` with `z` integral over `ℤ`
  in a field of characteristic zero and `n ≠ 0`, then `n ∣ m`.
-/

public section

namespace TauCeti

/-- **A rational algebraic integer is an integer**, read as a divisibility: if `n · z = m` for
natural numbers `m` and `n` with `n ≠ 0`, and `z` is integral over `ℤ` in a field of characteristic
zero, then `n` divides `m`. -/
theorem dvd_of_isIntegral_of_natCast_mul_eq {k : Type*} [Field k] [CharZero k] {m n : ℕ}
    {z : k} (hz : IsIntegral ℤ z) (h : (n : k) * z = m) (hn : n ≠ 0) : n ∣ m := by
  have hnk : (n : k) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hz' : algebraMap ℚ k ((m : ℚ) / (n : ℚ)) = z := by
    rw [map_div₀, map_natCast, map_natCast, eq_comm, eq_div_iff hnk, mul_comm]
    exact h
  have hq : IsIntegral ℤ ((m : ℚ) / (n : ℚ)) :=
    isIntegral_algebraMap_iff.mp (hz' ▸ hz)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hq
  have hyq : (y : ℚ) * (n : ℚ) = (m : ℚ) := by
    rw [← eq_intCast (algebraMap ℤ ℚ) y, hy, div_mul_cancel₀]
    exact Nat.cast_ne_zero.mpr hn
  refine Int.natCast_dvd_natCast.mp ⟨y, ?_⟩
  exact_mod_cast (by linarith : (m : ℚ) = (n : ℚ) * (y : ℚ))

end TauCeti
