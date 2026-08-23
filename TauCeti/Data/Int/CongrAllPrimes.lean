/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Infinite

/-!
# Integers pinned by their residues at all but one prime

An integer divisible by every prime except possibly one is zero, and consequently two integers
congruent modulo every prime except possibly one are equal. A nonzero integer has finitely many
prime divisors while the excluded primes are infinite in number, so some prime both divides it
and exceeds its absolute value.

The exception is what makes these usable: an argument that produces congruences one prime at a
time is typically forced to omit a characteristic, and may omit it without weakening the
conclusion. `TauCeti.Matrix.eq_quadratic_form_of_det_trace` is such an argument.

## Main results

* `Int.eq_zero_of_dvd_all_primes_ne`: an integer divisible by every prime `≠ p` is zero.
* `Int.eq_of_intCast_eq_all_primes_ne`: two integers agreeing in `ZMod ℓ` for every prime `ℓ ≠ p`
  are equal.

## Provenance

Ported from the AINTLIB `HasseWeil` project (Apache-2.0), revision `513e83879e2f`, file
`HasseWeil/WeilPairing/IntegerSeparation.lean`, declarations `int_eq_zero_of_dvd_all_primes_ne`
and `int_eq_of_congr_all_primes_ne`. Both statements are unchanged; the names follow Mathlib's
convention of naming after the conclusion, and the proofs are shortened — the first by
`Nat.exists_infinite_primes` at a single bound rather than a `max` of two, the second by
`sub_eq_zero` in place of `omega`.
-/

public section

namespace Int

/-- **An integer divisible by every prime except possibly one is zero.**

A nonzero integer is divisible only by primes at most its absolute value, but the primes `≠ p`
are unbounded, so one of them both divides it and exceeds it. -/
theorem eq_zero_of_dvd_all_primes_ne {D : ℤ} {p : ℕ}
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → (ℓ : ℤ) ∣ D) : D = 0 := by
  by_contra hD
  obtain ⟨ℓ, hℓ_ge, hℓ_prime⟩ := Nat.exists_infinite_primes (max (D.natAbs + 1) (p + 1))
  have hle : ℓ ≤ D.natAbs :=
    Nat.le_of_dvd (natAbs_pos.mpr hD) <| by
      simpa using natAbs_dvd_natAbs.mpr (h ℓ hℓ_prime (by omega))
  omega

/-- **Two integers agreeing modulo every prime except possibly one are equal.** -/
theorem eq_of_intCast_eq_all_primes_ne {A B : ℤ} {p : ℕ}
    (h : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → (A : ZMod ℓ) = (B : ZMod ℓ)) : A = B :=
  sub_eq_zero.mp <| eq_zero_of_dvd_all_primes_ne (p := p) fun ℓ hℓ hℓne ↦ by
    have : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ |>.mp <| by
      rw [Int.cast_sub, h ℓ hℓ hℓne, sub_self]

end Int
