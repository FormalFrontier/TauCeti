/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Logic.Basic

/-!
# Prime divisibility helpers

This file collects internal NumberField bookkeeping about rational primes and
integer divisibility. The lemmas here support coprimality side conditions in
splitting computations without exposing those proof details from the main
splitting API files.
-/

public section

namespace NumberField.Internal

/-- Distinct rational primes remain coprime after casting to integers. -/
theorem not_intCast_prime_dvd_natPrime {p l : ℕ} [Fact p.Prime]
    (hl : l.Prime) (hne : p ≠ l) : ¬ (p : ℤ) ∣ (l : ℤ) := by
  intro h
  have hp_dvd_l : p ∣ l := Int.natCast_dvd_natCast.mp h
  exact hne ((Nat.prime_dvd_prime_iff_eq Fact.out hl).mp hp_dvd_l)

end NumberField.Internal
