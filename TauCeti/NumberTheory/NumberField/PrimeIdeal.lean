/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.ClassGroup.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Prime ideals of rings of integers

This file records general utilities for choosing prime ideals of a number field above rational
primes and packaging them as non-zero-divisors so that their classes can be taken with
`ClassGroup.mk0`.

## Main results

* `NumberField.mem_nonZeroDivisors_of_prime_of_liesOver`: a prime ideal above a rational prime is
  a non-zero-divisor in the ideal monoid.
* `NumberField.exists_primeIdealFamily`: a finite set of rational primes admits a family of prime
  ideals above it, packaged for `ClassGroup.mk0`.
* `TauCeti.NumberField.card_primesOverFinset_le_finrank`: at most `[K : ℚ]` primes of `𝓞 K`
  lie over a nonzero prime of `ℤ`.
-/

public section

open NumberField Ideal
open scoped NumberField nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- An ideal lying over a rational prime is a non-zero-divisor in the ideal monoid, so it can be
passed to `ClassGroup.mk0`. -/
theorem mem_nonZeroDivisors_of_prime_of_liesOver {p : ℕ} (hp : p.Prime)
    (𝔭 : Ideal (𝓞 K)) [𝔭.LiesOver (span {(p : ℤ)})] :
    𝔭 ∈ nonZeroDivisors (Ideal (𝓞 K)) := by
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [Ideal.zero_eq_bot]
  exact Ideal.ne_bot_of_liesOver_of_ne_bot (p := span {(p : ℤ)})
    (by rw [ne_eq, Ideal.span_singleton_eq_bot, Int.natCast_eq_zero]
        exact hp.pos.ne') 𝔭

/-- A finite set of rational primes admits a family of prime ideals above it, packaged as
non-zero-divisors so their classes can be taken with `ClassGroup.mk0`. Away from the specified
finite set the family is filled with the unit ideal. -/
theorem exists_primeIdealFamily (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∃ Q : (ℕ → (Ideal (𝓞 K))⁰),
      (∀ p ∈ s, (Q p : Ideal (𝓞 K)).IsPrime) ∧
        ∀ p ∈ s, (Q p : Ideal (𝓞 K)).LiesOver (span {(p : ℤ)}) := by
  classical
  have hex : ∀ p, p ∈ s → ∃ Q : (Ideal (𝓞 K))⁰,
      (Q : Ideal (𝓞 K)).IsPrime ∧ (Q : Ideal (𝓞 K)).LiesOver (span {(p : ℤ)}) := by
    intro p hp
    let _ : Fact p.Prime := ⟨hs p hp⟩
    obtain ⟨𝔭, hprime, hover⟩ :=
      (inferInstance : Nonempty ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)))
    let _ := hprime
    let _ := hover
    exact ⟨⟨𝔭, mem_nonZeroDivisors_of_prime_of_liesOver (hs p hp) 𝔭⟩, hprime, hover⟩
  choose Q hprime hover using hex
  let Q' : ℕ → (Ideal (𝓞 K))⁰ := fun p ↦ if hp : p ∈ s then Q p hp else 1
  refine ⟨Q', ?_, ?_⟩
  · intro p hp
    simpa [Q', hp] using hprime p hp
  · intro p hp
    simpa [Q', hp] using hover p hp

end NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- At most `[K : ℚ]` primes of `𝓞 K` lie over a given nonzero prime of `ℤ`, since each
contributes a positive `ramificationIdx * inertiaDeg` to the fundamental identity. -/
theorem card_primesOverFinset_le_finrank {p : Ideal ℤ} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    (IsDedekindDomain.primesOverFinset p (𝓞 K)).card ≤ Module.finrank ℚ K :=
  calc
    (IsDedekindDomain.primesOverFinset p (𝓞 K)).card = ∑ _q : p.primesOver (𝓞 K), 1 := by
      rw [Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ,
        ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq,
        ← IsDedekindDomain.coe_primesOverFinset hp0 (𝓞 K), Set.ncard_coe_finset]
    _ ≤ ∑ q : p.primesOver (𝓞 K), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ :=
      Finset.sum_le_sum fun q _ => Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne'
          (Ideal.inertiaDeg_pos q.1 ℤ).ne')
    _ = Module.finrank ℤ (𝓞 K) := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 K)
    _ = Module.finrank ℚ K := _root_.NumberField.RingOfIntegers.rank K

end TauCeti.NumberField
