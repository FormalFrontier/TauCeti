/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.RingTheory.Int.Basic

/-!
# Odd prime discriminants

The genus-field layer of the multiquadratic roadmap uses **prime discriminants** rather than
bare squarefree radicands. For an odd prime `p`, the associated prime discriminant is

* `p` when `p ≡ 1 (mod 4)`;
* `-p` when `p ≡ 3 (mod 4)`.

This file records that elementary normalization as a small arithmetic API. The even prime
discriminants `-4`, `8`, and `-8` are deliberately left to the later quadratic-discriminant
packaging; the odd-prime case is the reusable piece needed to turn the roadmap's odd ramified
primes into radicands `p*` satisfying `p* ≡ 1 (mod 4)`.

## Main definitions and results

* `TauCeti.Multiquadratic.oddPrimeDiscriminant`: the integer `p` if `p % 4 = 1`, and `-p`
  otherwise.
* `TauCeti.Multiquadratic.oddPrimeDiscriminant_natAbs`: its absolute value is `p`.
* `TauCeti.Multiquadratic.prime_oddPrimeDiscriminant`: it is a prime integer.
* `TauCeti.Multiquadratic.dvd_oddPrimeDiscriminant_iff`: divisibility by `p*` is the same as
  divisibility by `p`.
* `TauCeti.Multiquadratic.oddPrimeDiscriminant_mod_four_eq_one`: for odd `p`, it is `1 mod 4`.
* `TauCeti.Multiquadratic.oddPrimeDiscriminant_eq_neg_one_pow_pred_div_two_mul`: the standard
  formula `p* = (-1)^((p-1)/2) p`.
* `TauCeti.Multiquadratic.oddPrimeDiscriminant_eq_neg_one_pow_div_two_mul`: the equivalent
  formula `p* = (-1)^(p/2) p`.
-/

public section

namespace TauCeti.Multiquadratic

/-- The odd prime discriminant `p*`: `p` when `p % 4 = 1` and `-p` otherwise (so the value is
`-p` for every `p` with `p % 4 ≠ 1`, including even inputs). The `p ≡ 3 (mod 4)` reading of the
second case is the intended one for odd primes. The primality hypothesis is not part of the
definition so that the expression rewrites by computation; the API below supplies the
prime-specific facts. -/
@[expose] def oddPrimeDiscriminant (p : ℕ) : ℤ :=
  if p % 4 = 1 then p else -(p : ℤ)

/-- The defining `if` expression for the odd prime discriminant. -/
theorem oddPrimeDiscriminant_def (p : ℕ) :
    oddPrimeDiscriminant p = if p % 4 = 1 then (p : ℤ) else -(p : ℤ) := rfl

/-- If `p ≡ 1 (mod 4)`, its odd prime discriminant is `p`. -/
@[simp] theorem oddPrimeDiscriminant_of_mod_four_eq_one {p : ℕ} (hp : p % 4 = 1) :
    oddPrimeDiscriminant p = p := by
  simp [oddPrimeDiscriminant, hp]

/-- If `p ≠ 1 (mod 4)`, its odd prime discriminant is `-p`. For an odd prime this is the
`p ≡ 3 (mod 4)` case. -/
@[simp] theorem oddPrimeDiscriminant_of_mod_four_ne_one {p : ℕ} (hp : p % 4 ≠ 1) :
    oddPrimeDiscriminant p = -(p : ℤ) := by
  simp [oddPrimeDiscriminant, hp]

/-- If `p ≡ 3 (mod 4)`, its odd prime discriminant is `-p`. -/
theorem oddPrimeDiscriminant_of_mod_four_eq_three {p : ℕ} (hp : p % 4 = 3) :
    oddPrimeDiscriminant p = -(p : ℤ) :=
  oddPrimeDiscriminant_of_mod_four_ne_one (by omega)

/-- The absolute value of the odd prime discriminant is the underlying natural number. -/
@[simp] theorem oddPrimeDiscriminant_natAbs (p : ℕ) : (oddPrimeDiscriminant p).natAbs = p := by
  by_cases hp : p % 4 = 1 <;> simp [oddPrimeDiscriminant, hp]

/-- The odd prime discriminant is nonzero exactly when `p` is nonzero. -/
@[simp] theorem oddPrimeDiscriminant_ne_zero {p : ℕ} :
    oddPrimeDiscriminant p ≠ 0 ↔ p ≠ 0 := by
  rw [← Int.natAbs_ne_zero, oddPrimeDiscriminant_natAbs]

/-- The odd prime discriminant of a natural prime is a prime integer. -/
theorem prime_oddPrimeDiscriminant {p : ℕ} (hp : p.Prime) :
    Prime (oddPrimeDiscriminant p) := by
  rw [Int.prime_iff_natAbs_prime, oddPrimeDiscriminant_natAbs]
  exact hp

/-- The odd prime discriminant of a squarefree natural number is squarefree. -/
theorem squarefree_oddPrimeDiscriminant {p : ℕ} (hp : Squarefree p) :
    Squarefree (oddPrimeDiscriminant p) := by
  rw [← Int.squarefree_natAbs, oddPrimeDiscriminant_natAbs]
  exact hp

/-- The odd prime discriminant divides an integer exactly when `p` does. -/
@[simp] theorem oddPrimeDiscriminant_dvd_iff {p : ℕ} {D : ℤ} :
    oddPrimeDiscriminant p ∣ D ↔ (p : ℤ) ∣ D := by
  by_cases hp : p % 4 = 1
  · rw [oddPrimeDiscriminant_of_mod_four_eq_one hp]
  · rw [oddPrimeDiscriminant_of_mod_four_ne_one hp, neg_dvd]

/-- An integer divides an odd prime discriminant exactly when it divides the underlying
natural number. This form is convenient when checking the unramifiedness side of the
splitting law. -/
@[simp] theorem dvd_oddPrimeDiscriminant_iff {p : ℕ} {q : ℤ} :
    q ∣ oddPrimeDiscriminant p ↔ q ∣ (p : ℤ) := by
  by_cases hp : p % 4 = 1
  · rw [oddPrimeDiscriminant_of_mod_four_eq_one hp]
  · rw [oddPrimeDiscriminant_of_mod_four_ne_one hp, Int.dvd_neg]

/-- An integer does not divide an odd prime discriminant exactly when it does not divide the
underlying natural number.
The negated form is convenient for the unramifiedness side of the splitting law. -/
theorem not_dvd_oddPrimeDiscriminant_iff {p : ℕ} {q : ℤ} :
    ¬ q ∣ oddPrimeDiscriminant p ↔ ¬ q ∣ (p : ℤ) := by
  exact not_congr dvd_oddPrimeDiscriminant_iff

/-- Family form of unramifiedness for odd prime discriminants: an integer divides none of
the `p i*` exactly when it divides none of the underlying `p i`. -/
theorem forall_not_dvd_oddPrimeDiscriminant_iff {ι : Type*} (p : ι → ℕ) {q : ℤ} :
    (∀ i, ¬ q ∣ oddPrimeDiscriminant (p i)) ↔
      ∀ i, ¬ q ∣ (p i : ℤ) := by
  simp_rw [not_dvd_oddPrimeDiscriminant_iff]

/-- The odd prime discriminant of an odd natural number is odd. -/
theorem odd_oddPrimeDiscriminant {p : ℕ} (hp : Odd p) :
    Odd (oddPrimeDiscriminant p) := by
  rw [← Int.not_even_iff_odd, even_iff_two_dvd, dvd_oddPrimeDiscriminant_iff]
  exact fun h => Nat.not_even_iff_odd.mpr hp (by
    simpa [even_iff_two_dvd] using Int.natCast_dvd_natCast.mp h)

/-- An odd natural number is `1` or `3` modulo `4`. -/
private theorem mod_four_eq_one_or_three_of_odd {p : ℕ} (hp : Odd p) :
    p % 4 = 1 ∨ p % 4 = 3 :=
  Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hp)

/-- For an odd `p`, the odd prime discriminant is congruent to `1` modulo `4`. -/
@[simp] theorem oddPrimeDiscriminant_mod_four_eq_one {p : ℕ} (hp : Odd p) :
    oddPrimeDiscriminant p % 4 = 1 := by
  rcases mod_four_eq_one_or_three_of_odd hp with hp1 | hp3
  · rw [oddPrimeDiscriminant_of_mod_four_eq_one hp1]
    exact_mod_cast hp1
  · rw [oddPrimeDiscriminant_of_mod_four_eq_three hp3]
    have hp3z : (p : ℤ) % 4 = 3 := by
      exact_mod_cast hp3
    omega

/-- The odd prime discriminant is always either `p` or `-p`. -/
theorem oddPrimeDiscriminant_eq_or_eq_neg {p : ℕ} :
    oddPrimeDiscriminant p = (p : ℤ) ∨ oddPrimeDiscriminant p = -(p : ℤ) := by
  by_cases hp : p % 4 = 1
  · exact Or.inl (oddPrimeDiscriminant_of_mod_four_eq_one hp)
  · exact Or.inr (oddPrimeDiscriminant_of_mod_four_ne_one hp)

/-- The sign of the odd prime discriminant is controlled by `p mod 4`. -/
theorem oddPrimeDiscriminant_pos_iff {p : ℕ} :
    0 < oddPrimeDiscriminant p ↔ p % 4 = 1 := by
  by_cases hmod : p % 4 = 1
  · rw [oddPrimeDiscriminant_of_mod_four_eq_one hmod]
    have hp : p ≠ 0 := by omega
    constructor
    · intro _; exact hmod
    · intro _; exact_mod_cast Nat.pos_of_ne_zero hp
  · rw [oddPrimeDiscriminant_of_mod_four_ne_one hmod]
    constructor
    · intro hpos
      omega
    · intro h
      omega

/-- The odd prime discriminant is negative exactly in the `p ≡ 3 (mod 4)` case. -/
theorem oddPrimeDiscriminant_neg_iff {p : ℕ} (hp : Odd p) :
    oddPrimeDiscriminant p < 0 ↔ p % 4 = 3 := by
  rcases mod_four_eq_one_or_three_of_odd hp with hp1 | hp3
  · have hpos : (0 : ℤ) < p := by
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    rw [oddPrimeDiscriminant_of_mod_four_eq_one hp1]
    exact ⟨fun hneg => by omega, fun h => by omega⟩
  · have hpos : (0 : ℤ) < p := by
      exact_mod_cast Nat.pos_of_ne_zero (by omega)
    rw [oddPrimeDiscriminant_of_mod_four_eq_three hp3]
    exact ⟨fun _ => hp3, fun _ => neg_neg_of_pos hpos⟩

/-- The odd prime discriminant in the standard notation `p* = (-1)^(p/2) p`. -/
theorem oddPrimeDiscriminant_eq_neg_one_pow_div_two_mul {p : ℕ} (hp : Odd p) :
    oddPrimeDiscriminant p = (-1 : ℤ) ^ (p / 2) * p := by
  rcases mod_four_eq_one_or_three_of_odd hp with hp1 | hp3
  · rw [oddPrimeDiscriminant_of_mod_four_eq_one hp1,
      ZMod.neg_one_pow_div_two_of_one_mod_four hp1]
    simp
  · rw [oddPrimeDiscriminant_of_mod_four_eq_three hp3,
      ZMod.neg_one_pow_div_two_of_three_mod_four hp3]
    simp

/-- The odd prime discriminant in the standard notation
`p* = (-1)^((p - 1)/2) p`. -/
theorem oddPrimeDiscriminant_eq_neg_one_pow_pred_div_two_mul {p : ℕ} (hp : Odd p) :
    oddPrimeDiscriminant p = (-1 : ℤ) ^ ((p - 1) / 2) * p := by
  rw [oddPrimeDiscriminant_eq_neg_one_pow_div_two_mul hp]
  congr 2
  rcases hp with ⟨k, rfl⟩
  omega

end TauCeti.Multiquadratic
