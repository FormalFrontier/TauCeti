/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.EvenPrimeDiscriminant
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
-- `SquareClass` supplies `legendreSym_mul_sq`, used only inside a proof below, so it is not
-- re-exported.
import TauCeti.NumberTheory.LegendreSymbol.SquareClass

/-!
# Legendre symbols of even prime discriminants

The genus-field layer of the multiquadratic roadmap normalizes the radicands of a quadratic
discriminant to **prime discriminants**. The odd prime discriminants `p* = (-1)^((p-1)/2) p`
are handled in `TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminant.Basic`, where the
splitting symbol is governed by quadratic reciprocity. This file records the complementary
**even** list `-4, 8, -8` (radicands `-1, 2, -2`), whose splitting at an odd prime `q` is
governed not by reciprocity but by the supplementary laws: the quadratic characters `χ₄`,
`χ₈`, and `χ₈'` on `q`.

Concretely, for an odd prime `q`,
* `(-1 / q) = χ₄ q`, the radicand of `-4`;
* `(2 / q) = χ₈ q`, the radicand of `8`;
* `(-2 / q) = χ₈' q`, the radicand of `-8`.

Since an even prime discriminant `D` is four times its radicand and `4` is a square, the
Legendre symbol of `D` itself agrees with that of its radicand at every odd prime; this is
what lets the genus field use the prime discriminant `D` as the splitting character.

## Main results

* `TauCeti.Multiquadratic.legendreSym_evenPrimeDiscriminantRadicand` expands the Legendre
  symbol of an even prime-discriminant radicand at an odd prime as the appropriate
  supplementary character.
* `TauCeti.Multiquadratic.legendreSym_evenPrimeDiscriminant_eq_legendreSym_radicand` shows
  that an even prime discriminant and its radicand have the same Legendre symbol at every
  odd prime.
* `legendreSym_evenPrimeDiscriminantRadicand_neg_four_eq_one_iff`,
  `..._eight_eq_one_iff`, and `..._neg_eight_eq_one_iff` give the quadratic-residue
  (splitting) conditions as congruences on `q` modulo `4` or `8`.
* `legendreSym_evenPrimeDiscriminant_neg_four_eq_one_iff`,
  `..._eight_eq_one_iff`, and `..._neg_eight_eq_one_iff` give the same conditions for the
  prime discriminants themselves.
-/

public section

namespace TauCeti.Multiquadratic

open ZMod

variable {q : ℕ} [Fact q.Prime]

/-- If `q` is an odd natural prime, then it does not divide `2` as an integer. -/
private theorem not_intCast_prime_dvd_two (hq : q ≠ 2) : ¬ (q : ℤ) ∣ (2 : ℤ) := by
  intro hdvd
  exact hq ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
    (Int.natCast_dvd_natCast.mp hdvd))

/-- The Legendre symbol of an even prime-discriminant radicand at an odd prime `q` is the
supplementary character attached to that discriminant: `χ₄ q` for `-4` (radicand `-1`),
`χ₈ q` for `8` (radicand `2`), and `χ₈' q` for `-8` (radicand `-2`). -/
theorem legendreSym_evenPrimeDiscriminantRadicand {D : ℤ} (hD : IsEvenPrimeDiscriminant D)
    (hq : q ≠ 2) :
    legendreSym q (evenPrimeDiscriminantRadicand D) =
      if D = -4 then χ₄ q else if D = 8 then χ₈ q else χ₈' q := by
  rcases hD with rfl | rfl | rfl
  · rw [evenPrimeDiscriminantRadicand_neg_four, if_pos rfl, legendreSym.at_neg_one hq]
  · rw [evenPrimeDiscriminantRadicand_eight, if_neg (by norm_num), if_pos rfl,
      legendreSym.at_two hq]
  · rw [evenPrimeDiscriminantRadicand_neg_eight, if_neg (by norm_num), if_neg (by norm_num),
      legendreSym.at_neg_two hq]

/-- An even prime discriminant `D` and its radicand `D / 4` have the same Legendre symbol at
every odd prime `q`: they differ by the square factor `4`, which contributes a trivial
symbol. This is the form used by the genus-field splitting law, where the prime discriminant
`D` itself is the splitting character. -/
theorem legendreSym_evenPrimeDiscriminant_eq_legendreSym_radicand {D : ℤ}
    (hD : IsEvenPrimeDiscriminant D) (hq : q ≠ 2) :
    legendreSym q D = legendreSym q (evenPrimeDiscriminantRadicand D) := by
  have hsq : D = evenPrimeDiscriminantRadicand D * 2 ^ 2 := by
    calc
      D = 4 * evenPrimeDiscriminantRadicand D :=
        evenPrimeDiscriminant_eq_four_mul_radicand hD
      _ = evenPrimeDiscriminantRadicand D * 2 ^ 2 := by ring
  calc
    legendreSym q D = legendreSym q (evenPrimeDiscriminantRadicand D * 2 ^ 2) :=
      congrArg (legendreSym q) hsq
    _ = legendreSym q (evenPrimeDiscriminantRadicand D) :=
      legendreSym_mul_sq (p := q) (a := evenPrimeDiscriminantRadicand D)
        (u := 2) (not_intCast_prime_dvd_two hq)

/-- The radicand `-1` of the prime discriminant `-4` is a quadratic residue modulo an odd
prime `q` exactly when `q ≡ 1 (mod 4)`; equivalently `q` splits in `ℚ(√-1) = ℚ(i)`. -/
theorem legendreSym_evenPrimeDiscriminantRadicand_neg_four_eq_one_iff (hq : q ≠ 2) :
    legendreSym q (evenPrimeDiscriminantRadicand (-4)) = 1 ↔ q % 4 = 1 := by
  rw [evenPrimeDiscriminantRadicand_neg_four,
    legendreSym.eq_one_iff (p := q) (a := (-1 : ℤ))]
  · push_cast
    rw [ZMod.exists_sq_eq_neg_one_iff]
    have hodd : q % 2 = 1 := (Nat.Prime.eq_two_or_odd Fact.out).resolve_left hq
    omega
  · norm_num [ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The radicand `2` of the prime discriminant `8` is a quadratic residue modulo an odd
prime `q` exactly when `q ≡ 1` or `7 (mod 8)`; equivalently `q` splits in `ℚ(√2)`. -/
theorem legendreSym_evenPrimeDiscriminantRadicand_eight_eq_one_iff (hq : q ≠ 2) :
    legendreSym q (evenPrimeDiscriminantRadicand 8) = 1 ↔ q % 8 = 1 ∨ q % 8 = 7 := by
  rw [evenPrimeDiscriminantRadicand_eight,
    legendreSym.eq_one_iff (p := q) (a := (2 : ℤ))]
  · push_cast
    exact ZMod.exists_sq_eq_two_iff hq
  · rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact not_intCast_prime_dvd_two hq

/-- The radicand `-2` of the prime discriminant `-8` is a quadratic residue modulo an odd
prime `q` exactly when `q ≡ 1` or `3 (mod 8)`; equivalently `q` splits in `ℚ(√-2)`. -/
theorem legendreSym_evenPrimeDiscriminantRadicand_neg_eight_eq_one_iff (hq : q ≠ 2) :
    legendreSym q (evenPrimeDiscriminantRadicand (-8)) = 1 ↔ q % 8 = 1 ∨ q % 8 = 3 := by
  rw [evenPrimeDiscriminantRadicand_neg_eight,
    legendreSym.eq_one_iff (p := q) (a := (-2 : ℤ))]
  · push_cast
    exact ZMod.exists_sq_eq_neg_two_iff hq
  · rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact fun h => not_intCast_prime_dvd_two hq (dvd_neg.mp h)

/-- The radicand of a variable even prime discriminant is a quadratic residue modulo an odd
prime `q` exactly under the corresponding supplementary congruence condition. -/
theorem legendreSym_evenPrimeDiscriminantRadicand_eq_one_iff {D : ℤ}
    (hD : IsEvenPrimeDiscriminant D) (hq : q ≠ 2) :
    legendreSym q (evenPrimeDiscriminantRadicand D) = 1 ↔
      if D = -4 then q % 4 = 1
      else if D = 8 then q % 8 = 1 ∨ q % 8 = 7
      else q % 8 = 1 ∨ q % 8 = 3 := by
  rcases hD with rfl | rfl | rfl
  · rw [if_pos rfl, legendreSym_evenPrimeDiscriminantRadicand_neg_four_eq_one_iff hq]
  · rw [if_neg (by norm_num), if_pos rfl,
      legendreSym_evenPrimeDiscriminantRadicand_eight_eq_one_iff hq]
  · rw [if_neg (by norm_num), if_neg (by norm_num),
      legendreSym_evenPrimeDiscriminantRadicand_neg_eight_eq_one_iff hq]

/-- A variable even prime discriminant is a quadratic residue modulo an odd prime `q`
exactly under the corresponding supplementary congruence condition. -/
theorem legendreSym_evenPrimeDiscriminant_eq_one_iff {D : ℤ}
    (hD : IsEvenPrimeDiscriminant D) (hq : q ≠ 2) :
    legendreSym q D = 1 ↔
      if D = -4 then q % 4 = 1
      else if D = 8 then q % 8 = 1 ∨ q % 8 = 7
      else q % 8 = 1 ∨ q % 8 = 3 := by
  rw [legendreSym_evenPrimeDiscriminant_eq_legendreSym_radicand hD hq,
    legendreSym_evenPrimeDiscriminantRadicand_eq_one_iff hD hq]

/-- The prime discriminant `-4` is a quadratic residue modulo an odd prime `q` exactly when
`q ≡ 1 (mod 4)`. -/
@[simp] theorem legendreSym_evenPrimeDiscriminant_neg_four_eq_one_iff (hq : q ≠ 2) :
    legendreSym q (-4) = 1 ↔ q % 4 = 1 := by
  simpa using legendreSym_evenPrimeDiscriminant_eq_one_iff
    (q := q) (D := -4) isEvenPrimeDiscriminant_neg_four hq

/-- The prime discriminant `8` is a quadratic residue modulo an odd prime `q` exactly when
`q ≡ 1` or `7 (mod 8)`. -/
@[simp] theorem legendreSym_evenPrimeDiscriminant_eight_eq_one_iff (hq : q ≠ 2) :
    legendreSym q 8 = 1 ↔ q % 8 = 1 ∨ q % 8 = 7 := by
  simpa using legendreSym_evenPrimeDiscriminant_eq_one_iff
    (q := q) (D := 8) isEvenPrimeDiscriminant_eight hq

/-- The prime discriminant `-8` is a quadratic residue modulo an odd prime `q` exactly when
`q ≡ 1` or `3 (mod 8)`. -/
@[simp] theorem legendreSym_evenPrimeDiscriminant_neg_eight_eq_one_iff (hq : q ≠ 2) :
    legendreSym q (-8) = 1 ↔ q % 8 = 1 ∨ q % 8 = 3 := by
  simpa using legendreSym_evenPrimeDiscriminant_eq_one_iff
    (q := q) (D := -8) isEvenPrimeDiscriminant_neg_eight hq

example :
    legendreSym 3 (evenPrimeDiscriminantRadicand (-8)) = 1 :=
  (legendreSym_evenPrimeDiscriminantRadicand_neg_eight_eq_one_iff (by norm_num)).mpr (by norm_num)

example :
    legendreSym 3 (evenPrimeDiscriminantRadicand 8) ≠ 1 := by
  intro h
  rw [legendreSym_evenPrimeDiscriminantRadicand_eight_eq_one_iff (q := 3) (by norm_num)] at h
  exact absurd h (by decide)

end TauCeti.Multiquadratic
