/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.NormNum.IsSquare

/-!
# Even prime discriminants

The genus-field layer of the multiquadratic roadmap uses the prime discriminants dividing a
quadratic discriminant. The odd-prime normalization `p*` is developed in
`TauCeti.NumberTheory.Multiquadratic.Prime.Discriminant.Basic`; this file records the complementary
2-adic list:

* `-4`, represented by the squarefree radicand `-1`;
* `8`, represented by the squarefree radicand `2`;
* `-8`, represented by the squarefree radicand `-2`.

The quotient by `4` is the radicand whose square root generates the same quadratic field as
the corresponding even prime discriminant. This is the small arithmetic API needed before the
later genus-field package can form the multiquadratic compositum of the `ℚ(√p*)` factors.

## Main definitions and results

* `TauCeti.Multiquadratic.IsEvenPrimeDiscriminant`: membership in the finite set
  `{-4, 8, -8}`.
* `TauCeti.Multiquadratic.evenPrimeDiscriminantRadicand`: the radicand `D / 4`.
* `TauCeti.Multiquadratic.evenPrimeDiscriminant_eq_four_mul_radicand`: reconstructs `D`
  from its radicand for the three even prime discriminants.
* `TauCeti.Multiquadratic.squarefree_evenPrimeDiscriminantRadicand`: the radicand is
  squarefree.
* `TauCeti.Multiquadratic.not_isSquare_evenPrimeDiscriminantRadicand_rat`: the associated
  rational radicand is not a square.
-/

public section

namespace TauCeti.Multiquadratic

/-- The three even prime discriminants: `-4`, `8`, and `-8`. -/
@[expose] def IsEvenPrimeDiscriminant (D : ℤ) : Prop :=
  D = -4 ∨ D = 8 ∨ D = -8

/-- The defining disjunction for `IsEvenPrimeDiscriminant`. -/
theorem isEvenPrimeDiscriminant_iff {D : ℤ} :
    IsEvenPrimeDiscriminant D ↔ D = -4 ∨ D = 8 ∨ D = -8 :=
  Iff.rfl

@[simp] theorem isEvenPrimeDiscriminant_neg_four :
    IsEvenPrimeDiscriminant (-4) :=
  Or.inl rfl

@[simp] theorem isEvenPrimeDiscriminant_eight :
    IsEvenPrimeDiscriminant 8 :=
  Or.inr (Or.inl rfl)

@[simp] theorem isEvenPrimeDiscriminant_neg_eight :
    IsEvenPrimeDiscriminant (-8) :=
  Or.inr (Or.inr rfl)

/-- The squarefree radicand associated to an even prime discriminant. For `D = -4, 8, -8`
this gives respectively `-1, 2, -2`. -/
def evenPrimeDiscriminantRadicand (D : ℤ) : ℤ :=
  D / 4

@[simp] theorem evenPrimeDiscriminantRadicand_neg_four :
    evenPrimeDiscriminantRadicand (-4) = -1 := by
  norm_num [evenPrimeDiscriminantRadicand]

@[simp] theorem evenPrimeDiscriminantRadicand_eight :
    evenPrimeDiscriminantRadicand 8 = 2 := by
  norm_num [evenPrimeDiscriminantRadicand]

@[simp] theorem evenPrimeDiscriminantRadicand_neg_eight :
    evenPrimeDiscriminantRadicand (-8) = -2 := by
  norm_num [evenPrimeDiscriminantRadicand]

/-- An even prime discriminant is four times its associated squarefree radicand. -/
theorem evenPrimeDiscriminant_eq_four_mul_radicand {D : ℤ} (hD : IsEvenPrimeDiscriminant D) :
    D = 4 * evenPrimeDiscriminantRadicand D := by
  rcases hD with rfl | rfl | rfl <;> norm_num [evenPrimeDiscriminantRadicand]

/-- The associated squarefree radicand of an even prime discriminant is one of `-1`, `2`,
or `-2`. -/
theorem evenPrimeDiscriminantRadicand_eq_neg_one_or_eq_two_or_eq_neg_two {D : ℤ}
    (hD : IsEvenPrimeDiscriminant D) :
    evenPrimeDiscriminantRadicand D = -1 ∨
      evenPrimeDiscriminantRadicand D = 2 ∨
        evenPrimeDiscriminantRadicand D = -2 := by
  rcases hD with rfl | rfl | rfl <;> simp

/-- The absolute value of the radicand attached to an even prime discriminant is `1` or `2`. -/
theorem evenPrimeDiscriminantRadicand_natAbs_eq_one_or_two {D : ℤ}
    (hD : IsEvenPrimeDiscriminant D) : (evenPrimeDiscriminantRadicand D).natAbs = 1 ∨
      (evenPrimeDiscriminantRadicand D).natAbs = 2 := by
  rcases hD with rfl | rfl | rfl <;> simp

/-- The radicand attached to an even prime discriminant is nonzero. -/
theorem evenPrimeDiscriminantRadicand_ne_zero {D : ℤ} (hD : IsEvenPrimeDiscriminant D) :
    evenPrimeDiscriminantRadicand D ≠ 0 := by
  rcases hD with rfl | rfl | rfl <;> simp

/-- The radicand attached to an even prime discriminant is squarefree. -/
theorem squarefree_evenPrimeDiscriminantRadicand {D : ℤ} (hD : IsEvenPrimeDiscriminant D) :
    Squarefree (evenPrimeDiscriminantRadicand D) := by
  rcases hD with rfl | rfl | rfl
  · norm_num
  · rw [evenPrimeDiscriminantRadicand_eight, ← Int.squarefree_natAbs]
    exact Nat.prime_two.squarefree
  · rw [evenPrimeDiscriminantRadicand_neg_eight, ← Int.squarefree_natAbs]
    exact Nat.prime_two.squarefree

/-- The even prime discriminants themselves are even. -/
theorem two_dvd_evenPrimeDiscriminant {D : ℤ} (hD : IsEvenPrimeDiscriminant D) : (2 : ℤ) ∣ D := by
  rcases hD with rfl | rfl | rfl <;> norm_num

/-- The radicand attached to an even prime discriminant is congruent to `-1` or `2`
modulo `4`. -/
theorem evenPrimeDiscriminantRadicand_mod_four_eq_three_or_two {D : ℤ}
    (hD : IsEvenPrimeDiscriminant D) :
    evenPrimeDiscriminantRadicand D % 4 = 3 ∨
      evenPrimeDiscriminantRadicand D % 4 = 2 := by
  rcases hD with rfl | rfl | rfl <;> norm_num

/-- The rational radicand associated to an even prime discriminant is not a square. -/
theorem not_isSquare_evenPrimeDiscriminantRadicand_rat {D : ℤ} (hD : IsEvenPrimeDiscriminant D) :
    ¬ IsSquare ((evenPrimeDiscriminantRadicand D : ℤ) : ℚ) := by
  rcases hD with rfl | rfl | rfl <;> norm_num [evenPrimeDiscriminantRadicand]

/-- The discriminant `-4` gives the radicand `-1`. -/
theorem evenPrimeDiscriminantRadicand_eq_neg_one_iff {D : ℤ} (hD : IsEvenPrimeDiscriminant D) :
    evenPrimeDiscriminantRadicand D = -1 ↔ D = -4 := by
  rcases hD with rfl | rfl | rfl <;> norm_num

/-- The discriminant `8` gives the radicand `2`. -/
theorem evenPrimeDiscriminantRadicand_eq_two_iff {D : ℤ} (hD : IsEvenPrimeDiscriminant D) :
    evenPrimeDiscriminantRadicand D = 2 ↔ D = 8 := by
  rcases hD with rfl | rfl | rfl <;> norm_num

/-- The discriminant `-8` gives the radicand `-2`. -/
theorem evenPrimeDiscriminantRadicand_eq_neg_two_iff {D : ℤ} (hD : IsEvenPrimeDiscriminant D) :
    evenPrimeDiscriminantRadicand D = -2 ↔ D = -8 := by
  rcases hD with rfl | rfl | rfl <;> norm_num

end TauCeti.Multiquadratic
