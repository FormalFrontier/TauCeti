/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Associated
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Squarefree elements, squares, and squarefree parts

This file records a few general facts about squarefree elements, squares, and rational squares
that Mathlib does not provide directly, used across the multiquadratic development.

* `Squarefree.not_isSquare`: a squarefree non-unit of a monoid is not a square (the converse of
  Mathlib's `IsUnit.squarefree`). It is phrased with `Squarefree` dot-notation, so a caller
  holding `ha : Squarefree a` and `hu : ¬ IsUnit a` can write `ha.not_isSquare hu`.
* `Squarefree.neg`: negation preserves squarefreeness in any ring with distributive negation.
* `not_isSquare_intCast_of_squarefree_of_ne_one`: a squarefree integer other than `1` is not a
  rational square.
* `isSquare_mul_sq_iff`: in a commutative group with zero, multiplying by a nonzero square does
  not change squareness — the statement that squareness depends only on the square class.
* `Int.exists_squarefree_mul_sq` and `Rat.exists_squarefree_int_mul_sq`: the **squarefree part**.
  Every nonzero integer, and every nonzero rational, is a squarefree *integer* times a nonzero
  square. Mathlib has this for the natural numbers only (`Nat.sq_mul_squarefree`); these are the
  integer and rational forms, which is what a square-class argument over `ℚ` needs.
* `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_squarefree`: squarefreeness of *every* prime
  divisor of an `n > 2`, read in a commutative ring, yields the single branch that Mathlib's
  `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt` splits into. This is the bridge from a
  uniform hypothesis, which a caller can usually establish without knowing `n`, to the sharp
  branch-dependent one that a proof consumes.
-/

public section

/-- A squarefree non-unit of a monoid is not a square. -/
theorem Squarefree.not_isSquare {R : Type*} [Monoid R] {a : R}
    (ha : Squarefree a) (hu : ¬ IsUnit a) : ¬ IsSquare a := by
  rintro ⟨r, rfl⟩
  exact hu ((ha r dvd_rfl).mul (ha r dvd_rfl))

/-- Negation preserves squarefreeness in any monoid with distributive negation. -/
theorem Squarefree.neg {R : Type*} [Monoid R] [HasDistribNeg R] {n : R}
    (hn : Squarefree n) : Squarefree (-n) :=
  ((Associated.refl n).neg_left).squarefree_iff.mpr hn

/-- A squarefree integer other than `1` is not a rational square. -/
theorem not_isSquare_intCast_of_squarefree_of_ne_one {n : ℤ}
    (hsf : Squarefree n) (hne : n ≠ 1) : ¬ IsSquare ((n : ℤ) : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  rintro ⟨a, ha⟩
  have hu : IsUnit a := hsf a (ha ▸ dvd_rfl)
  rcases Int.isUnit_iff.mp hu with rfl | rfl <;> simp_all

/-- **Squareness depends only on the square class.** Multiplying by the square of a nonzero
element does not change whether an element is a square. -/
theorem isSquare_mul_sq_iff {G₀ : Type*} [CommGroupWithZero G₀] {x y : G₀} (hy : y ≠ 0) :
    IsSquare (x * y ^ 2) ↔ IsSquare x := by
  refine ⟨fun h => ?_, fun h => h.mul (IsSquare.sq y)⟩
  have h' := h.mul (IsSquare.sq y⁻¹)
  rwa [mul_assoc, ← mul_pow, mul_inv_cancel₀ hy, one_pow, mul_one] at h'

/-- **The squarefree part of an integer.** Every nonzero integer is a squarefree integer times the
square of a nonzero integer. This is the integer form of Mathlib's `Nat.sq_mul_squarefree`; the
sign is carried by the squarefree factor. -/
theorem Int.exists_squarefree_mul_sq {n : ℤ} (hn : n ≠ 0) :
    ∃ a b : ℤ, Squarefree a ∧ b ≠ 0 ∧ n = a * b ^ 2 := by
  obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n.natAbs
  have habZ : (n.natAbs : ℤ) = (a : ℤ) * (b : ℤ) ^ 2 := by
    rw [← hab]; push_cast; ring
  have hb : (b : ℤ) ≠ 0 := by
    rintro hb0
    refine hn (Int.natAbs_eq_zero.mp ?_)
    have h0 : (n.natAbs : ℤ) = 0 := by rw [habZ, hb0]; ring
    exact_mod_cast h0
  have haZ : Squarefree (a : ℤ) := Int.squarefree_natCast.mpr ha
  rcases Int.natAbs_eq n with h | h
  · exact ⟨(a : ℤ), (b : ℤ), haZ, hb, by rw [h, habZ]⟩
  · exact ⟨-(a : ℤ), (b : ℤ), haZ.neg, hb, by rw [h, habZ]; ring⟩

/-- **The squarefree part of a rational number.** Every nonzero rational is a squarefree *integer*
times the square of a nonzero rational: its square class is represented by a squarefree integer.
This is what lets a square-class argument over `ℚ` work with squarefree integer radicands. -/
theorem Rat.exists_squarefree_int_mul_sq {q : ℚ} (hq : q ≠ 0) :
    ∃ (a : ℤ) (c : ℚ), Squarefree a ∧ c ≠ 0 ∧ q = a * c ^ 2 := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  obtain ⟨a, b, ha, hb, hab⟩ :=
    Int.exists_squarefree_mul_sq (n := q.num * (q.den : ℤ))
      (mul_ne_zero (Rat.num_ne_zero.mpr hq) (by exact_mod_cast q.den_ne_zero))
  refine ⟨a, (b : ℚ) / (q.den : ℚ), ha, div_ne_zero (by exact_mod_cast hb) hden, ?_⟩
  have habQ : (q.num : ℚ) * (q.den : ℚ) = (a : ℚ) * (b : ℚ) ^ 2 := by exact_mod_cast hab
  have hnum : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hden).mp (Rat.num_div_den q)
  rw [hnum] at habQ
  field_simp
  linear_combination habQ

namespace Nat

/-- **From uniform squarefreeness to the sharp branch.** If every prime dividing `n > 2` is
squarefree in `R`, then either `4 ∣ n` and `2` is squarefree there, or some *odd* prime divides
`n` and is squarefree there.

Mathlib's `Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt` supplies the dichotomy on `n`; what
this adds is carrying the squarefreeness through it. The point of stating it is that the two
hypotheses differ in usability: the uniform one can be established with no knowledge of `n` — over
`ℤ` it is free, since every rational prime is squarefree — while the branch-dependent one is what a
proof consumes. Anything proved from the sharp form is therefore available from the uniform form
through this lemma. -/
theorem four_dvd_or_exists_odd_prime_and_dvd_of_squarefree {R : Type*} [CommRing R] {n : ℕ}
    (hn : 2 < n) (hsf : ∀ p : ℕ, p.Prime → p ∣ n → Squarefree ((p : ℤ) : R)) :
    (4 ∣ n ∧ Squarefree (2 : R)) ∨
      ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ n ∧ Squarefree ((p : ℤ) : R) := by
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt hn with h4 | ⟨p, hp, hpn, hodd⟩
  · exact Or.inl ⟨h4, by simpa using hsf 2 Nat.prime_two (dvd_trans ⟨2, rfl⟩ h4)⟩
  · have hp_ne_two : p ≠ 2 := by rintro rfl; rw [Nat.odd_iff] at hodd; omega
    exact Or.inr ⟨p, hp, hp_ne_two, hpn, hsf p hp hpn⟩

end Nat
