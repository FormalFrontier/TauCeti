/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Ring.Associated
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
* `isSquare_mul_sq_iff`: in a field, multiplying by a nonzero square does not change squareness —
  the statement that squareness depends only on the square class.
* `Int.exists_squarefree_mul_sq` and `Rat.exists_squarefree_int_mul_sq`: the **squarefree part**.
  Every nonzero integer, and every nonzero rational, is a squarefree *integer* times a nonzero
  square. Mathlib has this for the natural numbers only (`Nat.sq_mul_squarefree`); these are the
  integer and rational forms, which is what a square-class argument over `ℚ` needs.
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

/-- **Squareness depends only on the square class.** In a field, multiplying by the square of a
nonzero element does not change whether an element is a square. -/
theorem isSquare_mul_sq_iff {F : Type*} [Field F] {x y : F} (hy : y ≠ 0) :
    IsSquare (x * y ^ 2) ↔ IsSquare x := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z / y, ?_⟩
    field_simp
    linear_combination hz
  · rintro ⟨z, rfl⟩
    exact ⟨z * y, by ring⟩

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
  rw [div_pow, ← mul_div_assoc, eq_div_iff (pow_ne_zero 2 hden)]
  linear_combination habQ
