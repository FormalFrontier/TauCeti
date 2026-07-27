/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Algebra.Ring.Associated
import Mathlib.Data.Rat.Lemmas

/-!
# Squarefree elements and rational squares

This file records a few general facts about squarefree elements and rational squares that Mathlib
does not provide directly, used across the multiquadratic development.

* `Squarefree.not_isSquare`: a squarefree non-unit of a monoid is not a square (the converse of
  Mathlib's `IsUnit.squarefree`). It is phrased with `Squarefree` dot-notation, so a caller
  holding `ha : Squarefree a` and `hu : ¬ IsUnit a` can write `ha.not_isSquare hu`.
* `Squarefree.neg`: negation preserves squarefreeness in any ring with distributive negation.
* `not_isSquare_intCast_of_squarefree_of_ne_one`: a squarefree integer other than `1` is not a
  rational square.
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
