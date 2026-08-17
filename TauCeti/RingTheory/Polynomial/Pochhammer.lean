/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Descending Pochhammer polynomials

This module provides basic lemmas for descending Pochhammer polynomials `descPochhammer R n`
over general rings.

Unlike Mathlib's `monic_descPochhammer` and `descPochhammer_natDegree`, which require
`[NoZeroDivisors R]` or `[Nontrivial R]`, the results here hold under minimal hypotheses by
transporting from the integer case `descPochhammer ℤ n`.

## Main declarations

* `TauCeti.monic_descPochhammer`: `descPochhammer R n` is monic over any ring `R`.
* `TauCeti.descPochhammer_natDegree`: `(descPochhammer R n).natDegree = n` for nontrivial `R`.
* `TauCeti.descPochhammer_degree`: `(descPochhammer R n).degree = n` for nontrivial `R`.
-/

public section

namespace TauCeti

open Polynomial

/-- Unlike `monic_descPochhammer`, this drops `[Nontrivial R]` and `[NoZeroDivisors R]`
and holds over any ring. -/
theorem monic_descPochhammer {R : Type*} [Ring R] (n : ℕ) :
    Monic (descPochhammer R n) := by
  rw [← descPochhammer_map (Int.castRingHom R)]
  exact (_root_.monic_descPochhammer ℤ n).map (Int.castRingHom R)

/-- Unlike `descPochhammer_natDegree`, this drops `[NoZeroDivisors R]` and holds over any
nontrivial ring. -/
@[simp]
theorem descPochhammer_natDegree {R : Type*} [Ring R] [Nontrivial R] (n : ℕ) :
    (descPochhammer R n).natDegree = n := by
  rw [← descPochhammer_map (Int.castRingHom R),
    (_root_.monic_descPochhammer ℤ n).natDegree_map (Int.castRingHom R),
    _root_.descPochhammer_natDegree (R := ℤ)]

/-- The degree of the descending Pochhammer polynomial over any nontrivial ring is `n`. -/
@[simp]
theorem descPochhammer_degree {R : Type*} [Ring R] [Nontrivial R] (n : ℕ) :
    (descPochhammer R n).degree = n := by
  rw [Polynomial.degree_eq_natDegree (monic_descPochhammer n).ne_zero,
    descPochhammer_natDegree n]

end TauCeti
