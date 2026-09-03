/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.IsIntegral

import Mathlib.Tactic.ComputeDegree

/-!
# Integrality from a monic quadratic relation

Mathlib's `IsIntegral.of_aeval_monic_of_isIntegral_coeff` takes a monic polynomial and asks for
each coefficient to be integral. Applying it to a quadratic means writing the polynomial out,
discharging the degree computation, and answering the coefficient obligation index by index — the
same half-dozen lines every time.

## Main results

* `IsIntegral.of_sq_add_mul_add_eq_zero`: if `y ^ 2 + b * y + c = 0` with `b` and `c` integral over
  `R`, then `y` is integral over `R`.

The relation is stated as an equation rather than through `Polynomial.aeval`, which is the form a
caller actually holds: a change-of-variables identity or a curve equation, rearranged by
`linear_combination`.

## Provenance

Extracted from `TauCeti/AlgebraicGeometry/EllipticCurve/Integrality.lean`, where it was a private
helper for `WeierstrassCurve.isIntegral_y_of_equation_of_isIntegral_x` with a note that it was
"kept here rather than exported, since `isIntegral_y_of_equation_of_isIntegral_x` is its only
consumer". A second consumer now exists — the coordinates of a change of variables between integral
Weierstrass models — so the note no longer holds and the statement moves to where both can reach
it. The proof is unchanged; only the name is now `IsIntegral`-prefixed, since nothing about it is
about elliptic curves.
-/

public section

open Polynomial

/-- **An element satisfying a monic quadratic relation with integral coefficients is integral.**
`y`, `b` and `c` live in an arbitrary commutative `R`-algebra `A`, and the relation is an equation
in `A` rather than a statement about `Polynomial.aeval`, so a caller supplies whatever identity it
already holds. -/
theorem IsIntegral.of_sq_add_mul_add_eq_zero {R : Type*} [CommRing R] {A : Type*} [CommRing A]
    [Algebra R A] {b c y : A} (hb : IsIntegral R b) (hc : IsIntegral R c)
    (h : y ^ 2 + b * y + c = 0) : IsIntegral R y := by
  -- `IsIntegral.of_aeval_monic_of_isIntegral_coeff` for `X ^ 2 + C b * X + C c`, with the degree
  -- computation and the per-coefficient obligations discharged index by index.
  nontriviality A
  have hdeg : (X ^ 2 + (C b * X + C c) : A[X]).natDegree = 2 := by compute_degree!
  refine IsIntegral.of_aeval_monic_of_isIntegral_coeff (p := X ^ 2 + (C b * X + C c))
    (monic_X_pow_add (by compute_degree!)) (by omega) ?_ ?_
  · have : Polynomial.eval y (X ^ 2 + (C b * X + C c) : A[X]) = 0 := by
      simpa only [eval_add, eval_pow, eval_X, eval_mul, eval_C, add_assoc] using h
    rw [this]
    exact isIntegral_zero
  · intro i
    match i with
    | 0 => simpa using hc
    | 1 => simpa using hb
    | 2 => simpa using (isIntegral_one : IsIntegral R (1 : A))
    | (n + 3) => simpa using (isIntegral_zero : IsIntegral R (0 : A))

end
