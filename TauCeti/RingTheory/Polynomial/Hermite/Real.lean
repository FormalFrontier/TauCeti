/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-!
# The probabilists' Hermite polynomials over `ℝ`

Mathlib defines `Polynomial.hermite` in `ℤ[X]`. Every analytic consumer in this library wants the
same family in `ℝ[X]`, and each of them was spelling the cast out inline as
`(hermite n).map (Int.castRingHom ℝ)`, re-deriving `eval` and `degree` facts about it at the point
of use. This file gives that cast a name and states those two facts once.

It deliberately sits beside
`TauCeti/RingTheory/Polynomial/Hermite/Derivative.lean` rather than in any analysis or probability
file: the definition mentions no measure, no inner product space, and no Gaussian, so putting it
here is what lets the *earlier* function-side files import it. A copy living in a Gaussian leaf
file would be unreachable from exactly the places that need it.

## Main definitions

* `TauCeti.hermiteℝ` — `Hₙ` cast into `ℝ[X]`.

## Main statements

* `TauCeti.eval_hermiteℝ` — evaluation agrees with `aeval` against the integer polynomial.
* `TauCeti.degree_hermiteℝ` — the cast preserves degrees, so `Hₙ` has degree exactly `n`. This is
  the exact-degree hypothesis that the polynomial-completeness machinery consumes.
-/

public section

namespace TauCeti

open Polynomial

/-- `Hₙ` over `ℝ`: Mathlib's `Polynomial.hermite n` lives in `ℤ[X]`, and the analytic consumers
in this library take a real polynomial family. -/
noncomputable def hermiteℝ (n : ℕ) : Polynomial ℝ := (hermite n).map (Int.castRingHom ℝ)

@[simp]
theorem eval_hermiteℝ (n : ℕ) (x : ℝ) : (hermiteℝ n).eval x = aeval x (hermite n) := by
  rw [hermiteℝ, Polynomial.eval_map, Polynomial.aeval_def]
  rfl

/-- The cast to `ℝ[X]` preserves degrees: `Hₙ` has degree exactly `n`.

Marked `@[simp]`, matching Mathlib's own `Polynomial.degree_hermite`. -/
@[simp]
theorem degree_hermiteℝ (n : ℕ) : (hermiteℝ n).degree = (n : WithBot ℕ) := by
  rw [hermiteℝ, Polynomial.degree_map_eq_of_injective Int.cast_injective, Polynomial.degree_hermite]

end TauCeti
