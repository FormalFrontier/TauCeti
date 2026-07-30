/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev

/-!
# The Chebyshev polynomials as a basis

This file packages the Chebyshev polynomials of the first kind as a basis of `R[X]` when `R` is an
integral domain in which `2` is invertible. Mathlib
already proves that `T R n` has degree `n`, records its leading coefficient, and bundles the
family as `Polynomial.Chebyshev.chebyshevTsequence`.  Its generic polynomial-sequence API then
gives a basis whenever all leading coefficients are units.

The resulting basis is an algebraic prerequisite for Part C of the `OrthogonalL2Bases` roadmap.

## Main declarations

* `Polynomial.Chebyshev.chebyshevTBasis`: the basis `n ↦ T R n` of `R[X]`;
-/

public section

namespace Polynomial.Chebyshev

variable {R : Type*} [CommRing R] [IsDomain R] [Invertible (2 : R)]

/-- The leading coefficient of every Chebyshev polynomial of the first kind over `R` is a unit. -/
private lemma isUnit_leadingCoeff_T (n : ℕ) : IsUnit (T R n).leadingCoeff := by
  rw [leadingCoeff_T]
  exact (isUnit_of_invertible (2 : R)).pow _

/-- The Chebyshev polynomials of the first kind, indexed by their nonnegative degree, form a
basis of `R[X]`. -/
noncomputable def chebyshevTBasis : Module.Basis ℕ R R[X] :=
  (chebyshevTsequence R).basis isUnit_leadingCoeff_T

/-- The `n`th vector of the Chebyshev basis is `T R n`. -/
@[simp]
lemma chebyshevTBasis_apply (n : ℕ) : chebyshevTBasis n = T R n :=
  Polynomial.Sequence.basis_eq_self _ _ n

end Polynomial.Chebyshev
