/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Shift

/-!
# The shift reduction for the Hille--Yosida theorem

The Hille--Yosida generation theorem is proved first at growth exponent zero.  For an operator
`A` with resolvent bounds on `(omega, infinity)`, the shifted operator `A - omega I` has the
corresponding bounds on `(0, infinity)`.  This file packages that reduction using the exact
resolvent translation

`R(lambda, A - omega I) = R(lambda + omega, A)`.

Together with `StronglyContinuousSemigroup.generator_expShift`, this is the shift step that
reduces the general `(M, omega)` generation problem to the exponent-zero construction.

## Main result

* `TauCeti.LinearPMap.hilleYosida_zero_of`: reduction of the general Hille--Yosida resolvent
  hypotheses to growth exponent zero.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Theorem II.3.5;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 1.
-/

public section

noncomputable section

namespace TauCeti.LinearPMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The general `(M, omega)` Hille--Yosida resolvent hypotheses become the exponent-zero
hypotheses for `A - omega I`.

This packages exactly the two facts consumed by the zero-exponent Yosida construction: every
positive `lambda` is a resolvent point, and every positive power satisfies the sharp
`M / lambda ^ n` estimate. -/
theorem hilleYosida_zero_of {A : X →ₗ.[ℝ] X} {M omega : ℝ}
    (hres : ∀ lambda, omega < lambda → lambda ∈ resolventSet A)
    (hbound : ∀ n : ℕ, 1 ≤ n → ∀ lambda, omega < lambda →
      ‖resolvent A lambda ^ n‖ ≤ M / (lambda - omega) ^ n) :
    (∀ lambda, 0 < lambda → lambda ∈ resolventSet (subScalar A omega)) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ lambda, 0 < lambda →
        ‖resolvent (subScalar A omega) lambda ^ n‖ ≤ M / lambda ^ n := by
  constructor
  · intro lambda hlambda
    rw [mem_resolventSet_subScalar_iff]
    exact hres (lambda + omega) (by linarith)
  · intro n hn lambda hlambda
    have hmem : lambda + omega ∈ resolventSet A := hres (lambda + omega) (by linarith)
    rw [resolvent_subScalar hmem]
    simpa only [add_sub_cancel_right] using hbound n hn (lambda + omega) (by linarith)

end TauCeti.LinearPMap

end
