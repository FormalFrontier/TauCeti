/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Periodic

/-!
# The local parameter under translation, period rescaling, and differentiation

Identities for the local parameter `𝕢 h z = exp (2 π I z / h)` at a cusp: translating
the argument multiplies by an exponential, the `m`-th power of the local parameter at
period `m * h` is the local parameter at period `h`, the parameter differentiates to
itself times `2πi/h`, and the logarithmic derivative of any periodic function of
nonzero width `h` factors through its cusp function along the parameter.

## Main declarations

* `TauCeti.Periodic.qParam_sub`: `𝕢 h (z - j) = 𝕢 h z * exp (-2 π I j / h)`.
* `TauCeti.Periodic.qParam_nat_mul_pow`: `𝕢 (m * h) z ^ m = 𝕢 h z` for `m ≠ 0`.
* `TauCeti.Periodic.hasDerivAt_qParam` (with `deriv_qParam`): the `q`-parameter
  differentiates to itself times `2πi/h`.
* `TauCeti.Periodic.logDeriv_eq_logDeriv_cuspFunction_mul_deriv_qParam`: the chain rule
  for the logarithmic derivative of a periodic function of nonzero width through its
  cusp function.

## References

* [Mathlib PR #39083](https://github.com/leanprover-community/mathlib4/pull/39083)
  (Chris Birkbeck) — the upstream draft this file ports onto the current Mathlib pin.
-/

public section

open Complex
open scoped Real

namespace TauCeti.Periodic

open Function.Periodic

local notation "𝕢" => Function.Periodic.qParam

variable {h : ℝ}

/-- Translation by `j` in the argument of `qParam` corresponds to multiplication by
`exp (-2 π I j / h)`. -/
theorem qParam_sub (z j : ℂ) : 𝕢 h (z - j) = 𝕢 h z * exp (-2 * π * I * j / h) := by
  simp only [qParam, ← Complex.exp_add]
  ring_nf

/-- The `m`-th power of the local parameter at period `m * h` is the local parameter at
period `h`. -/
theorem qParam_nat_mul_pow {m : ℕ} (hm : m ≠ 0) (z : ℂ) : 𝕢 (m * h) z ^ m = 𝕢 h z := by
  simp only [qParam, ← Complex.exp_nat_mul, ofReal_mul, ofReal_natCast]
  rw [mul_div_assoc', mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hm)]


/-- The `q`-parameter differentiates to itself times `2πi/h`. For `h = 0` the parameter
is the constant `1`, whose derivative is genuinely `0` — the value the division junk
`2πi/0 = 0` also produces — so the statement is unconditional. -/
theorem hasDerivAt_qParam (h : ℝ) (z : ℂ) :
    HasDerivAt (𝕢 h) (𝕢 h z * (2 * π * I / h)) z := by
  simpa only [Function.Periodic.qParam, id_eq, mul_one] using!
    (((hasDerivAt_id z).const_mul (2 * (π : ℂ) * I)).div_const h).cexp

/-- The derivative of the `q`-parameter, in rewrite form. -/
@[simp]
theorem deriv_qParam (h : ℝ) (z : ℂ) : deriv (𝕢 h) z = 𝕢 h z * (2 * π * I / h) :=
  (hasDerivAt_qParam h z).deriv

/-- The chain rule for the logarithmic derivative of a periodic function through its
cusp function: `logDeriv g` factors through `logDeriv (cuspFunction h g)` along the
`q`-parameter, for nonzero width `h`. The statement needs no differentiability: where
`g` is not
differentiable, neither is the cusp function at `𝕢 h z` — the composition
`cuspFunction h g ∘ 𝕢 h` is `g` — so both logarithmic derivatives take the junk
value `0`. -/
theorem logDeriv_eq_logDeriv_cuspFunction_mul_deriv_qParam {g : ℂ → ℂ} (hh : h ≠ 0)
    (hg : Function.Periodic g h) (z : ℂ) :
    logDeriv g z = logDeriv (cuspFunction h g) (𝕢 h z) * deriv (𝕢 h) z := by
  have hfun : g = fun w ↦ cuspFunction h g (𝕢 h w) :=
    funext fun w ↦ (eq_cuspFunction hh hg w).symm
  rcases em (DifferentiableAt ℂ g z) with hd | hd
  · conv_lhs => rw [hfun]
    exact logDeriv_comp (differentiableAt_cuspFunction hh hg hd)
      (hasDerivAt_qParam h z).differentiableAt
  · have hnc : ¬DifferentiableAt ℂ (cuspFunction h g) (𝕢 h z) := fun hc ↦ hd <| by
      rw [hfun]
      exact hc.comp z (hasDerivAt_qParam h z).differentiableAt
    rw [logDeriv_eq_zero_of_not_differentiableAt _ _ hd,
      logDeriv_eq_zero_of_not_differentiableAt _ _ hnc, zero_mul]

end TauCeti.Periodic

end
