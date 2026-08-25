/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Basic
public import TauCeti.Analysis.Contour.PiecewiseC1On
import TauCeti.Analysis.Contour.Winding.EndpointRatio

/-!
# The winding number of a closed curve is an integer

For a curve `γ` on an interval that returns to its start (`γ a = γ b`), avoids a point `w`, and is
regular enough — continuous, differentiable off a countable set, with an interval-integrable index
integrand — its generalized winding number about `w` is an integer (see
`exists_int_windingNumber_of_closed` for the exact hypotheses). This is the integrality step on the
Hungerbühler–Wasem path (HW Thm 3.3): combined with continuity of the winding number in the point,
it makes the winding number locally constant on the complement of the curve — the input to the
homology form of Cauchy's theorem.

Closing the curve is the only thing used here: `exp_two_pi_I_mul_windingNumber_of_avoidance`
evaluates `exp (2πi · n_w(γ))` as the endpoint ratio `(γ b - w) / (γ a - w)` for any avoiding arc,
and `γ a = γ b` makes that ratio `1`.

## Main results

* `TauCeti.Contour.exists_int_windingNumber_of_closed` — the generalized winding number of a closed
  curve is an integer.
* `TauCeti.Contour.IsPiecewiseC1On.exists_int_windingNumber` — the same for a closed piecewise-`C¹`
  curve, whose regularity supplies the raw hypotheses on its own.

## Provenance

Adapted from `hasGeneralizedWindingNumber_integer_of_closed` in `WindingInteger.lean` of the AINTLIB
`LeanModularForms` development, restated for a raw `γ : ℝ → ℂ` on an oriented interval. The
argument-lift computation that used to sit here now lives in `Winding.EndpointRatio`, which proves
it for arcs that need not close up.
-/

public section

open MeasureTheory Set

open scoped Interval

namespace TauCeti.Contour

/-- **The winding number of a closed curve is an integer.** For a curve `γ` on the oriented interval
with endpoints `a`, `b` that returns to its start (`γ a = γ b`), is continuous on `Set.uIcc a b`,
differentiable off a countable set `P`, avoids `w` throughout `Set.uIcc a b`, and has an
interval-integrable index integrand `(γ · - w)⁻¹ * deriv γ`, the generalized winding number
`windingNumber γ a b w` is an integer. -/
theorem exists_int_windingNumber_of_closed {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable) (hγ_cont : ContinuousOn γ (uIcc a b))
    (hγ_diff : ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) volume a b) :
    ∃ n : ℤ, windingNumber γ a b w = n := by
  -- The endpoint ratio of a closed curve is `1`, so the exponent is a multiple of `2πi`.
  have h := exp_two_pi_I_mul_windingNumber_of_avoidance hP hγ_cont hγ_diff h_avoid h_int
  rw [← hclosed, div_self (sub_ne_zero.mpr (h_avoid a left_mem_uIcc))] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_⟩
  rw [hn, mul_comm]

/-- **Piecewise-`C¹` form of winding-number integrality.** For a closed piecewise-`C¹` curve that
avoids `w`, the winding number about `w` is an integer. Piecewise-`C¹` regularity supplies the
continuity, differentiability and integrability hypotheses of
`exists_int_windingNumber_of_closed`. -/
theorem IsPiecewiseC1On.exists_int_windingNumber {γ : ℝ → ℂ} {a b : ℝ} {w : ℂ}
    (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b)
    (h_avoid : ∀ t ∈ uIcc a b, γ t ≠ w) :
    ∃ n : ℤ, windingNumber γ a b w = n := by
  obtain ⟨P, hP, hγ_diff⟩ := hγ.exists_countable_differentiableAt
  exact exists_int_windingNumber_of_closed hclosed hP hγ.continuousOn hγ_diff h_avoid
    (intervalIntegrable_inv_sub_mul_deriv hγ.continuousOn h_avoid hγ.intervalIntegrable_deriv)

end TauCeti.Contour

end
