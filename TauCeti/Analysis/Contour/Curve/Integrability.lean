/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.PiecewiseC1On

/-!
# Integrability of contour integrands

A piecewise-`C¹` curve has interval-integrable derivative. Multiplying that derivative by a
continuous function along the compact curve image therefore gives an interval-integrable contour
integrand. This file packages that Layer 0 conclusion of the contour-integration roadmap for
vector-valued integrands over `ℂ`.

The main theorem assumes continuity on the exact image `γ '' [[a, b]]`; a companion form accepts
continuity on any set containing that image. The scalar-valued multiplication form matches the
integrand convention used by the arc fundamental theorem of calculus.

## Main results

* `IsPiecewiseC1On.intervalIntegrable_deriv_smul_comp` — `t ↦ deriv γ t • f (γ t)` is
  interval-integrable when `f` is continuous on the curve image.
* `IsPiecewiseC1On.intervalIntegrable_deriv_smul_comp_of_mapsTo` — the same conclusion from
  continuity on an ambient set containing the curve.
* `IsPiecewiseC1On.intervalIntegrable_comp_mul_deriv` — the scalar-valued form
  `t ↦ f (γ t) * deriv γ t`.

The proof uses Mathlib's `IntervalIntegrable.smul_continuousOn`, after
`IsPiecewiseC1On.intervalIntegrable_deriv` supplies integrability of the velocity.
-/

public section

noncomputable section

namespace TauCeti.Contour

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {γ : ℝ → ℂ} {f : ℂ → E} {a b : ℝ}

/-- Along a piecewise-`C¹` curve, the product of the curve velocity with a function continuous on
the curve image is interval-integrable. This is the vector-valued contour integrand
`t ↦ deriv γ t • f (γ t)` from Layer 0 of the contour-integration roadmap. -/
theorem IsPiecewiseC1On.intervalIntegrable_deriv_smul_comp
    (hγ : IsPiecewiseC1On γ a b) (hf : ContinuousOn f (γ '' uIcc a b)) :
    IntervalIntegrable (fun t ↦ deriv γ t • f (γ t)) volume a b :=
  hγ.intervalIntegrable_deriv.smul_continuousOn
    (hf.comp hγ.continuousOn (mapsTo_image γ (uIcc a b)))

/-- Ambient-set form of `IsPiecewiseC1On.intervalIntegrable_deriv_smul_comp`: it suffices for `f`
to be continuous on a set `s` containing the curve image. -/
theorem IsPiecewiseC1On.intervalIntegrable_deriv_smul_comp_of_mapsTo {s : Set ℂ}
    (hγ : IsPiecewiseC1On γ a b) (hf : ContinuousOn f s) (hγs : MapsTo γ (uIcc a b) s) :
    IntervalIntegrable (fun t ↦ deriv γ t • f (γ t)) volume a b :=
  hγ.intervalIntegrable_deriv_smul_comp (hf.mono (image_subset_iff.mpr hγs))

/-- Scalar-valued multiplication form of
`IsPiecewiseC1On.intervalIntegrable_deriv_smul_comp`. This is the order of the two factors used by
the arc-FTC integrand `t ↦ f (γ t) * deriv γ t`. -/
theorem IsPiecewiseC1On.intervalIntegrable_comp_mul_deriv {f : ℂ → ℂ}
    (hγ : IsPiecewiseC1On γ a b) (hf : ContinuousOn f (γ '' uIcc a b)) :
    IntervalIntegrable (fun t ↦ f (γ t) * deriv γ t) volume a b :=
  (hγ.intervalIntegrable_deriv_smul_comp hf).congr fun t _ ↦ by
    rw [smul_eq_mul, mul_comm]

end TauCeti.Contour

end
