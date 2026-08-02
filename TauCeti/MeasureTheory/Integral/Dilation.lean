/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Dilation scaling of the lower Lebesgue integral

Dilating the variable of a function on a finite-dimensional real normed space `E` by a nonzero
scalar `r` rescales its integral against an additive Haar measure by `|(r ^ n)⁻¹|`, where `n` is
the dimension of `E`. Mathlib records this for the Bochner integral as
`MeasureTheory.Measure.integral_comp_smul`; this file is the lower-Lebesgue-integral counterpart,
proved the same way from `MeasureTheory.Measure.map_addHaar_smul`, and, like the Bochner version,
needing no integrability hypothesis.

## Main declarations

* `TauCeti.lintegral_comp_smul`: `∫⁻ x, g (r • x) ∂μ = |(r ^ n)⁻¹| * ∫⁻ x, g x ∂μ`.
* `TauCeti.lintegral_comp_inv_smul`: the same law written for `r⁻¹` and `0 < r`.
-/

public section

namespace TauCeti

open MeasureTheory Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Dilation scaling of the lower Lebesgue integral.** This is the counterpart, for `∫⁻`, of
Mathlib's `MeasureTheory.Measure.integral_comp_smul`; as there, no integrability of `g` is
needed. -/
theorem lintegral_comp_smul (g : E → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ x, g (r • x) ∂μ = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ∫⁻ x, g x ∂μ := by
  calc ∫⁻ x, g (r • x) ∂μ = ∫⁻ y, g y ∂Measure.map (fun x => r • x) μ :=
        (lintegral_map_equiv g
          (Homeomorph.smul (isUnit_iff_ne_zero.2 hr).unit).toMeasurableEquiv).symm
    _ = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ∫⁻ x, g x ∂μ := by
        rw [Measure.map_addHaar_smul μ hr, lintegral_smul_measure, smul_eq_mul]

/-- Dilating the variable by `r⁻¹`, for `0 < r`, multiplies a lower Lebesgue integral by
`r ^ n`, where `n` is the dimension of the ambient space. -/
theorem lintegral_comp_inv_smul (g : E → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    ∫⁻ x, g (r⁻¹ • x) ∂μ = ENNReal.ofReal (r ^ finrank ℝ E) * ∫⁻ x, g x ∂μ := by
  rw [lintegral_comp_smul μ g (inv_ne_zero hr.ne'), inv_pow, inv_inv,
    abs_of_nonneg (by positivity)]

end TauCeti
