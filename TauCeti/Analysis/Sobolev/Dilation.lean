/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

-- `TauCeti.MeasureTheory.Function.Lp.Dilation` is imported publicly:
-- `TauCeti.eLpNorm_comp_inv_smul` is the companion of the statement below, and supplies the
-- `eLpNorm` and Haar measure API appearing in its signature.
public import TauCeti.MeasureTheory.Function.Lp.Dilation
public import Mathlib.Analysis.Calculus.FDeriv.Basic
-- `Mathlib.Analysis.Calculus.FDeriv.Equiv` is imported privately: its `fderiv_comp_smul` is used
-- only inside the proof, so downstream importers do not pay for the equivalence machinery.
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/-!
# Dilation scaling of the Sobolev seminorms

Fix a finite-dimensional real normed space `E` of dimension `n` carrying an additive Haar
measure `μ`, and dilate the variable of a function by `r > 0`, i.e. replace `u` by
`x ↦ u (r⁻¹ • x)`. This file records how that operation rescales the `Lᵖ` seminorm of the
derivative, the second of the two quantities a first-order Sobolev estimate compares; the first,
the `Lᵖ` seminorm of the function itself, is `TauCeti.eLpNorm_comp_inv_smul`.

For `0 < p < ∞` the two scaling laws are

`‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p` and `‖D(u (r⁻¹ • ·))‖_p = r ^ (n / p - 1) * ‖Du‖_p`,

the extra `r⁻¹` in the second coming from the chain rule, in the shape of Mathlib's
`fderiv_comp_smul`. The mismatch of the two exponents is the scaling obstruction behind
`TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`: a
Poincaré-type inequality cannot hold with one constant for all compactly supported functions on
the whole space.

## Main declarations

* `TauCeti.eLpNorm_fderiv_comp_inv_smul`: `‖D(u (r⁻¹ • ·))‖_p = r ^ (n / p - 1) * ‖Du‖_p`.
-/

public section

namespace TauCeti

open MeasureTheory Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Dilation scaling of the `Lᵖ` seminorm of the derivative:**
`‖D(u (r⁻¹ • ·))‖_p = r ^ (n / p - 1) * ‖Du‖_p`. The exponent drops by one relative to
`TauCeti.eLpNorm_comp_inv_smul` because the chain rule contributes a factor `r⁻¹`. -/
theorem eLpNorm_fderiv_comp_inv_smul (u : E → F) {r : ℝ} (hr : 0 < r)
    {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞) :
    eLpNorm (fderiv ℝ fun y => u (r⁻¹ • y)) p μ =
      ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / p.toReal - 1)) * eLpNorm (fderiv ℝ u) p μ := by
  have hfderiv : (fderiv ℝ fun y => u (r⁻¹ • y)) = r⁻¹ • fun x => fderiv ℝ u (r⁻¹ • x) :=
    funext fun x => fderiv_comp_smul (f := u) (x := x) r⁻¹
  rw [hfderiv, eLpNorm_const_smul r⁻¹ (fun x => fderiv ℝ u (r⁻¹ • x)) p μ,
    eLpNorm_comp_inv_smul μ (fderiv ℝ u) hr hp₀ hp, ← mul_assoc]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos (by positivity : (0 : ℝ) < r⁻¹),
    ← ENNReal.ofReal_mul (by positivity), Real.rpow_sub hr, Real.rpow_one]
  congr 1
  field_simp

end TauCeti
