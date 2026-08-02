/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Dilation scaling of the Sobolev seminorms

Fix a finite-dimensional real normed space `E` of dimension `n` carrying an additive Haar
measure `μ`, and dilate the variable of a function by `r > 0`, i.e. replace `u` by
`x ↦ u (r⁻¹ • x)`. This file records how that operation rescales the two quantities a
first-order Sobolev estimate compares: the `Lᵖ` seminorm of the function, and the `Lᵖ`
seminorm of its derivative.

For `0 < p < ∞` the two scaling laws are

`‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p` and `‖D(u (r⁻¹ • ·))‖_p = r ^ (n / p - 1) * ‖Du‖_p`,

the extra `r⁻¹` in the second coming from the chain rule. The mismatch of the two exponents is
the scaling obstruction behind `TauCeti.not_exists_eLpNorm_le_const_mul_eLpNorm_fderiv`: a
Poincaré-type inequality cannot hold with one constant for all compactly supported functions on
the whole space.

Mathlib has the Bochner-integral scaling law `MeasureTheory.Measure.integral_comp_inv_smul`;
`TauCeti.lintegral_comp_smul` is its lower-Lebesgue-integral counterpart, proved the same way
from `MeasureTheory.Measure.map_addHaar_smul`, and is what the `eLpNorm` statements consume.

## Main declarations

* `TauCeti.lintegral_comp_smul`: `∫⁻ x, g (r • x) ∂μ = |(r ^ n)⁻¹| * ∫⁻ x, g x ∂μ`.
* `TauCeti.lintegral_comp_inv_smul`: the same law written for `r⁻¹` and `0 < r`.
* `TauCeti.eLpNorm_comp_inv_smul`: `‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p`.
* `TauCeti.hasFDerivAt_comp_inv_smul`, `TauCeti.fderiv_comp_inv_smul`: the chain rule for a
  dilation, `D(u (r⁻¹ • ·)) x = r⁻¹ • Du (r⁻¹ • x)`.
* `TauCeti.eLpNorm_fderiv_comp_inv_smul`: `‖D(u (r⁻¹ • ·))‖_p = r ^ (n / p - 1) * ‖Du‖_p`.
-/

public section

namespace TauCeti

open MeasureTheory Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

section Calculus

/-- **Chain rule for a dilation.** If `u` has derivative `u'` at `r⁻¹ • x`, then the dilate
`y ↦ u (r⁻¹ • y)` has derivative `r⁻¹ • u'` at `x`. -/
theorem hasFDerivAt_comp_inv_smul {u : E → F} {u' : E →L[ℝ] F} {x : E} (r : ℝ)
    (h : HasFDerivAt u u' (r⁻¹ • x)) :
    HasFDerivAt (fun y => u (r⁻¹ • y)) (r⁻¹ • u') x := by
  have hid : HasFDerivAt (fun y : E => r⁻¹ • y) (r⁻¹ • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_id x).const_smul r⁻¹
  have key : u' ∘L (r⁻¹ • ContinuousLinearMap.id ℝ E) = r⁻¹ • u' := by ext v; simp
  exact key ▸ h.comp x hid

/-- The derivative of a dilate is the dilate of the derivative, scaled by `r⁻¹`. -/
theorem fderiv_comp_inv_smul {u : E → F} (hu : Differentiable ℝ u) (r : ℝ) :
    (fderiv ℝ fun y => u (r⁻¹ • y)) = r⁻¹ • fun x => fderiv ℝ u (r⁻¹ • x) := by
  funext x
  exact (hasFDerivAt_comp_inv_smul r (hu (r⁻¹ • x)).hasFDerivAt).fderiv

end Calculus

section Measure

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E)
  [μ.IsAddHaarMeasure] {G : Type*} [NormedAddCommGroup G]

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

/-- **Dilation scaling of the `Lᵖ` seminorm:** `‖u (r⁻¹ • ·)‖_p = r ^ (n / p) * ‖u‖_p`, where
`n` is the dimension of the ambient space. -/
theorem eLpNorm_comp_inv_smul (f : E → G) {r : ℝ} (hr : 0 < r) {p : ℝ≥0∞} (hp₀ : p ≠ 0)
    (hp : p ≠ ∞) :
    eLpNorm (fun x => f (r⁻¹ • x)) p μ =
      ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / p.toReal)) * eLpNorm f p μ := by
  have ht : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp
  have key := lintegral_comp_inv_smul μ (fun y => ‖f y‖ₑ ^ p.toReal) hr
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp, eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp,
    key, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  have hpow : ((r ^ finrank ℝ E : ℝ)) ^ (1 / p.toReal) = r ^ ((finrank ℝ E : ℝ) / p.toReal) := by
    rw [← Real.rpow_natCast r (finrank ℝ E), ← Real.rpow_mul hr.le]
    ring_nf
  congr 1
  rw [← hpow]
  exact ENNReal.ofReal_rpow_of_pos (by positivity : (0 : ℝ) < r ^ finrank ℝ E)

/-- **Dilation scaling of the `Lᵖ` seminorm of the derivative:**
`‖D(u (r⁻¹ • ·))‖_p = r ^ (n / p - 1) * ‖Du‖_p`. The exponent drops by one relative to
`TauCeti.eLpNorm_comp_inv_smul` because the chain rule contributes a factor `r⁻¹`. -/
theorem eLpNorm_fderiv_comp_inv_smul {u : E → F} (hu : Differentiable ℝ u) {r : ℝ} (hr : 0 < r)
    {p : ℝ≥0∞} (hp₀ : p ≠ 0) (hp : p ≠ ∞) :
    eLpNorm (fderiv ℝ fun y => u (r⁻¹ • y)) p μ =
      ENNReal.ofReal (r ^ ((finrank ℝ E : ℝ) / p.toReal - 1)) * eLpNorm (fderiv ℝ u) p μ := by
  rw [fderiv_comp_inv_smul hu r, eLpNorm_const_smul r⁻¹ (fun x => fderiv ℝ u (r⁻¹ • x)) p μ,
    eLpNorm_comp_inv_smul μ (fderiv ℝ u) hr hp₀ hp, ← mul_assoc]
  congr 1
  rw [Real.enorm_eq_ofReal_abs, abs_of_pos (by positivity : (0 : ℝ) < r⁻¹),
    ← ENNReal.ofReal_mul (by positivity), Real.rpow_sub hr, Real.rpow_one]
  congr 1
  field_simp

end Measure

end TauCeti
