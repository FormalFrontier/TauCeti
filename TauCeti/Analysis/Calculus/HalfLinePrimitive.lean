/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The primitive of a function on the nonnegative half-line

Given `f : ℝ → ℝ`, this file constructs `TauCeti.halfLinePrimitive f`, the primitive `t ↦ ∫₀ᵗ f`
of `f` on `[0, ∞)`. To make the function total on `ℝ`, the integrand is composed with `max · 0`,
so on `[0, ∞)` the value is the ordinary integral `∫₀ᵗ f` and on `(-∞, 0]` it is the linear
extension `t ↦ t * f 0`.

The construction is generic calculus: it depends only on Mathlib's fundamental theorem of
calculus and knows nothing about complete monotonicity or Bernstein functions.

## Main declarations

* `TauCeti.halfLinePrimitive`: the primitive `∫₀ᵗ f` of `f` on the nonnegative half-line.
* `TauCeti.halfLinePrimitive_def`: the unconditional defining equation
  `halfLinePrimitive f t = ∫₀ᵗ f (max x 0)`.
* `TauCeti.halfLinePrimitive_eq_integral_of_nonneg`, `TauCeti.halfLinePrimitive_of_nonpos`: the
  value of the primitive on each half-line.
* `TauCeti.continuous_halfLinePrimitive`: the primitive is continuous on all of `ℝ` whenever `f`
  is continuous on `[0, ∞)`.
* `TauCeti.hasDerivAt_halfLinePrimitive`, `TauCeti.deriv_halfLinePrimitive`: its derivative is
  `f` at every nonnegative point.
-/

public section

open Set intervalIntegral

namespace TauCeti

variable {f : ℝ → ℝ} {t : ℝ}

/-- The primitive of `f` on the nonnegative half-line. The `max` canonically extends the
integrand to negative arguments; on `[0, ∞)` this is `∫₀ᵗ f`. -/
noncomputable def halfLinePrimitive (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..t, f (max x 0)

/-- The unconditional defining equation of `halfLinePrimitive`, usable in downstream files where
the body of the definition is not available. -/
theorem halfLinePrimitive_def (f : ℝ → ℝ) (t : ℝ) :
    halfLinePrimitive f t = ∫ x in (0 : ℝ)..t, f (max x 0) := by rfl

/-- If `f` is continuous on `[0, ∞)`, then its extension `x ↦ f (max x 0)` is continuous on all
of `ℝ`. -/
private theorem continuous_comp_max_zero (hf : ContinuousOn f (Ici 0)) :
    Continuous fun x : ℝ ↦ f (max x 0) := by
  simpa [Function.comp_def] using
    hf.comp_continuous (continuous_id'.max continuous_const) fun x ↦ mem_Ici.mpr (le_max_right x 0)

/-- On the nonnegative half-line, `halfLinePrimitive` is the ordinary integral of `f` from
zero. -/
@[grind =>]
theorem halfLinePrimitive_eq_integral_of_nonneg (ht : 0 ≤ t) :
    halfLinePrimitive f t = ∫ x in (0 : ℝ)..t, f x := by
  rw [halfLinePrimitive_def]
  apply intervalIntegral.integral_congr
  intro x hx
  simp only [uIcc_of_le ht] at hx
  simp only [max_eq_left hx.1]

/-- On the nonpositive half-line, `halfLinePrimitive` is the linear extension `t ↦ t * f 0`. -/
theorem halfLinePrimitive_of_nonpos (ht : t ≤ 0) : halfLinePrimitive f t = t * f 0 := by
  rw [halfLinePrimitive_def]
  have hconst : (∫ x in (0 : ℝ)..t, f (max x 0)) = ∫ _ in (0 : ℝ)..t, f 0 :=
    intervalIntegral.integral_congr fun x hx ↦ by
      simp only [uIcc_of_ge ht] at hx
      simp only [max_eq_right hx.2]
  rw [hconst]
  simp

/-- The value of `halfLinePrimitive f` at the origin is `0`. -/
@[simp]
theorem halfLinePrimitive_zero (f : ℝ → ℝ) : halfLinePrimitive f 0 = 0 := by
  simp [halfLinePrimitive_def]

/-- If `f` is continuous on `[0, ∞)`, then `halfLinePrimitive f` is continuous on all of `ℝ`; the
`max` extension of the integrand makes the primitive continuous through the origin. -/
theorem continuous_halfLinePrimitive (hf : ContinuousOn f (Ici 0)) :
    Continuous (halfLinePrimitive f) := by
  unfold halfLinePrimitive
  exact intervalIntegral.continuous_primitive
    (fun a b ↦ (continuous_comp_max_zero hf).intervalIntegrable a b) 0

/-- If `f` is continuous on `[0, ∞)`, then `halfLinePrimitive f` has derivative `f t` at every
`t ≥ 0`. The `max` extension of the integrand makes the derivative at `t = 0` two-sided. -/
theorem hasDerivAt_halfLinePrimitive (hf : ContinuousOn f (Ici 0)) (ht : 0 ≤ t) :
    HasDerivAt (halfLinePrimitive f) (f t) t := by
  have hcont := continuous_comp_max_zero hf
  unfold halfLinePrimitive
  simpa only [max_eq_left ht] using
    intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ)) (hcont.intervalIntegrable 0 t)
      hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt

/-- If `f` is continuous on `[0, ∞)`, then the derivative of `halfLinePrimitive f` is `f` at
every `t ≥ 0`. -/
@[grind =>]
theorem deriv_halfLinePrimitive (hf : ContinuousOn f (Ici 0)) (ht : 0 ≤ t) :
    deriv (halfLinePrimitive f) t = f t :=
  (hasDerivAt_halfLinePrimitive hf ht).deriv

end TauCeti

end
