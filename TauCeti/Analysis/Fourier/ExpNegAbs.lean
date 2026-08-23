/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Fourier transform of the two-sided exponential

For `0 < a` the function `x ↦ exp (-(a * |x|))` on `ℝ` is integrable, and pairing it against the
oscillation `exp (b * x * I)` produces the Lorentzian `2 * a / (a ^ 2 + b ^ 2)`. In Mathlib's
normalisation `𝓕 f ξ = ∫ x, exp (-2 π i x ξ) f x` this reads

`𝓕 (fun x ↦ exp (-(a * |x|))) ξ = 2 * a / (a ^ 2 + (2 * π * ξ) ^ 2)`.

The proof splits the line at the origin, where `|x|` becomes `∓x`, and evaluates the two
resulting complex exponential integrals with `integral_exp_mul_complex_Iic` and
`integral_exp_mul_complex_Ioi`.

## Main results

* `TauCeti.integrable_exp_neg_mul_abs`: integrability of `x ↦ exp (-(a * |x|))`;
* `TauCeti.integral_exp_mul_I_mul_exp_neg_mul_abs`: the Lorentzian pairing;
* `TauCeti.fourier_exp_neg_mul_abs`: the Fourier transform itself.
-/

public section

open MeasureTheory Set
open scoped FourierTransform Real

namespace TauCeti

variable {a : ℝ}

/-- The two-sided exponential is integrable on the line. -/
theorem integrable_exp_neg_mul_abs (ha : 0 < a) :
    Integrable (fun x : ℝ ↦ Real.exp (-(a * |x|))) := by
  have hIic : IntegrableOn (fun x : ℝ ↦ Real.exp (-(a * |x|))) (Iic 0) := by
    refine (integrableOn_exp_mul_Iic (a := a) ha 0).congr_fun (fun x hx ↦ ?_) measurableSet_Iic
    rw [abs_of_nonpos (mem_Iic.mp hx)]
    ring_nf
  have hIoi : IntegrableOn (fun x : ℝ ↦ Real.exp (-(a * |x|))) (Ioi 0) := by
    refine (integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0).congr_fun
      (fun x hx ↦ ?_) measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.mp hx)]
    ring_nf
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hIic.union hIoi

/-- **The Lorentzian pairing of the two-sided exponential with a complex oscillation.** -/
theorem integral_exp_mul_I_mul_exp_neg_mul_abs (ha : 0 < a) (b : ℝ) :
    (∫ x : ℝ, Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      = ((2 * a / (a ^ 2 + b ^ 2) : ℝ) : ℂ) := by
  have hre₁ : ((a : ℂ) + b * Complex.I).re = a := by simp
  have hre₂ : (-(a : ℂ) + b * Complex.I).re = -a := by simp
  have key : ∀ c x : ℝ, Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (c * x) : ℂ)
      = Complex.exp (((c : ℂ) + b * Complex.I) * x) := by
    intro c x
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hm : EqOn (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      (fun x : ℝ ↦ Complex.exp (((a : ℂ) + b * Complex.I) * x)) (Iic 0) := by
    intro x hx
    have hxa : -(a * |x|) = a * x := by rw [abs_of_nonpos (mem_Iic.mp hx)]; ring
    simpa only [hxa] using key a x
  have hp : EqOn (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      (fun x : ℝ ↦ Complex.exp ((-(a : ℂ) + b * Complex.I) * x)) (Ioi 0) := by
    intro x hx
    have hxa : -(a * |x|) = -a * x := by rw [abs_of_pos (mem_Ioi.mp hx)]; ring
    simpa only [hxa, Complex.ofReal_neg] using key (-a) x
  have hintm : IntegrableOn
      (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic (by rw [hre₁]; exact ha) 0).congr_fun
      (fun x hx ↦ (hm hx).symm) measurableSet_Iic
  have hintp : IntegrableOn
      (fun x : ℝ ↦ Complex.exp ((b : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ))
      (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (by rw [hre₂]; linarith) 0).congr_fun
      (fun x hx ↦ (hp hx).symm) measurableSet_Ioi
  have hne₁ : (a : ℂ) + b * Complex.I ≠ 0 := by
    intro h
    rw [h] at hre₁
    exact ha.ne' (by simpa using hre₁.symm)
  have hne₂ : -(a : ℂ) + b * Complex.I ≠ 0 := by
    intro h
    rw [h] at hre₂
    simp only [Complex.zero_re] at hre₂
    exact ha.ne' (by linarith)
  have hsq : (0 : ℝ) < a ^ 2 + b ^ 2 := by positivity
  rw [← intervalIntegral.integral_Iic_add_Ioi hintm hintp,
    setIntegral_congr_fun measurableSet_Iic hm, setIntegral_congr_fun measurableSet_Ioi hp,
    integral_exp_mul_complex_Iic (by rw [hre₁]; exact ha),
    integral_exp_mul_complex_Ioi (by rw [hre₂]; linarith)]
  have hprod : ((a : ℂ) + b * Complex.I) * (-(a : ℂ) + b * Complex.I)
      = -((a : ℂ) ^ 2 + (b : ℂ) ^ 2) := by
    linear_combination ((b : ℂ) ^ 2) * Complex.I_sq
  have hdenom : ((a : ℂ) ^ 2 + (b : ℂ) ^ 2) ≠ 0 := by
    have : ((a ^ 2 + b ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsq.ne'
    push_cast at this
    exact this
  rw [Complex.ofReal_div]
  push_cast
  simp only [mul_zero, Complex.exp_zero]
  field_simp
  linear_combination (-2 * (a : ℂ)) * hprod

/-- **The Fourier transform of the two-sided exponential.** With Mathlib's normalisation
`𝓕 f ξ = ∫ x, exp (-2 π i x ξ) f x`, the transform of `x ↦ exp (-(a * |x|))` is the Lorentzian
`2 * a / (a ^ 2 + (2 * π * ξ) ^ 2)`. -/
theorem fourier_exp_neg_mul_abs (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ (Real.exp (-(a * |x|)) : ℂ)) ξ
      = ((2 * a / (a ^ 2 + (2 * π * ξ) ^ 2) : ℝ) : ℂ) := by
  rw [Real.fourier_eq']
  have hrw : ∀ x : ℝ, Complex.exp ((↑(-2 * π * (inner ℝ x ξ : ℝ)) * Complex.I)) •
      ((Real.exp (-(a * |x|)) : ℝ) : ℂ)
      = Complex.exp (((-(2 * π * ξ) : ℝ) : ℂ) * x * Complex.I) * (Real.exp (-(a * |x|)) : ℂ) := by
    intro x
    rw [smul_eq_mul]
    congr 2
    push_cast [RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring
  simp only [hrw]
  rw [integral_exp_mul_I_mul_exp_neg_mul_abs ha]
  norm_num

end TauCeti
