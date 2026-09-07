/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Principal powers of `z - x` on the upper half-plane

For a real number `x`, the difference `z - x` of an upper-half-plane point and `x` again has
positive imaginary part, hence lies in `Complex.slitPlane`.  The principal power
`(z - x) ^ (r : ℂ)` is therefore holomorphic and nonvanishing there, and its logarithmic
derivative is the simple fraction `r / (z - x)`.

Reflecting the base across the real axis, replacing `z - x` by `x - z`, multiplies the power by
the constant `exp (π r i)` -- unimodular when `r` is real -- because the two bases lie on opposite
sides of the real axis.

These are the basic branch facts for a factor of a product of principal powers with real base
points, such as the Schwarz--Christoffel integrand.

## Main results

* `TauCeti.sub_ofReal_mem_slitPlane_of_im_pos`
* `TauCeti.differentiableAt_sub_cpow_of_im_pos`
* `TauCeti.sub_cpow_ne_zero_of_im_pos`
* `TauCeti.sub_cpow_eq_exp_mul_sub_cpow_of_im_pos`
* `TauCeti.logDeriv_sub_cpow_of_im_pos`
-/

public section

open Complex

namespace TauCeti

/-- Translating a point with positive imaginary part by a real number leaves it in the slit
plane. -/
lemma sub_ofReal_mem_slitPlane_of_im_pos {z : ℂ} (hz : 0 < z.im) (x : ℝ) :
    z - (x : ℂ) ∈ slitPlane := by
  simp [slitPlane, hz.ne']

/-- The principal power `(z - x) ^ (r : ℂ)` with real base point `x` and real exponent `r` is
differentiable at every point with positive imaginary part. -/
lemma differentiableAt_sub_cpow_of_im_pos {z : ℂ} (hz : 0 < z.im) (x r : ℝ) :
    DifferentiableAt ℂ (fun w : ℂ => (w - (x : ℂ)) ^ (r : ℂ)) z :=
  (differentiableAt_id.sub_const (x : ℂ)).cpow_const
    (sub_ofReal_mem_slitPlane_of_im_pos hz x)

/-- The principal power `(z - x) ^ (r : ℂ)` with real base point `x` and real exponent `r` does
not vanish at a point with positive imaginary part. -/
lemma sub_cpow_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) (x r : ℝ) :
    (z - (x : ℂ)) ^ (r : ℂ) ≠ 0 := by
  rw [Complex.cpow_ne_zero_iff]
  left
  intro h
  have := congr_arg Complex.im h
  simp only [sub_im, ofReal_im, sub_zero, zero_im] at this
  exact hz.ne' this

/-- Reflecting the base of a principal power with real base point multiplies it by the factor
`exp (π r i)`, unimodular for a real exponent `r`.  At a point with positive imaginary part the two
bases `z - x` and `x - z` lie on opposite sides of the real axis, so their arguments differ by `π`
and neither meets the branch cut of the other. -/
lemma sub_cpow_eq_exp_mul_sub_cpow_of_im_pos {z : ℂ} (hz : 0 < z.im) (x : ℝ) (r : ℂ) :
    (z - (x : ℂ)) ^ r = Complex.exp ((Real.pi : ℂ) * r * I) * ((x : ℂ) - z) ^ r := by
  have him : ((x : ℂ) - z).im < 0 := by simpa using hz
  have hne : (x : ℂ) - z ≠ 0 := fun h => by simp [h] at him
  have hlog : ∀ w : ℂ, w.im < 0 → Complex.log (-w) = Complex.log w + (Real.pi : ℂ) * I := by
    intro w hw
    apply Complex.ext
    · simp [Complex.log_re]
    · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hw]
  have hneg : z - (x : ℂ) = -((x : ℂ) - z) := by ring
  rw [hneg, Complex.cpow_def_of_ne_zero (neg_ne_zero.mpr hne),
    Complex.cpow_def_of_ne_zero hne, hlog _ him, ← Complex.exp_add]
  congr 1
  ring

/-- The logarithmic derivative of `w ↦ (w - x) ^ (r : ℂ)` at a point with positive imaginary
part is the simple fraction `r / (z - x)`. -/
lemma logDeriv_sub_cpow_of_im_pos {z : ℂ} (hz : 0 < z.im) (x r : ℝ) :
    logDeriv (fun w : ℂ => (w - (x : ℂ)) ^ (r : ℂ)) z = (r : ℂ) / (z - (x : ℂ)) := by
  have hslit := sub_ofReal_mem_slitPlane_of_im_pos hz x
  have hbase : z - (x : ℂ) ≠ 0 := slitPlane_ne_zero hslit
  have hpow : (z - (x : ℂ)) ^ (r : ℂ) ≠ 0 := sub_cpow_ne_zero_of_im_pos hz x r
  rw [logDeriv_apply,
    ((hasDerivAt_id' z).sub_const (x : ℂ)).cpow_const hslit |>.deriv,
    mul_one, Complex.cpow_sub _ _ hbase, Complex.cpow_one]
  field_simp

end TauCeti

end
