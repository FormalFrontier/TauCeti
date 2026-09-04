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

These are the basic branch facts for a factor of a product of principal powers with real base
points, such as the Schwarz--Christoffel integrand.

## Main results

* `TauCeti.sub_ofReal_mem_slitPlane_of_im_pos`
* `TauCeti.differentiableAt_sub_cpow_of_im_pos`
* `TauCeti.sub_cpow_ne_zero_of_im_pos`
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
