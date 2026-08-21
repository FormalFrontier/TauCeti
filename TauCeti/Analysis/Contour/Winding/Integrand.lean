/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# The real winding integrand

This file defines the pointwise real winding integrand and records its coordinate formula,
invariance under simultaneous nonzero complex scaling, velocity negation, vanishing at the
origin, and a crude bound away from the origin.

## Provenance

The pointwise imaginary-part decomposition is migrated and cleaned from the AINTLIB
`LeanModularForms` generalized-winding-number development.
-/

public section

namespace TauCeti.Contour

/-- The real winding integrand `(x ẏ - y ẋ) / (x² + y²)` for a position `z = x + iy`
and velocity `v = ẋ + iẏ`. It is defined as the imaginary part `(z⁻¹ * v).im` of the complex
winding integrand; in particular it is `0` at `z = 0`. Its relation to the complex integrand is
`realWindingIntegrand_def` and its coordinate form is `realWindingIntegrand_eq_div`. -/
public noncomputable def realWindingIntegrand (z v : ℂ) : ℝ := (z⁻¹ * v).im

/-- The real winding integrand is the imaginary part of the complex winding integrand `z⁻¹ * v`.
This is a convenient public rewrite lemma relating the real integrand to the complex index
integrand `(γ - w)⁻¹ * γ'`. -/
theorem realWindingIntegrand_def (z v : ℂ) :
    realWindingIntegrand z v = (z⁻¹ * v).im := by
  rw [realWindingIntegrand]

/-- The coordinate formula for the real winding integrand. -/
@[simp] theorem realWindingIntegrand_eq_div (z v : ℂ) :
    realWindingIntegrand z v =
      (z.re * v.im - z.im * v.re) / Complex.normSq z := by
  rw [realWindingIntegrand_def, inv_mul_eq_div, Complex.div_im]
  ring

/-- Scaling position and velocity by the same nonzero complex parameter leaves the real winding
integrand unchanged: it is the imaginary part of `(c * z)⁻¹ * (c * v) = z⁻¹ * v`, where the two
factors of `c` cancel in `ℂ`. -/
theorem realWindingIntegrand_mul_mul {c : ℂ} (hc : c ≠ 0) (z v : ℂ) :
    realWindingIntegrand (c * z) (c * v) = realWindingIntegrand z v := by
  rw [realWindingIntegrand_def, realWindingIntegrand_def, mul_inv_rev,
    mul_assoc, inv_mul_cancel_left₀ hc]

/-- Negating the velocity while keeping the position fixed negates the real winding integrand:
it is the imaginary part of `z⁻¹ * (-v) = -(z⁻¹ * v)`. -/
theorem realWindingIntegrand_neg_right (z v : ℂ) :
    realWindingIntegrand z (-v) = -realWindingIntegrand z v := by
  simp only [realWindingIntegrand_eq_div, Complex.neg_im, Complex.neg_re]; ring

/-- **A crude bound on the real winding integrand.** `realWindingIntegrand z v = (z⁻¹ * v).im`,
whose absolute value is at most `‖z⁻¹ * v‖ = ‖v‖ / ‖z‖` -- including at `z = 0`, where both sides
vanish (`simp [realWindingIntegrand_eq_div]`, `div_zero`). -/
theorem abs_realWindingIntegrand_le_div_norm (z v : ℂ) :
    |realWindingIntegrand z v| ≤ ‖v‖ / ‖z‖ := by
  rw [realWindingIntegrand_def]
  calc |(z⁻¹ * v).im| ≤ ‖z⁻¹ * v‖ := Complex.abs_im_le_norm _
    _ = ‖v‖ / ‖z‖ := by rw [norm_mul, norm_inv, mul_comm, ← div_eq_mul_inv]

/-- **The crude bound above, weakened to a uniform denominator** `m ≤ ‖z‖` away from the
singularity. -/
theorem abs_realWindingIntegrand_le_div_of_le_norm {z v : ℂ} {m : ℝ} (hm : 0 < m)
    (hz : m ≤ ‖z‖) : |realWindingIntegrand z v| ≤ ‖v‖ / m :=
  (abs_realWindingIntegrand_le_div_norm z v).trans (by gcongr)

end TauCeti.Contour
