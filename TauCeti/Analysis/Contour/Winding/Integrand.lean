/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# The real winding integrand

This file defines the pointwise real winding integrand and records its coordinate formula and
invariance under simultaneous nonzero complex scaling.

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

end TauCeti.Contour
