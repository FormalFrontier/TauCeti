/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Continuity of `arg` and `log` on the closed upper half-plane

The principal argument and logarithm are continuous on the punctured closed upper
half-plane `{z | 0 ≤ im z ∧ z ≠ 0}`. This strengthens Mathlib's continuity on the open
slit plane: the negative real axis is allowed because the approach is confined to
nonnegative imaginary parts, where `arg` agrees with the continuous `arccos` formula.
It is the boundary-tolerant ingredient for logarithmic primitives along contours that
touch the slit-plane boundary.

## Main declarations

* `TauCeti.continuousOn_arg_im_nonneg_ne_zero`.
* `TauCeti.continuousOn_log_im_nonneg_ne_zero`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development (`ForMathlib/ValenceFormula/WindingWeights/Common.lean`) this file ports
  onto the current Mathlib pin.
-/

public section

open Complex

namespace TauCeti

/-- The principal argument is continuous on the punctured closed upper half-plane: the
approach is confined to nonnegative imaginary parts, where `arg` is the `arccos` of the
normalized real part. -/
@[fun_prop]
theorem continuousOn_arg_im_nonneg_ne_zero :
    ContinuousOn Complex.arg {z : ℂ | 0 ≤ z.im ∧ z ≠ 0} := by
  rintro z ⟨hz_im, hz_ne⟩
  exact ContinuousWithinAt.congr
    ((continuous_re.continuousWithinAt.div continuous_norm.continuousWithinAt
      (norm_ne_zero_iff.mpr hz_ne)).arccos)
    (fun w ⟨hw_im, hw_ne⟩ ↦ Complex.arg_of_im_nonneg_of_ne_zero hw_im hw_ne)
    (Complex.arg_of_im_nonneg_of_ne_zero hz_im hz_ne)

/-- The principal logarithm is continuous on the punctured closed upper half-plane. -/
@[fun_prop]
theorem continuousOn_log_im_nonneg_ne_zero :
    ContinuousOn Complex.log {z : ℂ | 0 ≤ z.im ∧ z ≠ 0} := by
  have hlog : Complex.log = fun w ↦ ↑(Real.log ‖w‖) + ↑(Complex.arg w) * Complex.I :=
    funext fun w ↦ Complex.ext (by simp [Complex.log_re]) (by simp [Complex.log_im])
  rw [hlog]
  rintro z ⟨hz_im, hz_ne⟩
  refine ContinuousWithinAt.add ?_ ?_
  · exact (continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_log (norm_ne_zero_iff.mpr hz_ne)).comp
        continuous_norm.continuousAt)).continuousWithinAt
  · exact (continuous_ofReal.continuousAt.comp_continuousWithinAt
      (continuousOn_arg_im_nonneg_ne_zero z ⟨hz_im, hz_ne⟩)).mul continuousWithinAt_const

end TauCeti

end
