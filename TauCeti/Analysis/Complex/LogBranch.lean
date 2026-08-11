/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The principal logarithm across the branch cut

Negating a point in the open lower half-plane advances its principal logarithm by
`π·i`: the argument crosses the cut. This is the bookkeeping identity for logarithmic
primitives along contours that cross the negative real axis.

## Main declarations

* `TauCeti.log_neg_eq_log_add_pi_mul_I_of_im_neg`.
-/

public section

open Complex

namespace TauCeti

/-- For a point below the real axis, the logarithm of the negation gains `π·i`. -/
theorem log_neg_eq_log_add_pi_mul_I_of_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + Real.pi * Complex.I := by
  refine Complex.ext ?_ ?_
  · simp [Complex.log_re, Complex.add_re, Complex.mul_re]
  · simp [Complex.log_im, Complex.add_im, Complex.mul_im,
      Complex.arg_neg_eq_arg_add_pi_of_im_neg hz]

end TauCeti

end
