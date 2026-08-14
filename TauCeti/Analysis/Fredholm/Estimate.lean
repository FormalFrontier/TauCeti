/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Analysis.Normed.Operator.ClosedRange

/-!
# The a priori estimate of a Fredholm operator

A Fredholm operator `T : E →L[𝕜] F` has closed range and a finite-dimensional, topologically
complemented kernel, so the general estimate of `TauCeti.Analysis.Normed.Operator.ClosedRange`
applies to it: there is a continuous projection `P` of `E` onto `ker T` and a constant `C > 0` with

`‖x‖ ≤ C * ‖T x‖ + ‖P x‖`.

Because `ker T` is finite-dimensional, the correction term `‖P x‖` ranges over a locally compact
direction; this is what makes the estimate a compactness statement rather than a mere operator
bound, and it is the linear input to Smale's local properness lemma, which
`TauCeti.Analysis.Fredholm.Proper` reads off the same estimate.

## Main declarations

* `ContinuousLinearMap.IsFredholm.exists_projection_norm_le_mul_norm_add_norm`: the a priori
  estimate of a Fredholm operator, phrased against `ContinuousLinearMap.IsFredholm` as
  `TauCeti.Analysis.Fredholm.Basic` prescribes.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **The a priori estimate of a Fredholm operator**: there is a continuous projection `P` of `E`
onto `ker T` and a constant `C > 0` with `‖x‖ ≤ C * ‖T x‖ + ‖P x‖`.

This is `ContinuousLinearMap.exists_projection_norm_le_mul_norm_add_norm`, which needs only a
closed range and a complemented kernel, specialised to a Fredholm operator. -/
theorem _root_.ContinuousLinearMap.IsFredholm.exists_projection_norm_le_mul_norm_add_norm
    {T : E →L[𝕜] F} (hT : T.IsFredholm) :
    ∃ (P : E →L[𝕜] E) (C : ℝ), 0 < C ∧ IsIdempotentElem P ∧ P.range = T.ker ∧
      ∀ x, ‖x‖ ≤ C * ‖T x‖ + ‖P x‖ :=
  T.exists_projection_norm_le_mul_norm_add_norm hT.isClosed_range hT.closedComplemented_ker

end TauCeti
