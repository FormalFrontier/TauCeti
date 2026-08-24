/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-!
# The increment of a function along a segment

This file bounds the increment of a function between `x` and `x + h` by the integral of its
directional derivative along the segment joining them. It is the multi-dimensional form of
Mathlib's one-dimensional `enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc`, obtained by
composing with the affine parametrization `t ↦ x + t • h` of the segment.

The hypotheses are local to the segment: differentiability at each of its points and continuity
of the directional derivative along it.

## Main declarations

* `TauCeti.enorm_sub_le_lintegral_enorm_fderiv_apply`: the segment increment estimate.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, where this is the starting point of the
difference-quotient characterization of Sobolev functions.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F}

/-- **The segment increment estimate**: the norm of `u (x + h) - u x` is at most the integral
along the segment from `x` to `x + h` of the norm of the directional derivative
`Du(x + t • h) h`. -/
theorem enorm_sub_le_lintegral_enorm_fderiv_apply (x h : E)
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ u (x + t • h))
    (hc : ContinuousOn (fun t : ℝ => fderiv ℝ u (x + t • h) h) (Icc 0 1)) :
    ‖u (x + h) - u x‖ₑ ≤ ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ := by
  have hline : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fun s : ℝ => u (x + s • h)) t := by
    intro t ht
    simpa [Function.comp_def] using (hd t ht).comp t
      (by fun_prop : DifferentiableAt ℝ (fun s : ℝ => x + s • h) t)
  have hderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      derivWithin (fun s : ℝ => u (x + s • h)) (Icc 0 1) t =
        fderiv ℝ u (x + t • h) h := by
    intro t ht
    rw [(hline t ht).derivWithin ((uniqueDiffOn_Icc zero_lt_one).uniqueDiffWithinAt ht),
      (hd t ht).deriv_comp_add_smul]
  have hC1 : ContDiffOn ℝ 1 (fun s : ℝ => u (x + s • h)) (Icc 0 1) := by
    rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc zero_lt_one)]
    exact ⟨fun t ht => (hline t ht).differentiableWithinAt,
      hc.congr hderiv⟩
  have h01 := enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc hC1 zero_le_one
  calc
    ‖u (x + h) - u x‖ₑ ≤
        ∫⁻ t in Icc (0 : ℝ) 1,
          ‖derivWithin (fun s : ℝ => u (x + s • h)) (Icc 0 1) t‖ₑ := by
      simpa using h01
    _ = ∫⁻ t in Icc (0 : ℝ) 1, ‖fderiv ℝ u (x + t • h) h‖ₑ :=
      setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hderiv t ht]

end TauCeti
