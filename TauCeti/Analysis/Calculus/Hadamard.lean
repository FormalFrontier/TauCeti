/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Smooth Hadamard factorization

This file develops the first-order factorization of a smooth map through displacement from a
basepoint. It is the analytic input for identifying point derivations on a finite-dimensional
smooth manifold with tangent vectors.

## References

* [Lie groups and the Lie algebra correspondence roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/LieGroups/README.md),
  Deliverable A, Layer 0, "The Lie algebra and the tangent space at `1`".
-/

public section

noncomputable section

open MeasureTheory

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- First-order Taylor expansion along a segment, with its coefficient bundled as a continuous
linear map. -/
theorem ContDiff.sub_eq_intervalIntegral_fderiv (f : E → F) (hf : ContDiff ℝ 1 f) (x y : E) :
    f y - f x =
      (∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • (y - x))) (y - x) := by
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv (n := 0) (x := x) (y := y - x)
    (fun _ _ ↦ hf.contDiffAt)
  have hIntegrable : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ f (x + t • (y - x)))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact (hf.fderiv_right (m := 0) (by norm_num)).continuous.comp (by fun_prop)
  rw [ContinuousLinearMap.intervalIntegral_apply hIntegrable (y - x)]
  simpa [sub_eq_iff_eq_add, add_comm] using hTaylor
