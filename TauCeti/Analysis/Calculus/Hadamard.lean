/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
public import TauCeti.Analysis.Calculus.ParametricIntegral

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
open scoped ContDiff

universe u v

variable {E : Type u} {F : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The averaged derivative along the segment from `x` to `y`. -/
noncomputable def hadamardFactor [CompleteSpace F] (f : E → F) (x y : E) : E →L[ℝ] F :=
  ∫ t in (0 : ℝ)..1, fderiv ℝ f (x + t • (y - x))

/-- The averaged derivative written as an integral over the compact unit interval. -/
theorem hadamardFactor_eq_integral_Icc [CompleteSpace F] (f : E → F) (x : E) :
    hadamardFactor f x = fun y ↦ ∫ t in Set.Icc (0 : ℝ) 1,
      fderiv ℝ f (x + t • (y - x)) := by
  funext y
  rw [hadamardFactor, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc]

/-- At the basepoint, the averaged derivative is the ordinary derivative. -/
@[simp]
theorem hadamardFactor_self [CompleteSpace F] (f : E → F) (x : E) :
    hadamardFactor f x x = fderiv ℝ f x := by
  simp [hadamardFactor]

/-- If `f` is `n + 1` times continuously differentiable, its Hadamard factor is `n` times
continuously differentiable in the endpoint. -/
theorem ContDiff.contDiff_hadamardFactor_of_succ
    {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ∞) (f : E → F) (hf : ContDiff ℝ (n + 1) f) (x : E) :
    ContDiff ℝ n (hadamardFactor f x) := by
  rw [hadamardFactor_eq_integral_Icc]
  apply contDiff_integral_Icc_of_contDiff n
  have hd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (m := n) (by norm_num)
  exact hd.comp <| by fun_prop

/-- First-order Taylor expansion along a segment, with its coefficient bundled as a continuous
linear map. -/
theorem ContDiff.sub_eq_hadamardFactor_apply [CompleteSpace F]
    (f : E → F) (hf : ContDiff ℝ 1 f) (x y : E) :
    f y - f x = hadamardFactor f x y (y - x) := by
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv (n := 0) (x := x) (y := y - x)
    (fun _ _ ↦ hf.contDiffAt)
  have hIntegrable : IntervalIntegrable (fun t : ℝ ↦ fderiv ℝ f (x + t • (y - x)))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact (hf.fderiv_right (m := 0) (by norm_num)).continuous.comp (by fun_prop)
  rw [hadamardFactor, ContinuousLinearMap.intervalIntegral_apply hIntegrable (y - x)]
  simpa [sub_eq_iff_eq_add, add_comm] using hTaylor

/-- For a smooth function, the averaged derivative in Hadamard's factorization depends smoothly on
the endpoint. -/
theorem ContDiff.contDiff_hadamardFactor [CompleteSpace F] (f : E → F)
    (hf : ContDiff ℝ ∞ f)
    (x : E) : ContDiff ℝ ∞ (hadamardFactor f x) := by
  simpa using ContDiff.contDiff_hadamardFactor_of_succ (⊤ : ℕ∞) f (by simpa using hf) x
