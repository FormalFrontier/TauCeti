/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.BoundedGenerator.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Comparing commuting bounded-generator semigroups

This file gives the perturbation estimate needed to compare the bounded semigroups in the
Yosida approximation. If bounded operators `A` and `B` commute and both exponentials are
contractive at nonnegative times, then

`‖exp (t A) x - exp (t B) x‖ ≤ t ‖(A - B) x‖`.

The proof differentiates the interpolation

`s ↦ exp ((t - s) A) (exp (s B) x)`

on `[0, t]`. Commutativity moves `A - B` through the second exponential, after which both
exponential factors are bounded by one. This pointwise estimate is sharper than the generic
Banach-algebra bound involving `exp (t ‖A‖)` and `exp (t ‖B‖)`; that generic bound is useless
for Yosida approximations because their operator norms grow with the approximation parameter.

## Main result

* `TauCeti.Semigroups.norm_exp_smul_sub_exp_smul_apply_le_of_commute`: the pointwise comparison
  estimate for commuting contraction exponentials.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.3.5;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 1.
-/

public section

noncomputable section

open NormedSpace Set

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

private theorem hasDerivAt_exp_interpolation (A B : X →L[ℝ] X) (hcomm : Commute A B)
    (t s : ℝ) (x : X) :
    HasDerivAt
      (fun u : ℝ => (exp ((t - u) • A) * exp (u • B)) x)
      ((exp ((t - s) • A) * exp (s • B) * (B - A)) x) s := by
  have hA := HasDerivAt.comp_const_sub t s (hasDerivAt_exp_smul_const A (t - s))
  have hB := hasDerivAt_exp_smul_const B s
  have hAexpB : Commute A (exp (s • B)) := (hcomm.smul_right s).exp_right
  have hderiv :
      -(exp ((t - s) • A) * A) * exp (s • B) +
          exp ((t - s) • A) * (exp (s • B) * B) =
        exp ((t - s) • A) * exp (s • B) * (B - A) := by
    calc
      -(exp ((t - s) • A) * A) * exp (s • B) +
          exp ((t - s) • A) * (exp (s • B) * B)
          = -(exp ((t - s) • A) * exp (s • B) * A) +
              exp ((t - s) • A) * exp (s • B) * B := by
            rw [neg_mul, mul_assoc (exp ((t - s) • A)) A, hAexpB.eq,
              ← mul_assoc, ← mul_assoc]
      _ = exp ((t - s) • A) * exp (s • B) * (B - A) := by
        rw [mul_sub]
        abel
  have hBx : HasDerivAt (fun u : ℝ => exp (u • B) x)
      ((exp (s • B) * B) x) s := by
    simpa only [map_zero, add_zero] using hB.clm_apply (hasDerivAt_const s x)
  have hinterpolation := hA.clm_apply hBx
  have hderiv_apply := congrArg (fun T : X →L[ℝ] X => T x) hderiv
  simp only [add_apply, mul_apply_eq_comp, neg_apply] at hderiv_apply
  have hinterpolation' : HasDerivAt
      (fun u : ℝ => exp ((t - u) • A) (exp (u • B) x))
      (-(exp ((t - s) • A) (A (exp (s • B) x))) +
        exp ((t - s) • A) (exp (s • B) (B x))) s := by
    simpa only [mul_apply_eq_comp, neg_apply] using hinterpolation
  rw [hderiv_apply] at hinterpolation'
  simpa only [mul_apply_eq_comp] using hinterpolation'

/-- If `A` and `B` commute and their bounded-generator semigroups are contractive, then their
orbits differ by at most time times the difference of the generators:

`‖exp (t A) x - exp (t B) x‖ ≤ t ‖(A - B) x‖` for `t ≥ 0`.

This is the bounded Duhamel estimate in the commuting case. -/
theorem norm_exp_smul_sub_exp_smul_apply_le_of_commute (A B : X →L[ℝ] X)
    (hcomm : Commute A B)
    (hA : ∀ s : ℝ, 0 ≤ s → ‖exp (s • A)‖ ≤ 1)
    (hB : ∀ s : ℝ, 0 ≤ s → ‖exp (s • B)‖ ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (x : X) :
    ‖exp (t • A) x - exp (t • B) x‖ ≤ t * ‖(A - B) x‖ := by
  let f : ℝ → X := fun s => (exp ((t - s) • A) * exp (s • B)) x
  let f' : ℝ → X := fun s => (exp ((t - s) • A) * exp (s • B) * (B - A)) x
  have hderiv : ∀ s ∈ Icc (0 : ℝ) t, HasDerivWithinAt f (f' s) (Icc 0 t) s :=
    fun s _ => (hasDerivAt_exp_interpolation A B hcomm t s x).hasDerivWithinAt
  have hbound : ∀ s ∈ Ico (0 : ℝ) t, ‖f' s‖ ≤ ‖(A - B) x‖ := by
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1
    have hts_nonneg : 0 ≤ t - s := sub_nonneg.mpr hs.2.le
    simp only [f', mul_apply_eq_comp]
    calc
      ‖exp ((t - s) • A) (exp (s • B) ((B - A) x))‖
          ≤ ‖exp ((t - s) • A)‖ * ‖exp (s • B) ((B - A) x)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * ‖exp (s • B) ((B - A) x)‖ := by
        gcongr
        exact hA (t - s) hts_nonneg
      _ ≤ 1 * (1 * ‖(B - A) x‖) := by
        gcongr
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hB s hs_nonneg) (norm_nonneg _))
      _ = ‖(A - B) x‖ := by
        rw [one_mul, one_mul, ← neg_sub, neg_apply, norm_neg]
  have hestimate := norm_image_sub_le_of_norm_deriv_le_segment' hderiv hbound t
    (right_mem_Icc.mpr ht)
  have hf_zero : f 0 = exp (t • A) x := by
    simp [f]
  have hf_t : f t = exp (t • B) x := by
    simp [f]
  rw [hf_t, hf_zero, sub_zero] at hestimate
  simpa only [norm_sub_rev, mul_comm] using hestimate

end TauCeti.Semigroups

end
