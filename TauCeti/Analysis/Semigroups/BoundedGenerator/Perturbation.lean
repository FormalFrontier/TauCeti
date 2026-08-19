/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.BoundedGenerator.Basic
import TauCeti.Analysis.SpecialFunctions.Exponential

/-!
# Comparing commuting bounded-generator semigroups

This file gives the perturbation estimate needed to compare the bounded semigroups in the
Yosida approximation. If bounded operators `A` and `B` commute and their exponentials are bounded
by `M` and `N` at nonnegative times, then

`‖exp (t A) x - exp (t B) x‖ ≤ M * N * t * ‖(A - B) x‖`.

The proof applies Duhamel's formula to the difference of the two exponentials. Commutativity
moves `A - B` through the second exponential, after which the two exponential factors contribute
their bounds. This pointwise estimate is sharper than the generic Banach-algebra bound involving
`exp (t ‖A‖)` and `exp (t ‖B‖)`; that generic bound is useless for Yosida approximations because
their operator norms grow with the approximation parameter.

The two constants are kept separate rather than fixed to one: the Yosida approximations of a
dissipative operator have contractive exponentials, but under the Hille--Yosida hypotheses for a
general growth constant `M` they only satisfy `‖exp (t A_lambda)‖ ≤ M`, and the resulting
comparison carries the factor `M ^ 2`.

## Main result

* `TauCeti.Semigroups.norm_exp_smul_sub_exp_smul_apply_le_of_commute`: the pointwise comparison
  estimate for commuting exponentials with uniform bounds.

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

/-- If `A` and `B` commute and their bounded-generator semigroups obey the uniform bounds `M` and
`N` at nonnegative times, then their orbits differ by at most

`‖exp (t A) x - exp (t B) x‖ ≤ M * N * t * ‖(A - B) x‖` for `t ≥ 0`.

This is the bounded Duhamel estimate in the commuting case; the contraction case is `M = N = 1`. -/
theorem norm_exp_smul_sub_exp_smul_apply_le_of_commute {M N : ℝ} (A B : X →L[ℝ] X)
    (hcomm : Commute A B)
    (hA : ∀ s : ℝ, 0 ≤ s → ‖exp (s • A)‖ ≤ M)
    (hB : ∀ s : ℝ, 0 ≤ s → ‖exp (s • B)‖ ≤ N)
    {t : ℝ} (ht : 0 ≤ t) (x : X) :
    ‖exp (t • A) x - exp (t • B) x‖ ≤ M * N * t * ‖(A - B) x‖ := by
  let +nondep : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ _
  have hN : 0 ≤ N := (norm_nonneg _).trans (hB 0 le_rfl)
  have hsum : t • A + t • (B - A) = t • B := by module
  have hint := TauCeti.intervalIntegrable_exp_smul_mul_mul_exp_smul
    (t • A + t • (B - A)) (t • (B - A)) (t • A)
  have hduhamel := TauCeti.exp_add_sub_exp_eq_integral (t • A) (t • (B - A))
  rw [hsum] at hint hduhamel
  have happly := congrArg (fun C : X →L[ℝ] X => C x) hduhamel
  rw [ContinuousLinearMap.intervalIntegral_apply hint x] at happly
  simp only [sub_apply] at happly
  rw [norm_sub_rev, happly]
  refine (intervalIntegral.norm_integral_le_of_norm_le_const
    (C := M * N * t * ‖(A - B) x‖) ?_).trans_eq ?_
  · intro s hs
    rw [uIoc_of_le zero_le_one] at hs
    have hs_nonneg : 0 ≤ s := hs.1.le
    have hone_sub_nonneg : 0 ≤ 1 - s := sub_nonneg.mpr hs.2
    have hmove :
        (t • (B - A)) * exp ((s * t) • A) = exp ((s * t) • A) * (t • (B - A)) :=
      (((hcomm.symm.sub_left (Commute.refl A)).smul_left t).smul_right (s * t)).exp_right.eq
    simp only [smul_smul]
    rw [mul_assoc, hmove]
    simp only [mul_apply_eq_comp]
    calc
      ‖exp (((1 - s) * t) • B) (exp ((s * t) • A) ((t • (B - A)) x))‖
          ≤ ‖exp (((1 - s) * t) • B)‖ *
              ‖exp ((s * t) • A) ((t • (B - A)) x)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ N * ‖exp ((s * t) • A) ((t • (B - A)) x)‖ := by
        gcongr
        exact hB ((1 - s) * t) (mul_nonneg hone_sub_nonneg ht)
      _ ≤ N * (M * ‖(t • (B - A)) x‖) :=
        mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right (hA (s * t) (mul_nonneg hs_nonneg ht)) (norm_nonneg _)))
          hN
      _ = M * N * t * ‖(A - B) x‖ := by
        rw [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht,
          ← neg_sub, neg_apply, norm_neg]
        ring
  · simp

end TauCeti.Semigroups

end
