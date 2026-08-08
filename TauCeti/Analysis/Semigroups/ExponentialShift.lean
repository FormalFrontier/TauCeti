/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.GrowthBound

/-!
# Exponential shifts of strongly continuous semigroups

This file defines the exponentially shifted C₀-semigroup
`t ↦ exp (-lambda t) • S(t)`.  Shifting is the standard way to move a growth bound
`(ω, M)` to `(ω - lambda, M)`, and in particular to turn a semigroup with bound
`(lambda, 1)` into a contraction semigroup.

## References
The construction is standard in the Hille--Yosida theory of C₀-semigroups; see
Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Ch. II.
-/

public section

noncomputable section

open scoped NNReal

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

omit [CompleteSpace X] in
/-- The exponential shift of a C₀-semigroup by `lambda`.

At nonnegative time `t`, this is the semigroup `exp (-lambda t) • S(t)`.  It shifts
growth exponents by subtracting `lambda`; see `HasGrowthBound.expShift`. -/
def expShift (S : StronglyContinuousSemigroup X) (lambda : ℝ) :
    StronglyContinuousSemigroup X where
  toFun t := Real.exp (-(lambda * (t : ℝ))) • S t
  map_zero' := by
    rw [NNReal.coe_zero, mul_zero, neg_zero, Real.exp_zero, one_smul, S.map_zero]
  map_add' s t := by
    ext x
    simp only [NNReal.coe_add, ContinuousLinearMap.comp_apply, smul_apply]
    rw [S.map_add_apply, map_smul, smul_smul]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  continuousAt_zero' x := by
    have h_exp : Filter.Tendsto (fun t : ℝ≥0 => Real.exp (-(lambda * (t : ℝ))))
        (nhds 0) (nhds 1) := by
      have h_cont : ContinuousAt (fun t : ℝ≥0 => Real.exp (-(lambda * (t : ℝ)))) 0 :=
        (Real.continuous_exp.comp ((continuous_const.mul continuous_subtype_val).neg)).continuousAt
      simpa using h_cont.tendsto
    have h_orbit := S.continuousAt_zero_tendsto x
    simpa [ContinuousAt, S.map_zero_apply] using h_exp.smul h_orbit

omit [CompleteSpace X] in
/-- The native nonnegative-time operator of the exponential shift. -/
@[simp]
theorem expShift_apply (S : StronglyContinuousSemigroup X) (lambda : ℝ) (t : ℝ≥0) :
    S.expShift lambda t = Real.exp (-(lambda * (t : ℝ))) • S t := by
  rw [expShift]; rfl

omit [CompleteSpace X] in
/-- Pointwise form of `StronglyContinuousSemigroup.expShift_apply`. -/
theorem expShift_apply_apply (S : StronglyContinuousSemigroup X) (lambda : ℝ) (t : ℝ≥0) (x : X) :
    S.expShift lambda t x = Real.exp (-(lambda * (t : ℝ))) • S t x :=
  by rw [expShift_apply, smul_apply]

omit [CompleteSpace X] in
/-- The zero exponential shift is the original semigroup. -/
@[simp]
theorem expShift_zero (S : StronglyContinuousSemigroup X) :
    S.expShift 0 = S := by
  ext t x
  simp

omit [CompleteSpace X] in
/-- Successive exponential shifts add their parameters. -/
@[simp]
theorem expShift_expShift (S : StronglyContinuousSemigroup X) (lambda μ : ℝ) :
    (S.expShift lambda).expShift μ = S.expShift (lambda + μ) := by
  ext t x
  simp only [expShift_apply_apply]
  rw [smul_smul, ← Real.exp_add]
  congr 1
  ring_nf

omit [CompleteSpace X] in
/-- Real-time form of the shifted operator at nonnegative times. -/
theorem expShift_realOperator_of_nonneg (S : StronglyContinuousSemigroup X)
    (lambda t : ℝ) (ht : 0 ≤ t) :
    (S.expShift lambda).realOperator t = Real.exp (-(lambda * t)) • S.realOperator t := by
  have ht_coe : ((t.toNNReal : ℝ) = t) := Real.coe_toNNReal t ht
  rw [← ht_coe, realOperator_coe, realOperator_coe, expShift_apply]

omit [CompleteSpace X] in
/-- Pointwise real-time form of the shifted operator at nonnegative times. -/
theorem expShift_realOperator_apply_of_nonneg (S : StronglyContinuousSemigroup X)
    (lambda t : ℝ) (ht : 0 ≤ t) (x : X) : (S.expShift lambda).realOperator t x =
      Real.exp (-(lambda * t)) • S.realOperator t x := by
  rw [S.expShift_realOperator_of_nonneg lambda t ht]
  rw [smul_apply]

namespace HasGrowthBound

omit [CompleteSpace X] in
/-- Exponential shifting subtracts the shift parameter from the growth exponent. -/
theorem expShift {S : StronglyContinuousSemigroup X} {ω M lambda : ℝ}
    (hb : S.HasGrowthBound ω M) : (S.expShift lambda).HasGrowthBound (ω - lambda) M := by
  refine StronglyContinuousSemigroup.hasGrowthBound_of_bound hb.one_le (fun t ht => ?_)
  rw [S.expShift_realOperator_of_nonneg lambda t ht]
  calc ‖Real.exp (-(lambda * t)) • S.realOperator t‖
      ≤ ‖Real.exp (-(lambda * t))‖ * ‖S.realOperator t‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
    _ = Real.exp (-(lambda * t)) * ‖S.realOperator t‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    _ ≤ Real.exp (-(lambda * t)) * (M * Real.exp (ω * t)) :=
        mul_le_mul_of_nonneg_left (hb.bound t ht) (Real.exp_nonneg _)
    _ = M * (Real.exp (-(lambda * t)) * Real.exp (ω * t)) := by ring
    _ = M * Real.exp ((ω - lambda) * t) := by
        rw [← Real.exp_add]
        congr 1
        ring_nf

end HasGrowthBound

omit [CompleteSpace X] in
/-- A semigroup with growth bound `(lambda, 1)` becomes a contraction semigroup after
exponential shifting by `lambda`. -/
def expShiftContraction (S : StronglyContinuousSemigroup X) (lambda : ℝ)
    (hb : S.HasGrowthBound lambda 1) : ContractionSemigroup X where
  toStronglyContinuousSemigroup := S.expShift lambda
  contracting t := by
    have h := hb.expShift (lambda := lambda)
    have hbound := h.bound (t : ℝ) (by exact_mod_cast t.2)
    rw [realOperator_coe] at hbound
    rw [sub_self, zero_mul, Real.exp_zero, mul_one] at hbound
    exact hbound

omit [CompleteSpace X] in
/-- The C₀-semigroup underlying `expShiftContraction` is the exponential shift. -/
@[simp]
theorem expShiftContraction_toStronglyContinuousSemigroup
    (S : StronglyContinuousSemigroup X) (lambda : ℝ) (hb : S.HasGrowthBound lambda 1) :
    (S.expShiftContraction lambda hb).toStronglyContinuousSemigroup = S.expShift lambda := by
  rw [expShiftContraction]

omit [CompleteSpace X] in
/-- Native operator formula for `expShiftContraction`. -/
@[simp]
theorem expShiftContraction_apply (S : StronglyContinuousSemigroup X) (lambda : ℝ)
    (hb : S.HasGrowthBound lambda 1) (t : ℝ≥0) :
    S.expShiftContraction lambda hb t = Real.exp (-(lambda * (t : ℝ))) • S t :=
  by
    calc
      S.expShiftContraction lambda hb t =
          (S.expShiftContraction lambda hb).toStronglyContinuousSemigroup t := rfl
      _ = Real.exp (-(lambda * (t : ℝ))) • S t := by
          rw [expShiftContraction_toStronglyContinuousSemigroup, expShift_apply]

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end
