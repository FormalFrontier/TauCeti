/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.BoundedGenerator.Basic
public import TauCeti.Analysis.Semigroups.Dissipative.Basic

/-!
# Yosida approximations

This file constructs the bounded approximations used in the generation theorems for strongly
continuous semigroups. For an m-dissipative operator `A` and `lambda > 0`, its Yosida
approximation is

`A_lambda = lambda ^ 2 R(lambda, A) - lambda I = lambda A R(lambda, A)`.

The resolvent estimate makes `lambda R(lambda, A)` a contraction. Splitting the exponential of
`t A_lambda` into the commuting scalar and resolvent parts then proves that
`exp (t A_lambda)` is a contraction for every `t ≥ 0`. Thus each approximation generates a
uniformly continuous contraction semigroup. This is the bounded stage of the Yosida construction;
the later generation argument proves that these semigroups are Cauchy uniformly on compact time
intervals before defining their limit.

## Main results

* `TauCeti.Semigroups.yosidaApproximation`: the bounded operator `A_lambda`.
* `TauCeti.Semigroups.yosidaApproximation_eq_smul_apply_resolvent`: the identity
  `A_lambda x = lambda A R(lambda, A) x`.
* `TauCeti.Semigroups.yosidaSemigroup`: the uniformly continuous contraction semigroup generated
  by `A_lambda`.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section II.3.5;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 1.
-/

public section

noncomputable section

namespace TauCeti.Semigroups

open NormedSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The **Yosida approximation** of an unbounded operator `A` at `lambda`:
`A_lambda = lambda ^ 2 R(lambda, A) - lambda I`.

The definition is meaningful when `lambda` belongs to the resolvent set of `A`; the theorems in
this file obtain that membership from m-dissipativity and `lambda > 0`. -/
def yosidaApproximation (A : X →ₗ.[ℝ] X) (lambda : ℝ) : X →L[ℝ] X :=
  lambda ^ 2 • LinearPMap.resolvent A lambda - lambda • 1

omit [CompleteSpace X] in
/-- Pointwise form of the definition of the Yosida approximation. -/
@[simp]
theorem yosidaApproximation_apply (A : X →ₗ.[ℝ] X) (lambda : ℝ) (x : X) :
    yosidaApproximation A lambda x =
      lambda ^ 2 • LinearPMap.resolvent A lambda x - lambda • x := by
  simp [yosidaApproximation]

/-- The Yosida approximation is `lambda A R(lambda, A)` pointwise. -/
theorem yosidaApproximation_eq_smul_apply_resolvent {A : X →ₗ.[ℝ] X}
    (hA : IsMDissipative A) {lambda : ℝ} (hlambda : 0 < lambda) (x : X) :
    yosidaApproximation A lambda x = lambda • A ⟨LinearPMap.resolvent A lambda x,
      LinearPMap.resolvent_mem_domain (hA.mem_resolventSet hlambda) x⟩ := by
  rw [yosidaApproximation_apply, LinearPMap.apply_resolvent (hA.mem_resolventSet hlambda)]
  module

/-- The rescaled resolvent `lambda R(lambda, A)` of an m-dissipative operator is a contraction. -/
theorem norm_smul_resolvent_le_one {A : X →ₗ.[ℝ] X} (hA : IsMDissipative A)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ‖lambda • LinearPMap.resolvent A lambda‖ ≤ 1 := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
  calc
    lambda * ‖LinearPMap.resolvent A lambda‖ ≤ lambda * lambda⁻¹ := by
      gcongr
      exact hA.norm_resolvent_le hlambda
    _ = 1 := mul_inv_cancel₀ hlambda.ne'

/-- The Yosida approximation has the elementary bound `‖A_lambda‖ ≤ 2 lambda`. -/
theorem norm_yosidaApproximation_le {A : X →ₗ.[ℝ] X} (hA : IsMDissipative A)
    {lambda : ℝ} (hlambda : 0 < lambda) : ‖yosidaApproximation A lambda‖ ≤ 2 * lambda := by
  rw [yosidaApproximation]
  calc
    ‖lambda ^ 2 • LinearPMap.resolvent A lambda - lambda • 1‖
        ≤ ‖lambda ^ 2 • LinearPMap.resolvent A lambda‖ + ‖lambda • (1 : X →L[ℝ] X)‖ :=
      norm_sub_le _ _
    _ ≤ lambda ^ 2 * lambda⁻¹ + lambda := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlambda,
        abs_of_nonneg (sq_nonneg lambda)]
      have hone : ‖(1 : X →L[ℝ] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hA.norm_resolvent_le hlambda) (sq_nonneg lambda))
        (by simpa using mul_le_mul_of_nonneg_left hone hlambda.le)
    _ = 2 * lambda := by field_simp; ring

private theorem exp_yosidaApproximation_eq {A : X →ₗ.[ℝ] X} (lambda t : ℝ) :
    exp (t • yosidaApproximation A lambda) =
      exp ((-(t * lambda)) • (1 : X →L[ℝ] X)) *
        exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda) := by
  have hsplit : t • yosidaApproximation A lambda =
      (-(t * lambda)) • (1 : X →L[ℝ] X) +
        (t * lambda ^ 2) • LinearPMap.resolvent A lambda := by
    rw [yosidaApproximation, smul_sub]
    module
  rw [hsplit]
  exact exp_add_of_commute_of_mem_ball (𝕂 := ℝ) (Commute.one_left _ |>.smul_left _ |>.smul_right _)
    ((expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)

omit [CompleteSpace X] in
private theorem exp_smul_one_eq (c : ℝ) :
    exp (c • (1 : X →L[ℝ] X)) = Real.exp c • 1 := by
  calc
    exp (c • (1 : X →L[ℝ] X)) = exp (algebraMap ℝ (X →L[ℝ] X) c) := by
      rw [Algebra.smul_def, mul_one]
    _ = algebraMap ℝ (X →L[ℝ] X) (exp c) := (algebraMap_exp_comm c).symm
    _ = Real.exp c • 1 := by
      rw [Real.exp_eq_exp_ℝ, Algebra.smul_def, mul_one]

/-- The exponential of a positive-time multiple of a Yosida approximation is contractive. -/
theorem norm_exp_yosidaApproximation_le_one {A : X →ₗ.[ℝ] X} (hA : IsMDissipative A)
    {lambda t : ℝ} (hlambda : 0 < lambda) (ht : 0 ≤ t) :
    ‖exp (t • yosidaApproximation A lambda)‖ ≤ 1 := by
  calc
    ‖exp (t • yosidaApproximation A lambda)‖ =
        ‖exp ((-(t * lambda)) • (1 : X →L[ℝ] X)) *
          exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖ := by
      rw [exp_yosidaApproximation_eq]
    _ ≤ ‖exp ((-(t * lambda)) • (1 : X →L[ℝ] X))‖ *
          ‖exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖ := norm_mul_le _ _
    _ = Real.exp (-(t * lambda)) * ‖(1 : X →L[ℝ] X)‖ *
          ‖exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖ := by
      rw [exp_smul_one_eq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.exp_nonneg _)]
    _
        ≤ Real.exp (-(t * lambda)) *
          Real.exp ‖(t * lambda ^ 2) • LinearPMap.resolvent A lambda‖ := by
      have hone : ‖(1 : X →L[ℝ] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      have hexp := StronglyContinuousSemigroup.norm_exp_le_exp_norm
        ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)
      calc
        Real.exp (-(t * lambda)) * ‖(1 : X →L[ℝ] X)‖ *
            ‖exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖
            ≤ Real.exp (-(t * lambda)) * 1 *
              ‖exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖ := by gcongr
        _ ≤ Real.exp (-(t * lambda)) * 1 *
              Real.exp ‖(t * lambda ^ 2) • LinearPMap.resolvent A lambda‖ := by gcongr
        _ = Real.exp (-(t * lambda)) *
              Real.exp ‖(t * lambda ^ 2) • LinearPMap.resolvent A lambda‖ := by ring
    _ ≤ Real.exp (-(t * lambda)) * Real.exp (t * lambda) := by
      gcongr
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ t * lambda ^ 2)]
      calc
        t * lambda ^ 2 * ‖LinearPMap.resolvent A lambda‖
            = t * lambda * (lambda * ‖LinearPMap.resolvent A lambda‖) := by ring
        _ ≤ t * lambda * 1 := by
          gcongr
          simpa [norm_smul, Real.norm_eq_abs, abs_of_pos hlambda] using
            norm_smul_resolvent_le_one hA hlambda
        _ = t * lambda := mul_one _
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The uniformly continuous contraction semigroup generated by the Yosida approximation. -/
def yosidaSemigroup (A : X →ₗ.[ℝ] X) (hA : IsMDissipative A) (lambda : ℝ)
    (hlambda : 0 < lambda) : ContractionSemigroup X where
  toStronglyContinuousSemigroup := StronglyContinuousSemigroup.ofBounded
    (yosidaApproximation A lambda)
  contracting t := by
    calc
      ‖(StronglyContinuousSemigroup.ofBounded (yosidaApproximation A lambda)).toFun t‖ =
          ‖exp ((t : ℝ) • yosidaApproximation A lambda)‖ :=
        congrArg norm (StronglyContinuousSemigroup.ofBounded_apply _ t)
      _ ≤ 1 := norm_exp_yosidaApproximation_le_one hA hlambda t.property

/-- The Yosida semigroup is the exponential of the Yosida approximation. -/
@[simp]
theorem yosidaSemigroup_apply (A : X →ₗ.[ℝ] X) (hA : IsMDissipative A) (lambda : ℝ)
    (hlambda : 0 < lambda) (t : NNReal) :
    yosidaSemigroup A hA lambda hlambda t = exp ((t : ℝ) • yosidaApproximation A lambda) :=
  StronglyContinuousSemigroup.ofBounded_apply _ _

/-- The Yosida semigroup is continuous in operator norm, not merely strongly continuous. -/
theorem continuous_yosidaSemigroup (A : X →ₗ.[ℝ] X) (hA : IsMDissipative A) (lambda : ℝ)
    (hlambda : 0 < lambda) :
    Continuous fun t : NNReal => yosidaSemigroup A hA lambda hlambda t := by
  refine (StronglyContinuousSemigroup.ofBounded_continuous
    (yosidaApproximation A lambda)).congr fun t => ?_
  exact (StronglyContinuousSemigroup.ofBounded_apply _ t).trans
    (yosidaSemigroup_apply A hA lambda hlambda t).symm

/-- The generator of the Yosida semigroup is the everywhere-defined Yosida approximation. -/
@[simp]
theorem generator_yosidaSemigroup (A : X →ₗ.[ℝ] X) (hA : IsMDissipative A) (lambda : ℝ)
    (hlambda : 0 < lambda) :
    (yosidaSemigroup A hA lambda hlambda).toStronglyContinuousSemigroup.generator =
      (yosidaApproximation A lambda : X →ₗ[ℝ] X).toPMap ⊤ :=
  StronglyContinuousSemigroup.ofBounded_generator _

end TauCeti.Semigroups

end
