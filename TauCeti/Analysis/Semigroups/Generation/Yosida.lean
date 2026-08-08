/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.BoundedGenerator.Basic
public import TauCeti.Analysis.Semigroups.Dissipative.Basic
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# Yosida approximations

This file constructs the bounded approximations used in the generation theorems for strongly
continuous semigroups. For an operator `A` whose resolvent at `lambda > 0` satisfies the
contraction bound, its Yosida approximation is

`A_lambda = lambda ^ 2 R(lambda, A) - lambda I = lambda A R(lambda, A)`.

The resolvent estimate makes `lambda R(lambda, A)` a contraction. Splitting the exponential of
`t A_lambda` into the commuting scalar and resolvent parts then proves that
`exp (t A_lambda)` is a contraction for every `t ≥ 0`. Thus each approximation generates a
uniformly continuous contraction semigroup. This is the bounded stage of the Yosida construction;
the later generation argument proves that these semigroups are Cauchy uniformly on compact time
intervals before defining their limit.

## Main results

* `TauCeti.Semigroups.yosidaApproximation`: the bounded operator `A_lambda`.
* `TauCeti.Semigroups.yosidaApproximation_apply_eq_smul_apply_resolvent`: the identity
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

The definition is meaningful when `lambda` belongs to the resolvent set of `A`; its algebraic API
carries that membership explicitly, while the norm estimates carry the resolvent bound they use. -/
def yosidaApproximation (A : X →ₗ.[ℝ] X) (lambda : ℝ) : X →L[ℝ] X :=
  lambda ^ 2 • LinearPMap.resolvent A lambda - lambda • 1

omit [CompleteSpace X] in
/-- Pointwise form of the definition of the Yosida approximation. -/
@[simp]
theorem yosidaApproximation_apply (A : X →ₗ.[ℝ] X) (lambda : ℝ) (x : X) :
    yosidaApproximation A lambda x =
      lambda ^ 2 • LinearPMap.resolvent A lambda x - lambda • x := by
  simp [yosidaApproximation]

omit [CompleteSpace X] in
/-- At a point of the resolvent set, the Yosida approximation is `lambda A R(lambda, A)`
pointwise. -/
theorem yosidaApproximation_apply_eq_smul_apply_resolvent {A : X →ₗ.[ℝ] X} {lambda : ℝ}
    (hlambda : lambda ∈ LinearPMap.resolventSet A) (x : X) :
    yosidaApproximation A lambda x = lambda • A ⟨LinearPMap.resolvent A lambda x,
      LinearPMap.resolvent_mem_domain hlambda x⟩ := by
  rw [yosidaApproximation_apply, LinearPMap.apply_resolvent hlambda]
  module

omit [CompleteSpace X] in
/-- The Yosida approximation has the elementary bound `‖A_lambda‖ ≤ 2 lambda`. -/
theorem norm_yosidaApproximation_le {A : X →ₗ.[ℝ] X} {lambda : ℝ}
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) :
    ‖yosidaApproximation A lambda‖ ≤ 2 * lambda := by
  have hscaled : ‖lambda • (lambda • LinearPMap.resolvent A lambda)‖ ≤ lambda := by
    calc
      ‖lambda • (lambda • LinearPMap.resolvent A lambda)‖
          = lambda * ‖lambda • LinearPMap.resolvent A lambda‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
      _ ≤ lambda * 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
        gcongr
      _ = lambda := mul_one _
  have hone : ‖lambda • (1 : X →L[ℝ] X)‖ ≤ lambda := by
    calc
      ‖lambda • (1 : X →L[ℝ] X)‖ = lambda * ‖(1 : X →L[ℝ] X)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlambda]
      _ ≤ lambda * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ = lambda := mul_one _
  calc
    ‖yosidaApproximation A lambda‖
        = ‖lambda • (lambda • LinearPMap.resolvent A lambda) - lambda • (1 : X →L[ℝ] X)‖ := by
      rw [yosidaApproximation, smul_smul, pow_two]
    _ ≤ ‖lambda • (lambda • LinearPMap.resolvent A lambda)‖ + ‖lambda • (1 : X →L[ℝ] X)‖ :=
      norm_sub_le _ _
    _ ≤ lambda + lambda := add_le_add hscaled hone
    _ = 2 * lambda := (two_mul lambda).symm

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
  let +nondep : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ _
  exact exp_add_of_commute (Commute.one_left _ |>.smul_left _ |>.smul_right _)

/-- The exponential of a positive-time multiple of a Yosida approximation is contractive. -/
theorem norm_exp_smul_yosidaApproximation_le_one {A : X →ₗ.[ℝ] X} {lambda t : ℝ}
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) (ht : 0 ≤ t) :
    ‖exp (t • yosidaApproximation A lambda)‖ ≤ 1 := by
  let +nondep : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ _
  calc
    ‖exp (t • yosidaApproximation A lambda)‖ =
        ‖exp ((-(t * lambda)) • (1 : X →L[ℝ] X)) *
          exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖ := by
      rw [exp_yosidaApproximation_eq]
    _ ≤ ‖exp ((-(t * lambda)) • (1 : X →L[ℝ] X))‖ *
          ‖exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖ := norm_mul_le _ _
    _ ≤ Real.exp (-(t * lambda)) *
          Real.exp ‖(t * lambda ^ 2) • LinearPMap.resolvent A lambda‖ := by
      gcongr
      · exact ContinuousLinearMap.norm_exp_smul_one_le _
      · exact TauCeti.norm_exp_le_exp_norm ContinuousLinearMap.norm_id_le _
    _ ≤ Real.exp (-(t * lambda)) * Real.exp (t * lambda) := by
      gcongr
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ t * lambda ^ 2)]
      calc
        t * lambda ^ 2 * ‖LinearPMap.resolvent A lambda‖
            = t * lambda * (lambda * ‖LinearPMap.resolvent A lambda‖) := by ring
        _ ≤ t * lambda * 1 := by gcongr
        _ = t * lambda := mul_one _
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The uniformly continuous contraction semigroup generated by the Yosida approximation. -/
def yosidaSemigroup (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1)
    (hlambda : 0 < lambda) : ContractionSemigroup X where
  toStronglyContinuousSemigroup := StronglyContinuousSemigroup.ofBounded
    (yosidaApproximation A lambda)
  contracting t := by
    -- The `contracting` field exposes the raw `toFun`; it is definitionally the same function
    -- as the semigroup coercion used by `ofBounded_apply`.
    calc
      ‖(StronglyContinuousSemigroup.ofBounded (yosidaApproximation A lambda)).toFun t‖ =
          ‖exp ((t : ℝ) • yosidaApproximation A lambda)‖ :=
        congrArg norm (StronglyContinuousSemigroup.ofBounded_apply _ t)
      _ ≤ 1 := norm_exp_smul_yosidaApproximation_le_one hres hlambda t.property

/-- The C₀-semigroup underlying the Yosida semigroup is the bounded-generator semigroup of the
Yosida approximation. -/
@[simp]
theorem yosidaSemigroup_toStronglyContinuousSemigroup (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) :
    (yosidaSemigroup A lambda hres hlambda).toStronglyContinuousSemigroup =
      StronglyContinuousSemigroup.ofBounded (yosidaApproximation A lambda) := by
  simp [yosidaSemigroup]

/-- The Yosida semigroup is the exponential of the Yosida approximation. -/
@[simp]
theorem yosidaSemigroup_apply (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) (t : NNReal) :
    yosidaSemigroup A lambda hres hlambda t = exp ((t : ℝ) • yosidaApproximation A lambda) := by
  rw [← ContractionSemigroup.toStronglyContinuousSemigroup_apply,
    yosidaSemigroup_toStronglyContinuousSemigroup, StronglyContinuousSemigroup.ofBounded_apply]

/-- The Yosida semigroup is continuous in operator norm, not merely strongly continuous. -/
theorem continuous_yosidaSemigroup (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) :
    Continuous fun t : NNReal => yosidaSemigroup A lambda hres hlambda t := by
  refine (StronglyContinuousSemigroup.ofBounded_continuous
    (yosidaApproximation A lambda)).congr fun t => ?_
  exact (StronglyContinuousSemigroup.ofBounded_apply _ t).trans
    (yosidaSemigroup_apply A lambda hres hlambda t).symm

/-- The generator of the Yosida semigroup is the everywhere-defined Yosida approximation. -/
theorem yosidaSemigroup_generator (A : X →ₗ.[ℝ] X) (lambda : ℝ)
    (hres : lambda * ‖LinearPMap.resolvent A lambda‖ ≤ 1) (hlambda : 0 < lambda) :
    (yosidaSemigroup A lambda hres hlambda).toStronglyContinuousSemigroup.generator =
      (yosidaApproximation A lambda : X →ₗ[ℝ] X).toPMap ⊤ := by
  rw [yosidaSemigroup_toStronglyContinuousSemigroup,
    StronglyContinuousSemigroup.ofBounded_generator]

end TauCeti.Semigroups

end
