/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generation.Yosida.Basic
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# Bounded approximations for the Hille--Yosida theorem

This file establishes the bounded stage of the exponent-zero, general-`M` Hille--Yosida
construction. Suppose that the powers of an unbounded operator's resolvent at `lambda > 0` satisfy

`‖R(lambda, A) ^ n‖ ≤ M / lambda ^ n` for every `n ≥ 1`, with `1 ≤ M`.

Then every power of the scaled resolvent `lambda R(lambda, A)` has norm at most `M`. Expanding the
resolvent factor in

`exp (t A_lambda) = exp (-t lambda I) exp (t lambda² R(lambda, A))`

as a power series gives the uniform estimate `‖exp (t A_lambda)‖ ≤ M` for `t ≥ 0`. Consequently,
the bounded-generator semigroup associated to every Yosida approximation has growth bound `(0,M)`.
Unlike the contraction estimate in
`TauCeti.Analysis.Semigroups.Generation.Yosida.Basic`, this argument uses the bounds on *all*
resolvent powers; that distinction is exactly why the exponent-zero
Hille--Yosida hypothesis for general `M` is stronger than a bound on the resolvent alone.

For the general Hille--Yosida generation theorem, these estimates must be combined with reduction
from `(M, omega)` to exponent zero by shifting the operator, compact-time Cauchy convergence of the
approximating semigroups, construction of their strong limit, and identification of its generator.

## Main results

* `TauCeti.Semigroups.norm_smul_resolvent_pow_le`: the scaled resolvent powers are bounded by `M`.
* `TauCeti.Semigroups.norm_exp_smul_yosidaApproximation_le`: every positive-time Yosida
  exponential has norm at most `M`.
* `TauCeti.Semigroups.ofBounded_yosidaApproximation_hasGrowthBound`: the corresponding bounded
  semigroup has growth bound `(0,M)`.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Theorem II.3.5;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 1.
-/

public section

noncomputable section

namespace TauCeti.Semigroups

open NormedSpace

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- The exponent-zero Hille--Yosida bounds on the powers of `R(lambda, A)` imply the uniform bound
`‖(lambda R(lambda, A)) ^ n‖ ≤ M`, including at `n = 0` when `1 ≤ M`. -/
theorem norm_smul_resolvent_pow_le {A : X →ₗ.[ℝ] X} {lambda M : ℝ} (hM : 1 ≤ M)
    (hlambda : 0 < lambda)
    (hpow : ∀ n : ℕ, 1 ≤ n →
      ‖LinearPMap.resolvent A lambda ^ n‖ ≤ M / lambda ^ n) (n : ℕ) :
    ‖(lambda • LinearPMap.resolvent A lambda) ^ n‖ ≤ M := by
  cases n with
  | zero =>
      calc
        ‖(lambda • LinearPMap.resolvent A lambda) ^ 0‖ = ‖(1 : X →L[ℝ] X)‖ := by rw [pow_zero]
        _ ≤ 1 := ContinuousLinearMap.norm_id_le
        _ ≤ M := hM
  | succ n =>
      rw [smul_pow, norm_smul, Real.norm_eq_abs, abs_pow, abs_of_pos hlambda]
      calc
        lambda ^ (n + 1) * ‖LinearPMap.resolvent A lambda ^ (n + 1)‖
            ≤ lambda ^ (n + 1) * (M / lambda ^ (n + 1)) := by
              gcongr
              exact hpow (n + 1) (Nat.succ_pos n)
        _ = M := by
          field_simp

private theorem norm_exp_smul_smul_resolvent_le {A : X →ₗ.[ℝ] X} {lambda M t : ℝ}
    (hM : 1 ≤ M) (hlambda : 0 < lambda) (ht : 0 ≤ t)
    (hpow : ∀ n : ℕ, 1 ≤ n →
      ‖LinearPMap.resolvent A lambda ^ n‖ ≤ M / lambda ^ n) :
    ‖exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖ ≤
      M * Real.exp (t * lambda) := by
  let B : X →L[ℝ] X := lambda • LinearPMap.resolvent A lambda
  have hs : 0 ≤ t * lambda := mul_nonneg ht hlambda.le
  have hB (n : ℕ) : ‖B ^ n‖ ≤ M := by
    exact norm_smul_resolvent_pow_le hM hlambda hpow n
  have harg : (t * lambda) • B =
      (t * lambda ^ 2) • LinearPMap.resolvent A lambda := by
    dsimp only [B]
    rw [smul_smul]
    congr 1
    ring
  rw [← harg]
  exact ContinuousLinearMap.norm_exp_smul_le_mul_exp_of_norm_pow_le hs hB

/-- Under the exponent-zero Hille--Yosida power bounds for general `M`, every positive-time
Yosida approximation has norm at most `M`. -/
theorem norm_exp_smul_yosidaApproximation_le {A : X →ₗ.[ℝ] X} {lambda M t : ℝ}
    (hM : 1 ≤ M) (hlambda : 0 < lambda) (ht : 0 ≤ t)
    (hpow : ∀ n : ℕ, 1 ≤ n →
      ‖LinearPMap.resolvent A lambda ^ n‖ ≤ M / lambda ^ n) :
    ‖exp (t • yosidaApproximation A lambda)‖ ≤ M := by
  calc
    ‖exp (t • yosidaApproximation A lambda)‖ =
        ‖exp ((-(t * lambda)) • (1 : X →L[ℝ] X)) *
          exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖ := by
      rw [exp_yosidaApproximation]
    _ ≤ ‖exp ((-(t * lambda)) • (1 : X →L[ℝ] X))‖ *
          ‖exp ((t * lambda ^ 2) • LinearPMap.resolvent A lambda)‖ := norm_mul_le _ _
    _ ≤ Real.exp (-(t * lambda)) * (M * Real.exp (t * lambda)) := by
      gcongr
      · exact ContinuousLinearMap.norm_exp_smul_one_le _
      · exact norm_exp_smul_smul_resolvent_le hM hlambda ht hpow
    _ = M * (Real.exp (-(t * lambda)) * Real.exp (t * lambda)) := by ring
    _ = M := by rw [← Real.exp_add]; simp

/-- The bounded-generator semigroup associated to an exponent-zero Hille--Yosida approximation
has the uniform growth bound `(0, M)`. -/
theorem ofBounded_yosidaApproximation_hasGrowthBound {A : X →ₗ.[ℝ] X} {lambda M : ℝ}
    (hM : 1 ≤ M) (hlambda : 0 < lambda)
    (hpow : ∀ n : ℕ, 1 ≤ n →
      ‖LinearPMap.resolvent A lambda ^ n‖ ≤ M / lambda ^ n) :
    (StronglyContinuousSemigroup.ofBounded (yosidaApproximation A lambda)).HasGrowthBound 0 M := by
  refine StronglyContinuousSemigroup.hasGrowthBound_of_bound hM fun t ht => ?_
  rw [zero_mul, Real.exp_zero, mul_one,
    StronglyContinuousSemigroup.ofBounded_realOperator_of_nonneg _ ht]
  exact norm_exp_smul_yosidaApproximation_le hM hlambda ht hpow

end TauCeti.Semigroups

end
