/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Perturbation
public import TauCeti.Analysis.Semigroups.Resolvent.PowerBounds

/-!
# The resolvent of a bounded perturbation of a generator

For a semigroup `S` of growth `(omega, M)` and a bounded operator `B`, the sharp Hille--Yosida
bound `‖R(lambda, S.generator)‖ ≤ M / (lambda - omega)` makes the perturbation
`B +ᵥ S.generator` small against the resolvent as soon as `lambda > omega + M ‖B‖`. The Neumann
perturbation of a resolvent point (`TauCeti.LinearPMap.mem_resolventSet_vadd`) then puts every
such `lambda` in the resolvent set of the perturbed generator, with
`‖R(lambda, B + S.generator)‖ ≤ M / (lambda - omega - M ‖B‖)`.

Only the first power of the perturbed resolvent is controlled this way: iterating the Neumann
bound costs `M ^ n` rather than `M`, so it does not feed Hille--Yosida at `M > 1`. The general
generation theorem instead passes to an equivalent norm, reducing the operator argument to the
`M = 1` case; see `TauCeti/Analysis/Semigroups/Generation/BoundedPerturbation.lean`.

## Main results

* `TauCeti.Semigroups.StronglyContinuousSemigroup.mem_resolventSet_generator_vadd`: the resolvent
  set of the perturbed generator contains `(omega + M ‖B‖, ∞)`.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.norm_resolvent_generator_vadd_le`: the norm
  bound for the perturbed generator resolvent.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section III.1;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 3, Theorem 1.1.
-/

public section

namespace TauCeti.Semigroups.StronglyContinuousSemigroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  {omega M lambda : ℝ}

/-- **The resolvent set of a bounded perturbation of a generator.** For a semigroup of growth
`(omega, M)` and a bounded `B`, every `lambda > omega + M ‖B‖` lies in the resolvent set of
`B +ᵥ S.generator`. -/
theorem mem_resolventSet_generator_vadd (S : StronglyContinuousSemigroup X)
    (hb : S.HasGrowthBound omega M) (B : X →L[ℝ] X) (hlambda : omega + M * ‖B‖ < lambda) :
    lambda ∈ LinearPMap.resolventSet ((B : X →ₗ[ℝ] X) +ᵥ S.generator) := by
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hb.one_le
  have hMB : 0 ≤ M * ‖B‖ := mul_nonneg hM.le (norm_nonneg B)
  have homega : omega < lambda := by linarith
  refine LinearPMap.mem_resolventSet_vadd B (S.Ioi_subset_resolventSet_generator hb homega)
    (r := M / (lambda - omega)) (by simpa using S.norm_generator_resolvent_pow_le hb homega 1) ?_
  rw [mul_div_assoc', div_lt_one (by linarith)]
  nlinarith

/-- **The resolvent bound for a bounded perturbation of a generator.** For a semigroup of growth
`(omega, M)` and a bounded `B`, the resolvent of `B +ᵥ S.generator` obeys
`‖R(lambda, B + S.generator)‖ ≤ M / (lambda - omega - M ‖B‖)` for `lambda > omega + M ‖B‖`. -/
theorem norm_resolvent_generator_vadd_le (S : StronglyContinuousSemigroup X)
    (hb : S.HasGrowthBound omega M) (B : X →L[ℝ] X) (hlambda : omega + M * ‖B‖ < lambda) :
    ‖LinearPMap.resolvent ((B : X →ₗ[ℝ] X) +ᵥ S.generator) lambda‖
      ≤ M / (lambda - omega - M * ‖B‖) := by
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one hb.one_le
  have hMB : 0 ≤ M * ‖B‖ := mul_nonneg hM.le (norm_nonneg B)
  have homega : omega < lambda := by linarith
  have hpos : 0 < lambda - omega := by linarith
  have hsmall : ‖B‖ * (M / (lambda - omega)) < 1 := by
    rw [mul_div_assoc', div_lt_one hpos]
    nlinarith
  refine (LinearPMap.norm_resolvent_vadd_le B (S.Ioi_subset_resolventSet_generator hb homega)
    (r := M / (lambda - omega)) (by simpa using S.norm_generator_resolvent_pow_le hb homega 1)
    hsmall).trans_eq ?_
  have hne : lambda - omega ≠ 0 := ne_of_gt hpos
  have hden : (1 : ℝ) - ‖B‖ * (M / (lambda - omega)) ≠ 0 := ne_of_gt (by linarith)
  have hd : lambda - omega - M * ‖B‖ ≠ 0 := ne_of_gt (by linarith)
  field_simp

end TauCeti.Semigroups.StronglyContinuousSemigroup

end
