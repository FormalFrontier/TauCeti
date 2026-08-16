/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Semigroups.Generation.HilleYosida.Limit
public import TauCeti.Analysis.Semigroups.Generation.HilleYosida.Shift
public import TauCeti.Analysis.Semigroups.Generation.Yosida.Generator
public import TauCeti.Analysis.Semigroups.Generator.ExponentialShift
public import TauCeti.Analysis.Semigroups.Resolvent.Identity

/-!
# The Hille--Yosida generation theorem

This file completes the Yosida construction for a densely defined operator `A` on a real Banach
space. At growth exponent zero, the resolvent-power estimates

`‖R(lambda, A) ^ n‖ ≤ M / lambda ^ n`

produce the semigroup `hilleYosidaLimitSemigroup`. The compact-time convergence of its bounded
approximations and the shared positive resolvent half-line identify the generator of that
semigroup with `A`.

For a general growth exponent `omega`, apply the zero-exponent construction to
`A - omega I`, then exponentially shift the resulting semigroup back. The scalar-shift identities
for partial linear maps and semigroup generators show that the final generator is exactly `A`,
while the growth bound becomes `(omega, M)`.

This proves the Hille--Yosida milestone in Part A of the
[one-parameter-semigroups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/OneParameterSemigroups/README.md#part-a--strongly-continuous-semigroups).

## Main results

* `TauCeti.Semigroups.hilleYosidaLimitSemigroup_generator`: the exponent-zero limit semigroup has
  generator `A`.
* `TauCeti.Semigroups.hilleYosida_generation`: the general `(M, omega)` Hille--Yosida generation
  theorem.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Theorem II.3.8.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 1, Theorem 5.3.
-/

public section

noncomputable section

open Filter NormedSpace
open scoped NNReal Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-! ## Generator identification at exponent zero -/

/-- **The exponent-zero Hille--Yosida limit semigroup has generator `A`.**

The first resolvent-power estimate makes the Yosida approximations converge to `A` on its dense
domain. All power estimates together bound their exponentials by `M`, and the compact-time limit
theorems identify those exponentials with the orbits of `hilleYosidaLimitSemigroup`. Finally,
`1` is a resolvent point of both `A` and the limit generator, so the inclusion obtained from the
integrated Cauchy equation is an equality. -/
@[simp]
theorem hilleYosidaLimitSemigroup_generator {A : X →ₗ.[ℝ] X} {M : ℝ}
    (hM : 1 ≤ M)
    (hres : ∀ lambda : ℝ, 0 < lambda → lambda ∈ LinearPMap.resolventSet A)
    (hpow : ∀ n : ℕ, 1 ≤ n → ∀ lambda : ℝ, 0 < lambda →
      ‖LinearPMap.resolvent A lambda ^ n‖ ≤ M / lambda ^ n)
    (hdense : Dense (A.domain : Set X)) :
    (hilleYosidaLimitSemigroup hM hres hpow hdense).generator = A := by
  let S := hilleYosidaLimitSemigroup hM hres hpow hdense
  have hbound : ∀ lambda : ℝ, 0 < lambda →
      ‖LinearPMap.resolvent A lambda‖ ≤ M / lambda := by
    intro lambda hlambda
    simpa using hpow 1 le_rfl lambda hlambda
  apply S.generator_eq_of_yosidaApproximation (lambda := 1)
    (hres 1 one_pos)
    (S.mem_resolventSet_generator
      (hasGrowthBound_hilleYosidaLimitSemigroup hM hres hpow hdense) one_pos)
  · exact tendsto_yosidaApproximation_apply_atTop hres hbound hdense
  · intro x t ht
    simpa only [S, hilleYosidaLimitSemigroup_realOperator_apply_of_nonneg hM hres hpow hdense
      ht (x : X)] using
      tendsto_yosidaLimit_of_norm_resolvent_pow_le hM hres hpow hdense ht (x : X)
  · intro x T hT
    refine (tendstoUniformlyOn_exp_yosidaApproximation_of_norm_resolvent_pow_le
      hM hres hpow hdense (A x) hT).congr_right fun u hu => ?_
    exact (hilleYosidaLimitSemigroup_realOperator_apply_of_nonneg hM hres hpow hdense
      hu.1 (A x)).symm
  · intro T _hT
    refine ⟨M, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with lambda hlambda u hu
    exact norm_exp_smul_yosidaApproximation_le hM hlambda hu.1
      fun n hn => hpow n hn lambda hlambda

/-! ## The general generation theorem -/

/-- **Hille--Yosida generation theorem.** Let `A` be a densely defined operator on a real Banach
space, let `1 ≤ M`, and suppose that every real `lambda > omega` belongs to the resolvent set of
`A`, with the power estimates

`‖R(lambda, A) ^ n‖ ≤ M / (lambda - omega) ^ n` for every `n ≥ 1`.

Then `A` generates a strongly continuous semigroup with growth bound `(omega, M)`. The produced
semigroup is the exponential unshift of the exponent-zero Yosida limit for `A - omega I`. -/
theorem hilleYosida_generation {A : X →ₗ.[ℝ] X} {M omega : ℝ}
    (hM : 1 ≤ M) (hdense : Dense (A.domain : Set X))
    (hres : ∀ lambda : ℝ, omega < lambda → lambda ∈ LinearPMap.resolventSet A)
    (hpow : ∀ n : ℕ, 1 ≤ n → ∀ lambda : ℝ, omega < lambda →
      ‖LinearPMap.resolvent A lambda ^ n‖ ≤ M / (lambda - omega) ^ n) :
    ∃ S : StronglyContinuousSemigroup X, S.generator = A ∧ S.HasGrowthBound omega M := by
  obtain ⟨hres₀, hpow₀⟩ := LinearPMap.hilleYosida_zero_of hres hpow
  have hdense₀ : Dense ((LinearPMap.subScalar A omega).domain : Set X) := by
    simpa using hdense
  let T := hilleYosidaLimitSemigroup hM hres₀ hpow₀ hdense₀
  refine ⟨T.expShift (-omega), ?_, ?_⟩
  · rw [StronglyContinuousSemigroup.generator_expShift]
    dsimp only [T]
    rw [hilleYosidaLimitSemigroup_generator hM hres₀ hpow₀ hdense₀,
      LinearPMap.subScalar_subScalar, add_neg_cancel, LinearPMap.subScalar_zero]
  · have hT : T.HasGrowthBound 0 M := by
      exact hasGrowthBound_hilleYosidaLimitSemigroup hM hres₀ hpow₀ hdense₀
    simpa using hT.expShift (lambda := -omega)

end TauCeti.Semigroups

end
