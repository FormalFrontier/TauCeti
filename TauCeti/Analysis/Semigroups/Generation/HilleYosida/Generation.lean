/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generation.HilleYosida.Limit
public import TauCeti.Analysis.Semigroups.Generation.HilleYosida.Shift
public import TauCeti.Analysis.Semigroups.Generation.Yosida.Generator
public import TauCeti.Analysis.Semigroups.Generator.ExponentialShift
public import TauCeti.Analysis.Semigroups.Resolvent.PowerBounds

/-!
# The Hille--Yosida generation theorem

This file completes the Yosida construction for a densely defined operator `A` on a real Banach
space. At growth exponent zero, the resolvent-power estimates

`‖R(lambda, A) ^ n‖ ≤ M / lambda ^ n`

produce the semigroup `hilleYosidaLimitSemigroup`. The compact-time convergence of its bounded
approximations and the shared positive resolvent half-line identify the generator of that
semigroup with `A`.

For a general growth exponent `omega`, `hilleYosidaSemigroup` applies the zero-exponent
construction to `A - omega I`, then exponentially shifts the resulting semigroup back. The
scalar-shift identities for partial linear maps and semigroup generators show that its generator
is exactly `A`, while its growth bound becomes `(omega, M)`. The final characterization combines
this construction with density and the sharp generator-resolvent estimates for every C₀-semigroup.

This proves the Hille--Yosida milestone in Part A of the
[one-parameter-semigroups roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/OneParameterSemigroups/README.md#part-a--strongly-continuous-semigroups).

## Main results

* `TauCeti.Semigroups.hilleYosidaLimitSemigroup_generator`: the exponent-zero limit semigroup has
  generator `A`.
* `TauCeti.Semigroups.hilleYosidaSemigroup`: the general `(M, omega)` constructed semigroup.
* `TauCeti.Semigroups.hilleYosidaSemigroup_apply`: evaluation of the constructed semigroup.
* `TauCeti.Semigroups.hilleYosidaSemigroup_realOperator_apply_of_nonneg`: real-time evaluation at
  nonnegative times.
* `TauCeti.Semigroups.tendsto_hilleYosidaSemigroup`: convergence of the shifted Yosida
  approximating orbits.
* `TauCeti.Semigroups.hilleYosidaSemigroup_generator`: identification of its generator.
* `TauCeti.Semigroups.hasGrowthBound_hilleYosidaSemigroup`: its prescribed growth bound.
* `TauCeti.Semigroups.hilleYosida_generation`: the general `(M, omega)` Hille--Yosida generation
  theorem.
* `TauCeti.Semigroups.hilleYosida_generation_iff`: the Hille--Yosida characterization.

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

section

variable {A : X →ₗ.[ℝ] X} {M omega : ℝ}
variable (hM : 1 ≤ M)
variable (hres : ∀ lambda : ℝ, omega < lambda → lambda ∈ LinearPMap.resolventSet A)
variable (hpow : ∀ n : ℕ, 1 ≤ n → ∀ lambda : ℝ, omega < lambda →
  ‖LinearPMap.resolvent A lambda ^ n‖ ≤ M / (lambda - omega) ^ n)
variable (hdense : Dense (A.domain : Set X))

include hM hres hpow hdense

omit [CompleteSpace X] hM hres hpow in
private theorem dense_subScalar_domain :
    Dense ((LinearPMap.subScalar A omega).domain : Set X) := by
  simpa using hdense

/-- The strongly continuous semigroup constructed by the general `(M, omega)` Hille--Yosida
theorem. It is the exponential unshift of the exponent-zero limit semigroup for
`A - omega I`. -/
def hilleYosidaSemigroup : StronglyContinuousSemigroup X :=
  (hilleYosidaLimitSemigroup hM
    (LinearPMap.hilleYosida_zero_of hres hpow).1
    (LinearPMap.hilleYosida_zero_of hres hpow).2
    (dense_subScalar_domain hdense)).expShift (-omega)

private theorem hilleYosidaSemigroup_eq :
    hilleYosidaSemigroup hM hres hpow hdense =
      (hilleYosidaLimitSemigroup hM
        (LinearPMap.hilleYosida_zero_of hres hpow).1
        (LinearPMap.hilleYosida_zero_of hres hpow).2
        (dense_subScalar_domain hdense)).expShift (-omega) := rfl

/-- Evaluating the general Hille--Yosida semigroup gives the exponentially shifted
exponent-zero Yosida limit. -/
@[simp]
theorem hilleYosidaSemigroup_apply (t : ℝ≥0) (x : X) :
    hilleYosidaSemigroup hM hres hpow hdense t x =
      Real.exp (omega * (t : ℝ)) • yosidaLimit (LinearPMap.subScalar A omega) t x := by
  simp only [hilleYosidaSemigroup_eq, StronglyContinuousSemigroup.expShift_apply_apply,
    hilleYosidaLimitSemigroup_apply, neg_mul, neg_neg]

/-- Real-time evaluation of the general Hille--Yosida semigroup at a nonnegative time. -/
@[simp]
theorem hilleYosidaSemigroup_realOperator_apply_of_nonneg {t : ℝ} (ht : 0 ≤ t) (x : X) :
    (hilleYosidaSemigroup hM hres hpow hdense).realOperator t x =
      Real.exp (omega * t) • yosidaLimit (LinearPMap.subScalar A omega) t x := by
  simp only [hilleYosidaSemigroup_eq,
    StronglyContinuousSemigroup.expShift_realOperator_apply_of_nonneg _ _ _ ht,
    hilleYosidaLimitSemigroup_realOperator_apply_of_nonneg _ _ _ _ ht, neg_mul, neg_neg]

/-- The shifted Yosida approximations converge pointwise to the general Hille--Yosida semigroup. -/
theorem tendsto_hilleYosidaSemigroup (t : ℝ≥0) (x : X) :
    Tendsto (fun lambda : ℝ => Real.exp (omega * (t : ℝ)) •
        exp ((t : ℝ) • yosidaApproximation (LinearPMap.subScalar A omega) lambda) x)
      atTop (𝓝 (hilleYosidaSemigroup hM hres hpow hdense t x)) := by
  rw [hilleYosidaSemigroup_apply]
  exact (tendsto_yosidaLimit_of_norm_resolvent_pow_le hM
    (LinearPMap.hilleYosida_zero_of hres hpow).1
    (LinearPMap.hilleYosida_zero_of hres hpow).2
    (dense_subScalar_domain hdense) t.2 x).const_smul
      (Real.exp (omega * (t : ℝ)) : ℝ)

/-- The general Hille--Yosida semigroup has generator `A`. -/
@[simp]
theorem hilleYosidaSemigroup_generator :
    (hilleYosidaSemigroup hM hres hpow hdense).generator = A := by
  rw [hilleYosidaSemigroup_eq, StronglyContinuousSemigroup.generator_expShift,
    hilleYosidaLimitSemigroup_generator hM
      (LinearPMap.hilleYosida_zero_of hres hpow).1
      (LinearPMap.hilleYosida_zero_of hres hpow).2
      (dense_subScalar_domain hdense),
    LinearPMap.subScalar_subScalar, add_neg_cancel, LinearPMap.subScalar_zero]

/-- The general Hille--Yosida semigroup has the prescribed growth bound `(omega, M)`. -/
theorem hasGrowthBound_hilleYosidaSemigroup :
    (hilleYosidaSemigroup hM hres hpow hdense).HasGrowthBound omega M := by
  rw [hilleYosidaSemigroup_eq]
  have hzero := hasGrowthBound_hilleYosidaLimitSemigroup hM
    (LinearPMap.hilleYosida_zero_of hres hpow).1
    (LinearPMap.hilleYosida_zero_of hres hpow).2
    (dense_subScalar_domain hdense)
  simpa only [zero_sub, neg_neg] using hzero.expShift (lambda := -omega)

/-- **Hille--Yosida generation theorem.** Let `A` be a densely defined operator on a real Banach
space, let `1 ≤ M`, and suppose that every real `lambda > omega` belongs to the resolvent set of
`A`, with the power estimates

`‖R(lambda, A) ^ n‖ ≤ M / (lambda - omega) ^ n` for every `n ≥ 1`.

Then `A` generates a strongly continuous semigroup with growth bound `(omega, M)`. The produced
semigroup is the exponential unshift of the exponent-zero Yosida limit for `A - omega I`. -/
theorem hilleYosida_generation :
    ∃ S : StronglyContinuousSemigroup X, S.generator = A ∧ S.HasGrowthBound omega M :=
  ⟨hilleYosidaSemigroup hM hres hpow hdense,
    hilleYosidaSemigroup_generator hM hres hpow hdense,
    hasGrowthBound_hilleYosidaSemigroup hM hres hpow hdense⟩

end

/-- **Hille--Yosida characterization.** An unbounded operator is the generator of a strongly
continuous semigroup with growth bound `(omega, M)` if and only if `1 ≤ M`, its domain is dense,
the half-line `(omega, ∞)` lies in its resolvent set, and its resolvent powers satisfy the sharp
Hille--Yosida estimates. -/
theorem hilleYosida_generation_iff (A : X →ₗ.[ℝ] X) (M omega : ℝ) :
    (∃ S : StronglyContinuousSemigroup X, S.generator = A ∧ S.HasGrowthBound omega M) ↔
      1 ≤ M ∧ Dense (A.domain : Set X) ∧
        (∀ lambda : ℝ, omega < lambda → lambda ∈ LinearPMap.resolventSet A) ∧
        ∀ n : ℕ, 1 ≤ n → ∀ lambda : ℝ, omega < lambda →
          ‖LinearPMap.resolvent A lambda ^ n‖ ≤ M / (lambda - omega) ^ n := by
  constructor
  · rintro ⟨S, rfl, hb⟩
    refine ⟨hb.one_le, (by simpa only [S.generator_domain] using S.dense_domain),
      (fun _ hlambda => S.Ioi_subset_resolventSet_generator hb hlambda), ?_⟩
    · intro n _hn lambda hlambda
      exact S.norm_generator_resolvent_pow_le hb hlambda n
  · rintro ⟨hM, hdense, hres, hpow⟩
    exact hilleYosida_generation hM hres hpow hdense

end TauCeti.Semigroups

end
