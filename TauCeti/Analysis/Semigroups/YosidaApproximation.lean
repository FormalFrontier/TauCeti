/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Identity
public import TauCeti.Analysis.Semigroups.BoundedGenerator.Basic

/-!
# The Yosida approximation of a contraction semigroup generator

For a contraction semigroup `S` with generator `A` and a parameter `lambda > 0`, the **Yosida
approximation** is the bounded operator

`A_lambda = lambda ^ 2 • R(lambda) - lambda • I`,

built from the Laplace-transform resolvent `R(lambda)` of
`TauCeti/Analysis/Semigroups/Resolvent/Basic.lean`. It is the standard bounded stand-in for the
generally unbounded generator: it is defined on all of `X`, it agrees with `A` in the limit
`lambda → ∞`, and — the content of this file — it generates a *contraction* semigroup rather
than merely a uniformly continuous one.

Main results:

* `ContractionSemigroup.yosidaApprox` and its pointwise unfolding;
* `ContractionSemigroup.yosidaApprox_eq_smul_sub_one`, the factored form
  `A_lambda = lambda • (lambda • R(lambda) - I)`;
* `ContractionSemigroup.norm_yosidaApprox_le`, the bound `‖A_lambda‖ ≤ 2 * lambda`;
* `ContractionSemigroup.yosidaApprox_apply_of_mem_domain`, the identity
  `A_lambda x = lambda • R(lambda) (A x)` on the generator domain;
* `ContractionSemigroup.norm_exp_yosidaApprox_le_one`, the contraction estimate
  `‖exp (t • A_lambda)‖ ≤ 1` for `t ≥ 0`;
* `ContractionSemigroup.yosidaSemigroup`, packaging `exp (t • A_lambda)` as a
  `ContractionSemigroup`, together with the identification of its generator.

The contraction estimate is the reason the approximation is useful. Splitting
`t • A_lambda` into the commuting summands `(t * lambda ^ 2) • R(lambda)` and
`(-(t * lambda)) • I` turns the exponential into a product; the scalar factor contributes
`Real.exp (-(t * lambda))` exactly, while the resolvent factor is bounded by
`Real.exp (t * lambda ^ 2 * ‖R(lambda)‖) ≤ Real.exp (t * lambda)` using `‖R(lambda)‖ ≤ 1/lambda`.
The two cancel. Note that this uses only the first-power resolvent bound, not the iterated
bounds of `TauCeti/Analysis/Semigroups/Resolvent/PowerBounds.lean`.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Theorem II.3.5 (the
Yosida approximation in the proof of the Hille--Yosida generation theorem); Pazy, *Semigroups of
Linear Operators and Applications to Partial Differential Equations*, Theorem 1.3.1.
-/

public section

noncomputable section

open scoped NNReal
open NormedSpace

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace ContractionSemigroup

/-- The Yosida approximation `A_lambda = lambda ^ 2 • R(lambda) - lambda • I` of the generator
of a contraction semigroup. -/
def yosidaApprox (S : ContractionSemigroup X) (lambda : ℝ) (hlambda : 0 < lambda) :
    X →L[ℝ] X :=
  lambda ^ 2 • S.resolvent lambda hlambda - lambda • (1 : X →L[ℝ] X)

/-- The Yosida approximation, applied to a vector. -/
theorem yosidaApprox_apply (S : ContractionSemigroup X) (lambda : ℝ) (hlambda : 0 < lambda)
    (x : X) :
    S.yosidaApprox lambda hlambda x
      = lambda ^ 2 • S.resolvent lambda hlambda x - lambda • x := by
  rw [yosidaApprox]; rfl

/-- The Yosida approximation factors as `lambda • (lambda • R(lambda) - I)`. -/
theorem yosidaApprox_eq_smul_sub_one (S : ContractionSemigroup X) (lambda : ℝ)
    (hlambda : 0 < lambda) :
    S.yosidaApprox lambda hlambda
      = lambda • (lambda • S.resolvent lambda hlambda - (1 : X →L[ℝ] X)) := by
  rw [yosidaApprox, smul_sub, smul_smul, ← sq]

/-- The operator-norm bound `‖A_lambda‖ ≤ 2 * lambda`, from `‖R(lambda)‖ ≤ 1/lambda`. -/
theorem norm_yosidaApprox_le (S : ContractionSemigroup X) (lambda : ℝ) (hlambda : 0 < lambda) :
    ‖S.yosidaApprox lambda hlambda‖ ≤ 2 * lambda := by
  have hres : ‖lambda ^ 2 • S.resolvent lambda hlambda‖ ≤ lambda := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg lambda)]
    calc lambda ^ 2 * ‖S.resolvent lambda hlambda‖
        ≤ lambda ^ 2 * (1 / lambda) := by
          exact mul_le_mul_of_nonneg_left (S.resolvent_norm_le lambda hlambda) (sq_nonneg lambda)
      _ = lambda := by field_simp [hlambda.ne', sq]
  have hone : ‖lambda • (1 : X →L[ℝ] X)‖ ≤ lambda := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlambda.le]
    calc lambda * ‖(1 : X →L[ℝ] X)‖
        ≤ lambda * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hlambda.le
      _ = lambda := mul_one lambda
  calc ‖S.yosidaApprox lambda hlambda‖
      ≤ ‖lambda ^ 2 • S.resolvent lambda hlambda‖ + ‖lambda • (1 : X →L[ℝ] X)‖ :=
        norm_sub_le _ _
    _ ≤ lambda + lambda := add_le_add hres hone
    _ = 2 * lambda := (two_mul lambda).symm

/-- On the generator domain the Yosida approximation is `A_lambda x = lambda • R(lambda) (A x)`.
This is the form that makes `A_lambda x → A x` plausible: the scaled resolvent
`lambda • R(lambda)` converges strongly to the identity. -/
theorem yosidaApprox_apply_of_mem_domain (S : ContractionSemigroup X) (lambda : ℝ)
    (hlambda : 0 < lambda) (x : S.toStronglyContinuousSemigroup.domain) :
    S.yosidaApprox lambda hlambda (x : X)
      = lambda • S.resolvent lambda hlambda
          (S.toStronglyContinuousSemigroup.generator
            ⟨x, by rw [StronglyContinuousSemigroup.generator_domain]; exact x.property⟩) := by
  have hleft := S.resolventLeftInv lambda hlambda x
  have hsplit :
      S.resolvent lambda hlambda
          (lambda • (x : X) - S.toStronglyContinuousSemigroup.generator
            ⟨x, by rw [StronglyContinuousSemigroup.generator_domain]; exact x.property⟩)
        = lambda • S.resolvent lambda hlambda (x : X)
          - S.resolvent lambda hlambda
              (S.toStronglyContinuousSemigroup.generator
                ⟨x, by rw [StronglyContinuousSemigroup.generator_domain]; exact x.property⟩) := by
    rw [map_sub, map_smul]
  rw [hsplit] at hleft
  have hadd : lambda • S.resolvent lambda hlambda (x : X)
      = (x : X) + S.resolvent lambda hlambda
          (S.toStronglyContinuousSemigroup.generator
            ⟨x, by rw [StronglyContinuousSemigroup.generator_domain]; exact x.property⟩) :=
    sub_eq_iff_eq_add.mp hleft
  have hx : lambda • S.resolvent lambda hlambda (x : X) - (x : X)
      = S.resolvent lambda hlambda
          (S.toStronglyContinuousSemigroup.generator
            ⟨x, by rw [StronglyContinuousSemigroup.generator_domain]; exact x.property⟩) := by
    rw [hadd]
    abel
  rw [yosidaApprox_apply, ← hx, smul_sub, smul_smul, ← sq]

omit [CompleteSpace X] in
/-- The exponential of `c • I` is the scalar exponential, as a multiple of the identity. -/
private theorem exp_smul_one (c : ℝ) :
    exp (c • (1 : X →L[ℝ] X)) = Real.exp c • (1 : X →L[ℝ] X) := by
  rw [← Algebra.algebraMap_eq_smul_one, ← algebraMap_exp_comm,
    Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ]

/-- **The Yosida approximation generates a contraction semigroup.** For `t ≥ 0`,
`‖exp (t • A_lambda)‖ ≤ 1`.

The proof splits `t • A_lambda` into the commuting summands `(t * lambda ^ 2) • R(lambda)` and
`(-(t * lambda)) • I`; the second contributes the factor `Real.exp (-(t * lambda))`, which
cancels the bound `Real.exp (t * lambda)` on the first. -/
theorem norm_exp_yosidaApprox_le_one (S : ContractionSemigroup X) (lambda : ℝ)
    (hlambda : 0 < lambda) {t : ℝ} (ht : 0 ≤ t) :
    ‖exp (t • S.yosidaApprox lambda hlambda)‖ ≤ 1 := by
  set R := S.resolvent lambda hlambda with hR
  have hsplit : t • S.yosidaApprox lambda hlambda
      = (t * lambda ^ 2) • R + (-(t * lambda)) • (1 : X →L[ℝ] X) := by
    rw [yosidaApprox, smul_sub, smul_smul, smul_smul, neg_smul, sub_eq_add_neg]
  have hcomm : Commute ((t * lambda ^ 2) • R) ((-(t * lambda)) • (1 : X →L[ℝ] X)) :=
    (Commute.one_right _).smul_right _
  have hscalar : ‖exp ((-(t * lambda)) • (1 : X →L[ℝ] X))‖ ≤ Real.exp (-(t * lambda)) := by
    rw [exp_smul_one, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    calc Real.exp (-(t * lambda)) * ‖(1 : X →L[ℝ] X)‖
        ≤ Real.exp (-(t * lambda)) * 1 :=
          mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (Real.exp_nonneg _)
      _ = Real.exp (-(t * lambda)) := mul_one _
  have hres : ‖exp ((t * lambda ^ 2) • R)‖ ≤ Real.exp (t * lambda) := by
    refine (StronglyContinuousSemigroup.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg ht (sq_nonneg lambda))]
    calc t * lambda ^ 2 * ‖R‖
        ≤ t * lambda ^ 2 * (1 / lambda) :=
          mul_le_mul_of_nonneg_left (hR ▸ S.resolvent_norm_le lambda hlambda)
            (mul_nonneg ht (sq_nonneg lambda))
      _ = t * lambda := by field_simp [hlambda.ne', sq]
  calc ‖exp (t • S.yosidaApprox lambda hlambda)‖
      = ‖exp ((t * lambda ^ 2) • R) * exp ((-(t * lambda)) • (1 : X →L[ℝ] X))‖ := by
        rw [hsplit, StronglyContinuousSemigroup.exp_add_of_commute hcomm]
    _ ≤ ‖exp ((t * lambda ^ 2) • R)‖ * ‖exp ((-(t * lambda)) • (1 : X →L[ℝ] X))‖ :=
        norm_mul_le _ _
    _ ≤ Real.exp (t * lambda) * Real.exp (-(t * lambda)) :=
        mul_le_mul hres hscalar (norm_nonneg _) (Real.exp_nonneg _)
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

/-- The contraction semigroup `t ↦ exp (t • A_lambda)` generated by the Yosida approximation.

Unlike `ofBounded`, which only gives the growth bound `(‖A‖, 1)`, this is a genuine
`ContractionSemigroup`: the cancellation in `norm_exp_yosidaApprox_le_one` promotes the growth
bound to `(0, 1)`. -/
def yosidaSemigroup (S : ContractionSemigroup X) (lambda : ℝ) (hlambda : 0 < lambda) :
    ContractionSemigroup X where
  toStronglyContinuousSemigroup :=
    StronglyContinuousSemigroup.ofBounded (S.yosidaApprox lambda hlambda)
  contracting t := by
    have h : (StronglyContinuousSemigroup.ofBounded (S.yosidaApprox lambda hlambda)) t
        = exp ((t : ℝ) • S.yosidaApprox lambda hlambda) :=
      StronglyContinuousSemigroup.ofBounded_apply _ t
    rw [show ((StronglyContinuousSemigroup.ofBounded (S.yosidaApprox lambda hlambda)).toFun t)
        = (StronglyContinuousSemigroup.ofBounded (S.yosidaApprox lambda hlambda)) t from rfl, h]
    exact S.norm_exp_yosidaApprox_le_one lambda hlambda t.coe_nonneg

/-- The underlying C₀-semigroup of `yosidaSemigroup` is `ofBounded A_lambda`. -/
theorem yosidaSemigroup_toStronglyContinuousSemigroup (S : ContractionSemigroup X) (lambda : ℝ)
    (hlambda : 0 < lambda) :
    (S.yosidaSemigroup lambda hlambda).toStronglyContinuousSemigroup
      = StronglyContinuousSemigroup.ofBounded (S.yosidaApprox lambda hlambda) := by
  rw [yosidaSemigroup]

/-- `yosidaSemigroup` is the operator exponential of the Yosida approximation. -/
theorem yosidaSemigroup_apply (S : ContractionSemigroup X) (lambda : ℝ) (hlambda : 0 < lambda)
    (t : ℝ≥0) :
    (S.yosidaSemigroup lambda hlambda) t = exp ((t : ℝ) • S.yosidaApprox lambda hlambda) :=
  StronglyContinuousSemigroup.ofBounded_apply _ t

/-- The generator of `yosidaSemigroup` is the Yosida approximation itself, defined everywhere. -/
theorem yosidaSemigroup_generator (S : ContractionSemigroup X) (lambda : ℝ)
    (hlambda : 0 < lambda) :
    (S.yosidaSemigroup lambda hlambda).toStronglyContinuousSemigroup.generator
      = ((S.yosidaApprox lambda hlambda : X →ₗ[ℝ] X).toPMap ⊤) :=
  StronglyContinuousSemigroup.ofBounded_generator _

/-- The generator domain of `yosidaSemigroup` is everything: the approximation is bounded. -/
theorem yosidaSemigroup_domain_eq_top (S : ContractionSemigroup X) (lambda : ℝ)
    (hlambda : 0 < lambda) :
    (S.yosidaSemigroup lambda hlambda).toStronglyContinuousSemigroup.domain = ⊤ :=
  StronglyContinuousSemigroup.ofBounded_domain_eq_top _

end ContractionSemigroup

end TauCeti.Semigroups

end

end
