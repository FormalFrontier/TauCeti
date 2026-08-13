/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Generation.LimitSemigroup
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# The Lumer--Phillips generation theorem

A densely defined m-dissipative operator `A` on a real Banach space generates a strongly
continuous contraction semigroup. The semigroup itself was built in
`TauCeti/Analysis/Semigroups/Generation/LimitSemigroup.lean` as the limit
`S(t) x = lim_{lambda -> ∞} exp (t A_lambda) x` of the Yosida exponentials; this file identifies
its generator with `A`, which is what makes the construction a *generation* theorem.

The identification runs through the integrated form of the Cauchy problem. Each bounded
approximation satisfies the exact Duhamel identity

`exp (t A_lambda) x - x = ∫₀ᵗ exp (u A_lambda) (A_lambda x) du`

(`TauCeti.ContinuousLinearMap.exp_smul_apply_sub_eq_intervalIntegral`), and for `x ∈ D(A)` both
sides converge: the left-hand side by the defining convergence of the limit, the right-hand
side because `A_lambda x -> A x` and because `exp (u A_lambda) -> S(u)` uniformly on `[0, t]`.
That gives `S(t) x - x = ∫₀ᵗ S(u) (A x) du`, whose difference quotient at
`t = 0` is the orbit average of `A x`, hence tends to `A x`. So `A` is a restriction of the
generator; since `1` lies in the resolvent set of both — `A` is m-dissipative by hypothesis, and
the generator of a contraction semigroup is m-dissipative — the restriction is an equality
(`TauCeti.LinearPMap.eq_of_le_of_mem_resolventSet`).

## Main results

* `TauCeti.Semigroups.IsMDissipative.yosidaLimitSemigroup_generator`: the generator of the
  Yosida limit semigroup of a densely defined m-dissipative `A` is `A`.
* `TauCeti.Semigroups.IsMDissipative.exists_contractionSemigroup_generator_eq`: the
  **Lumer--Phillips generation theorem**.
* `TauCeti.Semigroups.exists_contractionSemigroup_generator_eq_iff`: combined with the converse
  already available, an operator generates a contraction semigroup exactly when it is densely
  defined and m-dissipative.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Theorem II.3.15;
Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
Chapter 1, Theorem 4.3.
-/

public section

noncomputable section

open scoped NNReal Topology

open Filter NormedSpace

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace IsMDissipative

variable {A : X →ₗ.[ℝ] X}

/-! ## Passing to the limit in the Duhamel identity -/

/-- For a domain vector `x`, the Duhamel integrands of the Yosida approximations converge to the
limit orbit of `A x`, uniformly on the compact interval `[0, T]`.

Two errors are combined: `A_lambda x -> A x` in norm, and `exp (u A_lambda) (A x)` converges to
the limit orbit uniformly in `u`; contractivity of `exp (u A_lambda)` turns the first into a
uniform error as well. -/
private theorem tendstoUniformlyOn_duhamel_integrand (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) (x : A.domain) {T : ℝ} (hT : 0 ≤ T) :
    TendstoUniformlyOn
      (fun lambda u : ℝ =>
        exp (u • yosidaApproximation A lambda) (yosidaApproximation A lambda (x : X)))
      (fun u : ℝ => yosidaLimit A u (A x)) atTop (Set.Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hquot : Tendsto (fun lambda : ℝ => yosidaApproximation A lambda (x : X)) atTop
      (𝓝 (A x)) :=
    hA.tendsto_yosidaApproximation_apply_atTop hdense x
  have hquot' : ∀ᶠ lambda : ℝ in atTop,
      ‖yosidaApproximation A lambda (x : X) - A x‖ < epsilon / 2 := by
    have := tendsto_iff_norm_sub_tendsto_zero.mp hquot
    filter_upwards [this.eventually (eventually_lt_nhds (by positivity : (0 : ℝ) < epsilon / 2))]
      with lambda h using h
  have huniform := (hA.tendstoUniformlyOn_exp_yosidaApproximation hdense (A x) hT)
  rw [Metric.tendstoUniformlyOn_iff] at huniform
  filter_upwards [hquot', huniform (epsilon / 2) (by positivity),
    eventually_gt_atTop (0 : ℝ)] with lambda hclose huni hlambda u hu
  have hcontr : ‖exp (u • yosidaApproximation A lambda)‖ ≤ 1 :=
    norm_exp_smul_yosidaApproximation_le_one
      (hA.mul_norm_resolvent_le_one hlambda) hlambda hu.1
  have hsplit :
      yosidaLimit A u (A x) -
          exp (u • yosidaApproximation A lambda) (yosidaApproximation A lambda (x : X)) =
        (yosidaLimit A u (A x) - exp (u • yosidaApproximation A lambda) (A x)) -
          exp (u • yosidaApproximation A lambda)
            (yosidaApproximation A lambda (x : X) - A x) := by
    rw [map_sub]
    abel
  have hfirst : ‖exp (u • yosidaApproximation A lambda)
      (yosidaApproximation A lambda (x : X) - A x)‖ < epsilon / 2 := by
    calc ‖exp (u • yosidaApproximation A lambda)
          (yosidaApproximation A lambda (x : X) - A x)‖
        ≤ ‖exp (u • yosidaApproximation A lambda)‖ *
            ‖yosidaApproximation A lambda (x : X) - A x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖yosidaApproximation A lambda (x : X) - A x‖ := by
          simpa using mul_le_mul_of_nonneg_right hcontr (norm_nonneg _)
      _ < epsilon / 2 := hclose
  have hsecond : ‖yosidaLimit A u (A x) - exp (u • yosidaApproximation A lambda) (A x)‖
      < epsilon / 2 := by
    have := huni u hu
    rwa [dist_eq_norm] at this
  rw [dist_eq_norm, hsplit]
  calc ‖(yosidaLimit A u (A x) - exp (u • yosidaApproximation A lambda) (A x)) -
        exp (u • yosidaApproximation A lambda)
          (yosidaApproximation A lambda (x : X) - A x)‖
      ≤ ‖yosidaLimit A u (A x) - exp (u • yosidaApproximation A lambda) (A x)‖ +
        ‖exp (u • yosidaApproximation A lambda)
          (yosidaApproximation A lambda (x : X) - A x)‖ := norm_sub_le _ _
    _ < epsilon / 2 + epsilon / 2 := by gcongr
    _ = epsilon := add_halves epsilon

/-- **The integrated Cauchy problem for the Yosida limit.** For `x ∈ D(A)` and `t ≥ 0`,

`S(t) x - x = ∫₀ᵗ S(u) (A x) du`,

where `S` is the Yosida limit semigroup. Both sides of the Duhamel identity for the bounded
approximations converge, the integral because its integrand converges uniformly on `[0, t]`. -/
theorem yosidaLimit_sub_eq_intervalIntegral (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) (x : A.domain) {t : ℝ} (ht : 0 ≤ t) :
    yosidaLimit A t (x : X) - (x : X) = ∫ u in (0 : ℝ)..t, yosidaLimit A u (A x) := by
  -- The Duhamel integrals converge to the integral of the limit orbit, because their integrands
  -- converge uniformly on `[0, t]` and are continuous there.
  have hint : Tendsto (fun lambda : ℝ =>
      ∫ u in (0 : ℝ)..t, exp (u • yosidaApproximation A lambda)
        (yosidaApproximation A lambda (x : X))) atTop
      (𝓝 (∫ u in (0 : ℝ)..t, yosidaLimit A u (A x))) :=
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (.of_forall fun lambda =>
        ((differentiable_exp_smul_const ℝ
          (yosidaApproximation A lambda)).continuous.clm_apply continuous_const).continuousOn)
      (by rw [Set.uIcc_of_le ht]; exact hA.tendstoUniformlyOn_duhamel_integrand hdense x ht)
  refine tendsto_nhds_unique ?_ hint
  have heq : ∀ lambda : ℝ,
      (∫ u in (0 : ℝ)..t, exp (u • yosidaApproximation A lambda)
        (yosidaApproximation A lambda (x : X))) =
      exp (t • yosidaApproximation A lambda) (x : X) - (x : X) := fun lambda =>
    (ContinuousLinearMap.exp_smul_apply_sub_eq_intervalIntegral
      (yosidaApproximation A lambda) t (x : X)).symm
  simp only [heq]
  exact (hA.tendsto_yosidaLimit hdense ht (x : X)).sub_const _

/-! ## Identification of the generator -/

/-- For `x ∈ D(A)`, the difference quotients of the Yosida limit semigroup converge to `A x`:
by the integrated Cauchy problem they are the orbit averages of `A x`, which converge to `A x`
by strong continuity. -/
private theorem tendsto_genQuot_yosidaLimitSemigroup (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) (x : A.domain) :
    Tendsto (fun t : ℝ => (1 / t) •
        ((hA.yosidaLimitSemigroup hdense).realOperator t (x : X) - (x : X)))
      (𝓝[>] (0 : ℝ)) (𝓝 (A x)) := by
  refine ((hA.yosidaLimitSemigroup
    hdense).toStronglyContinuousSemigroup.tendsto_average_orbit_zero (A x)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : (0 : ℝ) < t)
  refine congrArg _ ?_
  rw [hA.yosidaLimitSemigroup_realOperator_apply hdense ht.le,
    hA.yosidaLimit_sub_eq_intervalIntegral hdense x ht.le,
    intervalIntegral.integral_of_le ht.le]
  refine (MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_).symm
  exact (hA.yosidaLimitSemigroup_realOperator_apply hdense hu.1.le (A x)).symm

/-- The operator `A` is a restriction of the generator of its Yosida limit semigroup. -/
private theorem le_yosidaLimitSemigroup_generator (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) :
    A ≤ (hA.yosidaLimitSemigroup hdense).toStronglyContinuousSemigroup.generator := by
  set S := (hA.yosidaLimitSemigroup hdense).toStronglyContinuousSemigroup with hS
  have hmem : ∀ y : A.domain, (y : X) ∈ S.domain := fun y =>
    (S.mem_domain_iff_tendsto (y : X)).mpr ⟨A y, hA.tendsto_genQuot_yosidaLimitSemigroup hdense y⟩
  refine ⟨fun y hy => ?_, fun y z hyz => ?_⟩
  · rw [S.generator_domain]
    exact hmem ⟨y, hy⟩
  · have hgen := S.generator_eq_of_tendsto (hmem y)
      (hA.tendsto_genQuot_yosidaLimitSemigroup hdense y)
    rw [← hgen]
    exact congrArg _ (Subtype.ext hyz)

/-- **The generator of the Yosida limit semigroup is the operator it was built from.** For a
densely defined m-dissipative `A`, the semigroup `yosidaLimitSemigroup` has generator `A`. -/
@[simp]
theorem yosidaLimitSemigroup_generator (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) :
    (hA.yosidaLimitSemigroup hdense).toStronglyContinuousSemigroup.generator = A :=
  (LinearPMap.eq_of_le_of_mem_resolventSet (hA.le_yosidaLimitSemigroup_generator hdense)
    (hA.mem_resolventSet one_pos)
    ((ContractionSemigroup.isMDissipative_generator _).mem_resolventSet one_pos)).symm

/-- **The Lumer--Phillips generation theorem.** A densely defined m-dissipative operator on a
real Banach space generates a strongly continuous contraction semigroup.

Dissipativity plus the range condition packaged in `IsMDissipative` is exactly the hypothesis
set of Lumer--Phillips; the semigroup produced is the strong limit of the semigroups generated
by the Yosida approximations of `A`. -/
theorem exists_contractionSemigroup_generator_eq (hA : IsMDissipative A)
    (hdense : Dense (A.domain : Set X)) :
    ∃ S : ContractionSemigroup X, S.toStronglyContinuousSemigroup.generator = A :=
  ⟨hA.yosidaLimitSemigroup hdense, hA.yosidaLimitSemigroup_generator hdense⟩

end IsMDissipative

/-- **Lumer--Phillips as a characterization.** An unbounded operator on a real Banach space is
the generator of a strongly continuous contraction semigroup if and only if it is densely
defined and m-dissipative.

The forward direction is the density of a generator domain together with the converse of
Lumer--Phillips; the backward direction is the generation theorem. -/
theorem exists_contractionSemigroup_generator_eq_iff (A : X →ₗ.[ℝ] X) :
    (∃ S : ContractionSemigroup X, S.toStronglyContinuousSemigroup.generator = A) ↔
      Dense (A.domain : Set X) ∧ IsMDissipative A := by
  refine ⟨fun ⟨S, hS⟩ => ⟨?_, ?_⟩, fun ⟨hdense, hA⟩ =>
    hA.exists_contractionSemigroup_generator_eq hdense⟩
  · have hdom : (A.domain : Set X) = (S.toStronglyContinuousSemigroup.domain : Set X) := by
      rw [← hS, S.toStronglyContinuousSemigroup.generator_domain]
    rw [hdom]
    exact S.toStronglyContinuousSemigroup.dense_domain
  · rw [← hS]
    exact ContractionSemigroup.isMDissipative_generator S

end TauCeti.Semigroups

end
