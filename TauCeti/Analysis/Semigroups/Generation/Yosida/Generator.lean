/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Generation.Yosida.Basic
-- The bounded-operator Duhamel identity is used only inside the proofs below.
import TauCeti.Analysis.Normed.Operator.Exponential

/-!
# Identifying the generator of a Yosida limit semigroup

This file isolates the final, common step in generation theorems proved by Yosida approximation.
Let `A` be an unbounded operator and suppose that the bounded semigroups

`exp (t A_lambda)`, where `A_lambda = lambda ^ 2 R(lambda, A) - lambda I`,

converge to a strongly continuous semigroup `S`: at each nonnegative time on a vector `x` of
`D(A)`, and uniformly on compact time intervals on the orbit of its image `A x`. If the operators
`A_lambda` converge to `A` on `D(A)` and the approximating semigroups are norm bounded on each
compact time interval, then `A` is a restriction of the generator of `S`.

The proof passes the bounded Duhamel identity

`exp (t A_lambda) x - x = integral_0^t exp (u A_lambda) (A_lambda x) du`

to the limit. For `x in D(A)`, the integrands converge uniformly to `S(u) (A x)`: one error is
the compact-time convergence of the orbit of `A x`, and the other is controlled by the time-local
operator bound and `A_lambda x -> A x`. Only the integrand needs uniform convergence; the left
side of the identity passes to the limit at the single time `t`. The resulting integrated
identity makes the generator difference quotients converge to `A x`. A shared resolvent point of
`A` and the generator then upgrades the restriction to equality.

This is the generator-identification rung that follows the construction of the limit semigroup in
a generation theorem. The Lumer--Phillips theorem in
`TauCeti/Analysis/Semigroups/Generation/LumerPhillips.lean` supplies the hypotheses with the
contraction bound `1`; `TauCeti/Analysis/Semigroups/Generation/HilleYosida/Generation.lean`
supplies them with the general Hille--Yosida growth constant `M`.

## Main results

* `TauCeti.Semigroups.StronglyContinuousSemigroup.le_generator_of_yosidaApproximation`:
  the original operator is a restriction of the generator of the compact-time limit semigroup.
* `TauCeti.Semigroups.StronglyContinuousSemigroup.generator_eq_of_yosidaApproximation`:
  a shared resolvent point identifies the generator with the original operator.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Theorem II.3.5.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 1, Theorem 3.1.
-/

public section

noncomputable section

open Filter MeasureTheory NormedSpace
open scoped NNReal Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-! ## Convergence of the Duhamel integrands -/

omit [CompleteSpace X] in
/-- If the orbits of `A x` under the Yosida semigroups converge uniformly on `[0, T]`, the
approximating operators converge at `x`, and the Yosida semigroups are eventually bounded in
operator norm by `K` on `[0, T]`, then the corresponding Duhamel integrands converge uniformly
on `[0, T]`. -/
private theorem tendstoUniformlyOn_yosidaDuhamel_integrand {A : X →ₗ.[ℝ] X}
    (S : StronglyContinuousSemigroup X) {K T : ℝ} (x : A.domain)
    (happrox : Tendsto (fun lambda : ℝ => yosidaApproximation A lambda (x : X)) atTop
      (𝓝 (A x)))
    (horbit : TendstoUniformlyOn
      (fun lambda u : ℝ => exp (u • yosidaApproximation A lambda) (A x))
      (fun u : ℝ => S.realOperator u (A x)) atTop (Set.Icc 0 T))
    (hbound : ∀ᶠ lambda in atTop, ∀ u ∈ Set.Icc (0 : ℝ) T,
      ‖exp (u • yosidaApproximation A lambda)‖ ≤ K) :
    TendstoUniformlyOn
      (fun lambda u : ℝ =>
        exp (u • yosidaApproximation A lambda) (yosidaApproximation A lambda (x : X)))
      (fun u : ℝ => S.realOperator u (A x)) atTop (Set.Icc 0 T) := by
  -- Replacing `K` by `max K 1` makes the error budget `epsilon / K` available without assuming
  -- anything about the sign of `K`.
  have hKpos : (0 : ℝ) < max K 1 := lt_of_lt_of_le zero_lt_one (le_max_right K 1)
  -- The two integrands differ by the bounded operator applied to `A_lambda x - A x`, which
  -- tends to `0` uniformly in the time parameter.
  have herr : TendstoUniformlyOn
      (fun lambda u : ℝ =>
        exp (u • yosidaApproximation A lambda) (yosidaApproximation A lambda (x : X) - A x))
      0 atTop (Set.Icc 0 T) := by
    rw [SeminormedAddGroup.tendstoUniformlyOn_zero]
    intro epsilon hepsilon
    have hclose : ∀ᶠ lambda : ℝ in atTop,
        ‖yosidaApproximation A lambda (x : X) - A x‖ < epsilon / max K 1 :=
      (tendsto_iff_norm_sub_tendsto_zero.mp happrox).eventually
        (eventually_lt_nhds (div_pos hepsilon hKpos))
    filter_upwards [hclose, hbound] with lambda hlambda hbound_lambda u hu
    calc
      ‖exp (u • yosidaApproximation A lambda)
          (yosidaApproximation A lambda (x : X) - A x)‖
          ≤ ‖exp (u • yosidaApproximation A lambda)‖ *
              ‖yosidaApproximation A lambda (x : X) - A x‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ max K 1 * ‖yosidaApproximation A lambda (x : X) - A x‖ := by
            gcongr
            exact (hbound_lambda u hu).trans (le_max_left K 1)
      _ < max K 1 * (epsilon / max K 1) := mul_lt_mul_of_pos_left hlambda hKpos
      _ = epsilon := by field_simp
  refine ((horbit.add herr).congr_right fun u _ => by simp).congr ?_
  filter_upwards with lambda u _
  simp only [Pi.add_apply]
  rw [← map_add]
  congr 1
  abel

namespace StronglyContinuousSemigroup

/-! ## The integrated Cauchy problem -/

/-- The bounded Duhamel identities pass to a compact-time Yosida limit. For every `x ∈ D(A)`
and `t ≥ 0`,

`S(t) x - x = integral_0^t S(u) (A x) du`.

This is the analytic core of generator identification. Only the orbit of `A x` is integrated, so
only it has to converge uniformly on `[0, t]`; for `x` itself convergence at the single time `t`
suffices. -/
private theorem realOperator_sub_eq_intervalIntegral_of_yosidaApproximation
    (S : StronglyContinuousSemigroup X) {A : X →ₗ.[ℝ] X} {K t : ℝ}
    (x : A.domain) (ht : 0 ≤ t)
    (happrox : Tendsto (fun lambda : ℝ => yosidaApproximation A lambda (x : X)) atTop
      (𝓝 (A x)))
    (hpoint_x : Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) (x : X)) atTop
      (𝓝 (S.realOperator t (x : X))))
    (huniform_Ax : TendstoUniformlyOn
      (fun lambda u : ℝ => exp (u • yosidaApproximation A lambda) (A x))
      (fun u : ℝ => S.realOperator u (A x)) atTop (Set.Icc 0 t))
    (hbound : ∀ᶠ lambda in atTop, ∀ u ∈ Set.Icc (0 : ℝ) t,
      ‖exp (u • yosidaApproximation A lambda)‖ ≤ K) :
    S.realOperator t (x : X) - (x : X) =
      ∫ u in (0 : ℝ)..t, S.realOperator u (A x) := by
  have hintegrand := tendstoUniformlyOn_yosidaDuhamel_integrand S x happrox huniform_Ax hbound
  have hint : Tendsto (fun lambda : ℝ =>
      ∫ u in (0 : ℝ)..t, exp (u • yosidaApproximation A lambda)
        (yosidaApproximation A lambda (x : X))) atTop
      (𝓝 (∫ u in (0 : ℝ)..t, S.realOperator u (A x))) :=
    TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
      (.of_forall fun lambda =>
        ((differentiable_exp_smul_const ℝ
          (yosidaApproximation A lambda)).continuous.clm_apply continuous_const).continuousOn)
      (by simpa only [Set.uIcc_of_le ht] using hintegrand)
  refine tendsto_nhds_unique ?_ hint
  have heq : ∀ lambda : ℝ,
      (∫ u in (0 : ℝ)..t, exp (u • yosidaApproximation A lambda)
        (yosidaApproximation A lambda (x : X))) =
      exp (t • yosidaApproximation A lambda) (x : X) - (x : X) := fun lambda =>
    (ContinuousLinearMap.exp_smul_apply_sub_eq_intervalIntegral
      (yosidaApproximation A lambda) t (x : X)).symm
  simp only [heq]
  exact hpoint_x.sub_const _

/-! ## Identification of the generator -/

/-- If Yosida exponentials converge to `S` — at each nonnegative time on the orbit of a domain
vector, and uniformly on compact time intervals on the orbit of its image — the approximating
generators converge to `A` on its domain, and the exponentials are bounded in operator norm on
each compact time interval, then `A` is a restriction of the generator of `S`.

The hypotheses are stated independently so the theorem applies both to the contraction estimates
in Lumer--Phillips and to the general power estimates in Hille--Yosida. -/
theorem le_generator_of_yosidaApproximation
    (S : StronglyContinuousSemigroup X) {A : X →ₗ.[ℝ] X}
    (happrox : ∀ x : A.domain,
      Tendsto (fun lambda : ℝ => yosidaApproximation A lambda (x : X)) atTop (𝓝 (A x)))
    (hpoint : ∀ (x : A.domain) {t : ℝ}, 0 ≤ t →
      Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) (x : X)) atTop
        (𝓝 (S.realOperator t (x : X))))
    (huniform : ∀ (x : A.domain) {T : ℝ}, 0 ≤ T →
      TendstoUniformlyOn
        (fun lambda u : ℝ => exp (u • yosidaApproximation A lambda) (A x))
        (fun u : ℝ => S.realOperator u (A x)) atTop (Set.Icc 0 T))
    (hbound : ∀ {T : ℝ}, 0 < T → ∃ K : ℝ, ∀ᶠ lambda in atTop, ∀ u ∈ Set.Icc (0 : ℝ) T,
      ‖exp (u • yosidaApproximation A lambda)‖ ≤ K) :
    A ≤ S.generator := by
  refine S.le_generator_of_forall_tendsto fun x => ?_
  refine (S.tendsto_average_orbit_zero (A x)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (ht : (0 : ℝ) < t)
  obtain ⟨K, hK⟩ := hbound ht
  refine congrArg _ ?_
  rw [S.realOperator_sub_eq_intervalIntegral_of_yosidaApproximation x ht.le (happrox x)
    (hpoint x ht.le) (huniform x ht.le) hK, intervalIntegral.integral_of_le ht.le]

/-- **A compact-time Yosida limit semigroup has generator `A`.** In addition to the convergence
and boundedness hypotheses giving `A ≤ generator S`, it suffices that `A` and the generator have
one shared resolvent point.

This is the reusable generator-identification step of a Yosida-approximation generation theorem;
`IsMDissipative.yosidaLimitSemigroup_generator` is the Lumer--Phillips instance. -/
theorem generator_eq_of_yosidaApproximation
    (S : StronglyContinuousSemigroup X) {A : X →ₗ.[ℝ] X} {lambda : ℝ}
    (hres : lambda ∈ LinearPMap.resolventSet A)
    (hgenres : lambda ∈ LinearPMap.resolventSet S.generator)
    (happrox : ∀ x : A.domain,
      Tendsto (fun mu : ℝ => yosidaApproximation A mu (x : X)) atTop (𝓝 (A x)))
    (hpoint : ∀ (x : A.domain) {t : ℝ}, 0 ≤ t →
      Tendsto (fun mu : ℝ => exp (t • yosidaApproximation A mu) (x : X)) atTop
        (𝓝 (S.realOperator t (x : X))))
    (huniform : ∀ (x : A.domain) {T : ℝ}, 0 ≤ T →
      TendstoUniformlyOn
        (fun mu u : ℝ => exp (u • yosidaApproximation A mu) (A x))
        (fun u : ℝ => S.realOperator u (A x)) atTop (Set.Icc 0 T))
    (hbound : ∀ {T : ℝ}, 0 < T → ∃ K : ℝ, ∀ᶠ mu in atTop, ∀ u ∈ Set.Icc (0 : ℝ) T,
      ‖exp (u • yosidaApproximation A mu)‖ ≤ K) :
    S.generator = A :=
  (LinearPMap.eq_of_le_of_mem_resolventSet
    (S.le_generator_of_yosidaApproximation happrox hpoint huniform hbound)
    hres hgenres).symm

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end
