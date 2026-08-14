/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Generation.Yosida.Basic
public import TauCeti.Analysis.Semigroups.Resolvent.Identity
-- The bounded-operator Duhamel identity and the metric characterization of uniform convergence
-- are used only inside the proofs below.
import TauCeti.Analysis.Normed.Operator.Exponential
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Identifying the generator of a Yosida limit semigroup

This file isolates the final, common step in generation theorems proved by Yosida approximation.
Let `A` be an unbounded operator and suppose that the bounded semigroups

`exp (t A_lambda)`, where `A_lambda = lambda ^ 2 R(lambda, A) - lambda I`,

converge to a strongly continuous semigroup `S`: at each nonnegative time on a vector `x` of
`D(A)`, and uniformly on compact time intervals on its image `A x`. If the operators `A_lambda`
converge to `A` on `D(A)` and the approximating semigroups have a common operator-norm bound,
then `A` is a restriction of the generator of `S`.

The proof passes the bounded Duhamel identity

`exp (t A_lambda) x - x = integral_0^t exp (u A_lambda) (A_lambda x) du`

to the limit. For `x in D(A)`, the integrands converge uniformly to `S(u) (A x)`: one error is
the compact-time convergence of the orbit of `A x`, and the other is controlled by the common
operator bound and `A_lambda x -> A x`. Only the integrand needs uniform convergence; the left
side of the identity passes to the limit at the single time `t`. The resulting integrated
identity makes the generator difference quotients converge to `A x`. A shared resolvent point of
`A` and the generator then upgrades the restriction to equality.

This is the generator-identification rung used after constructing the limit semigroup in both
the Lumer--Phillips and Hille--Yosida generation theorems. The existing Lumer--Phillips theorem
supplies the hypotheses with common bound `1`; the general Hille--Yosida construction supplies
them with its growth constant `M`.

The formal proof generalizes and relocates the former Lumer--Phillips declarations
`IsMDissipative.tendstoUniformlyOn_duhamel_integrand`,
`IsMDissipative.yosidaLimit_sub_eq_intervalIntegral`,
`IsMDissipative.tendsto_genQuot_yosidaLimitSemigroup`, and
`IsMDissipative.le_yosidaLimitSemigroup_generator`. Their reusable replacements are the
Duhamel-integrand lemma below and the three public generator-identification results listed here.

## Main results

* `TauCeti.Semigroups.StronglyContinuousSemigroup.sub_eq_intervalIntegral_of_yosidaApproximation`:
  the bounded Duhamel identities pass to the compact-time limit.
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
/-- If the Yosida semigroups converge uniformly on `[0, T]`, their generators converge on a
domain vector, and their operator norms are eventually bounded by `K`, then the corresponding
Duhamel integrands converge uniformly on `[0, T]`.

Only positivity of `K` is needed for the error budget `epsilon / (2 * K)`. -/
private theorem tendstoUniformlyOn_yosidaDuhamel_integrand {A : X →ₗ.[ℝ] X}
    (S : StronglyContinuousSemigroup X) {K T : ℝ} (hK : 0 < K) (x : A.domain)
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
  rw [Metric.tendstoUniformlyOn_iff] at horbit ⊢
  intro epsilon hepsilon
  have hclose : ∀ᶠ lambda : ℝ in atTop,
      ‖yosidaApproximation A lambda (x : X) - A x‖ < epsilon / (2 * K) := by
    have hzero := tendsto_iff_norm_sub_tendsto_zero.mp happrox
    exact hzero.eventually (eventually_lt_nhds (div_pos hepsilon (mul_pos zero_lt_two hK)))
  filter_upwards [hclose, horbit (epsilon / 2) (by positivity), hbound]
    with lambda hlambda horbit_lambda hbound_lambda u hu
  have hsplit :
      S.realOperator u (A x) -
          exp (u • yosidaApproximation A lambda) (yosidaApproximation A lambda (x : X)) =
        (S.realOperator u (A x) - exp (u • yosidaApproximation A lambda) (A x)) -
          exp (u • yosidaApproximation A lambda)
            (yosidaApproximation A lambda (x : X) - A x) := by
    rw [map_sub]
    abel
  have hinput :
      ‖exp (u • yosidaApproximation A lambda)
          (yosidaApproximation A lambda (x : X) - A x)‖ < epsilon / 2 := by
    calc
      ‖exp (u • yosidaApproximation A lambda)
          (yosidaApproximation A lambda (x : X) - A x)‖
          ≤ ‖exp (u • yosidaApproximation A lambda)‖ *
              ‖yosidaApproximation A lambda (x : X) - A x‖ :=
            ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * ‖yosidaApproximation A lambda (x : X) - A x‖ := by
            gcongr
            exact hbound_lambda u hu
      _ < K * (epsilon / (2 * K)) := mul_lt_mul_of_pos_left hlambda hK
      _ = epsilon / 2 := by field_simp
  have horbit' :
      ‖S.realOperator u (A x) - exp (u • yosidaApproximation A lambda) (A x)‖ <
        epsilon / 2 := by
    simpa only [dist_eq_norm] using horbit_lambda u hu
  rw [dist_eq_norm, hsplit]
  exact (norm_sub_le _ _).trans_lt (by linarith)

/-! ## The integrated Cauchy problem -/

/-- The bounded Duhamel identities pass to a compact-time Yosida limit. For every `x ∈ D(A)`
and `t ≥ 0`,

`S(t) x - x = integral_0^t S(u) (A x) du`.

This is the analytic core of generator identification. Only the orbit of `A x` is integrated, so
only it has to converge uniformly on `[0, t]`; for `x` itself convergence at the single time `t`
suffices. -/
theorem StronglyContinuousSemigroup.sub_eq_intervalIntegral_of_yosidaApproximation
    (S : StronglyContinuousSemigroup X) {A : X →ₗ.[ℝ] X} {K t : ℝ} (hK : 0 < K)
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
  have hintegrand := tendstoUniformlyOn_yosidaDuhamel_integrand S hK x happrox
    huniform_Ax hbound
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
generators converge to `A` on its domain, and the exponentials have a common bound `K`, then `A`
is a restriction of the generator of `S`.

The hypotheses are stated independently so the theorem applies both to the contraction estimates
in Lumer--Phillips and to the general power estimates in Hille--Yosida. -/
theorem StronglyContinuousSemigroup.le_generator_of_yosidaApproximation
    (S : StronglyContinuousSemigroup X) {A : X →ₗ.[ℝ] X} {K : ℝ} (hK : 0 < K)
    (happrox : ∀ x : A.domain,
      Tendsto (fun lambda : ℝ => yosidaApproximation A lambda (x : X)) atTop (𝓝 (A x)))
    (hconv : ∀ (x : A.domain) {t : ℝ}, 0 ≤ t →
      Tendsto (fun lambda : ℝ => exp (t • yosidaApproximation A lambda) (x : X)) atTop
        (𝓝 (S.realOperator t (x : X))) ∧
      TendstoUniformlyOn
        (fun lambda u : ℝ => exp (u • yosidaApproximation A lambda) (A x))
        (fun u : ℝ => S.realOperator u (A x)) atTop (Set.Icc 0 t))
    (hbound : ∀ {T : ℝ}, 0 ≤ T →
      ∀ᶠ lambda in atTop, ∀ u ∈ Set.Icc (0 : ℝ) T,
        ‖exp (u • yosidaApproximation A lambda)‖ ≤ K) :
    A ≤ S.generator := by
  have htend : ∀ x : A.domain,
      Tendsto (fun t : ℝ => (1 / t) • (S.realOperator t (x : X) - (x : X)))
        (𝓝[>] (0 : ℝ)) (𝓝 (A x)) := by
    intro x
    refine (S.tendsto_average_orbit_zero (A x)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : (0 : ℝ) < t)
    refine congrArg _ ?_
    rw [S.sub_eq_intervalIntegral_of_yosidaApproximation hK x ht.le (happrox x)
      (hconv x ht.le).1 (hconv x ht.le).2 (hbound ht.le),
      intervalIntegral.integral_of_le ht.le]
  have hmem : ∀ x : A.domain, (x : X) ∈ S.domain := fun x =>
    (S.mem_domain_iff_tendsto (x : X)).mpr ⟨A x, htend x⟩
  refine ⟨fun x hx => ?_, fun x y hxy => ?_⟩
  · rw [S.generator_domain]
    exact hmem ⟨x, hx⟩
  · have hgen := S.generator_eq_of_tendsto (hmem x) (htend x)
    rw [← hgen]
    exact congrArg _ (Subtype.ext hxy)

/-- **A compact-time Yosida limit semigroup has generator `A`.** In addition to the convergence
and common-bound hypotheses giving `A ≤ generator S`, it suffices that `A` and the generator have
one shared resolvent point.

This is the reusable generator-identification step in the Hille--Yosida construction. -/
theorem StronglyContinuousSemigroup.generator_eq_of_yosidaApproximation
    (S : StronglyContinuousSemigroup X) {A : X →ₗ.[ℝ] X} {K lambda : ℝ}
    (hK : 0 < K) (hres : lambda ∈ LinearPMap.resolventSet A)
    (hgenres : lambda ∈ LinearPMap.resolventSet S.generator)
    (happrox : ∀ x : A.domain,
      Tendsto (fun mu : ℝ => yosidaApproximation A mu (x : X)) atTop (𝓝 (A x)))
    (hconv : ∀ (x : A.domain) {t : ℝ}, 0 ≤ t →
      Tendsto (fun mu : ℝ => exp (t • yosidaApproximation A mu) (x : X)) atTop
        (𝓝 (S.realOperator t (x : X))) ∧
      TendstoUniformlyOn
        (fun mu u : ℝ => exp (u • yosidaApproximation A mu) (A x))
        (fun u : ℝ => S.realOperator u (A x)) atTop (Set.Icc 0 t))
    (hbound : ∀ {T : ℝ}, 0 ≤ T →
      ∀ᶠ mu in atTop, ∀ u ∈ Set.Icc (0 : ℝ) T,
        ‖exp (u • yosidaApproximation A mu)‖ ≤ K) :
    S.generator = A :=
  (LinearPMap.eq_of_le_of_mem_resolventSet
    (S.le_generator_of_yosidaApproximation hK happrox hconv hbound)
    hres hgenres).symm

end TauCeti.Semigroups

end
