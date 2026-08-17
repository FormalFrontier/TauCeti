/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Basic
public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded
public import TauCeti.Analysis.Semigroups.Generator.OrbitDerivative

/-!
# The Laplace-transform resolvent is the resolvent of the generator

This file proves that the Laplace-transform resolvent is also a left inverse of
`lambda • I - A` on the generator domain. Together with the right-inverse identity from
`TauCeti/Analysis/Semigroups/Resolvent/Basic.lean` that identifies it as *the* resolvent of the
generator in the unbounded sense of
`TauCeti/Analysis/Normed/Operator/Resolvent/Unbounded.lean`:
`StronglyContinuousSemigroup.generator_resolvent_eq` says
`LinearPMap.resolvent S.generator lambda = S.resolvent hb lambda hlambda` for `lambda` beyond
the growth exponent.

Everything else here is read off that bridge. The resolvent identity
`R(lambda) - R(mu) = (mu - lambda) R(lambda) R(mu)` and commutativity of resolvents are the
abstract `LinearPMap.resolvent_sub_resolvent` and `LinearPMap.resolvent_comm` transported along
it, rather than separate arguments; the identity is recorded both for `resolvent` and for
`resolventFun`, the resolvent seen as a function of the spectral parameter alone. The bridge
also transports the Laplace-transform norm estimate to the abstract resolvent:
`‖R(lambda, A)‖ ≤ M / (lambda - omega)`. The sharp power estimate is proved from the integral
power formula in `TauCeti/Analysis/Semigroups/Resolvent/PowerBounds.lean`.

## References

The argument follows Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
Theorem II.1.10: integration of the derivative of `exp (-lambda * t) • S(t)x` gives the
left-inverse formula, from which the algebraic resolvent identity follows. The generation
estimates are Theorem II.3.5 there.
-/

public section

noncomputable section

open scoped NNReal Topology
open MeasureTheory

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

namespace StronglyContinuousSemigroup

/-- The exponentially weighted orbit of a generator-domain vector tends to zero when the
exponential rate is larger than the semigroup growth exponent. -/
private theorem tendsto_exp_neg_smul_realOperator_atTop (S : StronglyContinuousSemigroup X)
    {omega M lambda : ℝ} (hb : S.HasGrowthBound omega M) (hlambda : omega < lambda) (x : S.domain) :
    Filter.Tendsto (fun t : ℝ => Real.exp (-(lambda * t)) • S.realOperator t (x : X))
      Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (g := fun t : ℝ =>
      (M * ‖(x : X)‖) * Real.exp (-((lambda - omega) * t)))
    (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(lambda * t)) * ‖S.realOperator t (x : X)‖
        ≤ Real.exp (-(lambda * t)) * (M * Real.exp (omega * t) * ‖(x : X)‖) := by
          gcongr
          exact le_trans (ContinuousLinearMap.le_opNorm _ _)
            (by gcongr; exact hb.bound t ht.le)
      _ = M * ‖(x : X)‖ * Real.exp (-((lambda - omega) * t)) := by
          ring_nf
          rw [Real.exp_add]
          ring
  · have hrate : Filter.Tendsto (fun t : ℝ => (lambda - omega) * t)
        Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop (sub_pos.mpr hlambda)
    simpa only [Function.comp_apply, smul_eq_mul, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hrate).const_mul (M * ‖(x : X)‖)

/-- At a **positive** time the weighted orbit is two-sidedly differentiable: the orbit derivative
is already known within `Set.Ici 0`, which is a neighbourhood of any `t > 0`. -/
private theorem hasDerivAt_exp_neg_smul_realOperator
    (S : StronglyContinuousSemigroup X) [CompleteSpace X] (lambda : ℝ) (x : S.domain) {t : ℝ}
    (ht : 0 < t) :
    HasDerivAt
      (fun u : ℝ => Real.exp (-(lambda * u)) • S.realOperator u (x : X))
      (Real.exp (-(lambda * t)) •
        (S.realOperator t (S.generator
          ⟨x, by rw [S.generator_domain]; exact x.property⟩) -
          lambda • S.realOperator t (x : X))) t := by
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-(lambda * u)))
      (-lambda * Real.exp (-(lambda * t))) t := by
    have h := (Real.hasDerivAt_exp (t * -lambda)).comp t (hasDerivAt_mul_const (-lambda))
    have heq : (fun u : ℝ => Real.exp (u * -lambda)) =
        fun u => Real.exp (-(lambda * u)) := by
      funext u
      congr 1
      ring
    rw [← heq]
    exact h.congr_deriv (by ring_nf)
  have horbit : HasDerivAt (fun s : ℝ => S.realOperator s (x : X))
      (S.realOperator t (S.generator
        ⟨x, by rw [S.generator_domain]; exact x.property⟩)) t := by
    rw [← S.realOperator_generator_map ht.le x]
    exact (S.realOperator_hasDerivWithinAt_Ici x ht.le).hasDerivAt (Ici_mem_nhds ht)
  refine (hexp.smul horbit).congr_deriv ?_
  module

/-- The Laplace-transform resolvent is a left inverse to `lambda • I - A` on the generator
domain: `R(lambda) (lambda x - A x) = x`. -/
@[simp] theorem resolventLeftInv (S : StronglyContinuousSemigroup X) {omega M : ℝ} [CompleteSpace X]
    (hb : S.HasGrowthBound omega M) (lambda : ℝ) (hlambda : omega < lambda) (x : S.domain) :
    S.resolvent hb lambda hlambda
        (lambda • (x : X) - S.generator
          ⟨x, by rw [S.generator_domain]; exact x.property⟩) = x := by
  let Ax : X := S.generator ⟨x, by rw [S.generator_domain]; exact x.property⟩
  let g := fun t : ℝ => Real.exp (-(lambda * t)) • S.realOperator t (x : X)
  let g' := fun t : ℝ => Real.exp (-(lambda * t)) •
    (S.realOperator t Ax - lambda • S.realOperator t (x : X))
  have hg_cont : ContinuousOn g (Set.Ici 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn.smul
      (S.realOperator_continuousOn_Ici (x : X))
  have hg_deriv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt g (g' t) t := by
    intro t ht
    simpa only [g, g', Ax] using S.hasDerivAt_exp_neg_smul_realOperator lambda x ht
  have hg'_int : IntegrableOn g' (Set.Ioi 0) := by
    have hAx := S.integrableOn_resolvent_integrand hb lambda hlambda Ax
    have hx := S.integrableOn_resolvent_integrand hb lambda hlambda (lambda • (x : X))
    convert hAx.sub hx using 1
    ext t
    simp only [g', Pi.sub_apply, map_smul, smul_sub, smul_smul]
  have h_integral : ∫ t in Set.Ioi (0 : ℝ), g' t = -(x : X) := by
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto (hg_cont 0 Set.self_mem_Ici)
      hg_deriv hg'_int (S.tendsto_exp_neg_smul_realOperator_atTop hb hlambda x)]
    simp only [g, mul_zero, neg_zero, Real.exp_zero, S.realOperator_zero_apply, one_smul, zero_sub]
  rw [S.resolvent_apply]
  have hpoint : ∀ t : ℝ,
      Real.exp (-(lambda * t)) • S.realOperator t
          (lambda • (x : X) - Ax) = -g' t := by
    intro t
    simp only [g', map_sub, map_smul, smul_sub, smul_smul]
    module
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpoint t)]
  rw [MeasureTheory.integral_neg, h_integral, neg_neg]

/-! ## The bridge to the resolvent of the generator -/

/-- For a C₀-semigroup with growth bound `(omega, M)` and `lambda > omega`, the
Laplace-transform resolvent `R(lambda) x = ∫₀^∞ e^{-λt} S(t) x dt` inverts `lambda • I - A` for
the generator `A`: it lands in `D(A)` (`StronglyContinuousSemigroup.resolvent_mem_domain`) and
is a two-sided inverse there (`StronglyContinuousSemigroup.resolventRightInv`,
`StronglyContinuousSemigroup.resolventLeftInv`). -/
theorem isResolventAt_generator (S : StronglyContinuousSemigroup X) [CompleteSpace X]
    {omega M : ℝ} (hb : S.HasGrowthBound omega M) {lambda : ℝ} (hlambda : omega < lambda) :
    LinearPMap.IsResolventAt S.generator lambda (S.resolvent hb lambda hlambda) where
  mem_domain y := by
    rw [S.generator_domain]
    exact S.resolvent_mem_domain hb lambda hlambda y
  smul_sub_apply y := S.resolventRightInv hb lambda hlambda y
  apply_smul_sub x :=
    S.resolventLeftInv hb lambda hlambda ⟨(x : X), by rw [← S.generator_domain]; exact x.property⟩

/-- Every `lambda` beyond the growth exponent lies in the resolvent set of the generator. -/
theorem mem_resolventSet_generator (S : StronglyContinuousSemigroup X) [CompleteSpace X]
    {omega M : ℝ} (hb : S.HasGrowthBound omega M) {lambda : ℝ} (hlambda : omega < lambda) :
    lambda ∈ LinearPMap.resolventSet S.generator :=
  (S.isResolventAt_generator hb hlambda).mem_resolventSet

/-- The half-line `(omega, ∞)` lies in the resolvent set of the generator — the hypothesis `hres`
of the Hille--Yosida generation theorem, here in its (already available) converse direction. -/
theorem Ioi_subset_resolventSet_generator (S : StronglyContinuousSemigroup X) [CompleteSpace X]
    {omega M : ℝ} (hb : S.HasGrowthBound omega M) :
    Set.Ioi omega ⊆ LinearPMap.resolventSet S.generator :=
  fun _ hlambda => S.mem_resolventSet_generator hb hlambda

/-- **The Laplace-transform bridge.** The resolvent of the generator, in the unbounded sense, is
the Laplace transform `R(lambda) x = ∫₀^∞ e^{-λt} S(t) x dt`. -/
theorem generator_resolvent_eq (S : StronglyContinuousSemigroup X) [CompleteSpace X]
    {omega M : ℝ} (hb : S.HasGrowthBound omega M) {lambda : ℝ} (hlambda : omega < lambda) :
    LinearPMap.resolvent S.generator lambda = S.resolvent hb lambda hlambda :=
  LinearPMap.resolvent_eq_of_isResolventAt (S.isResolventAt_generator hb hlambda)

/-- **Hille--Yosida resolvent bound** for the resolvent of the generator:
`‖R(lambda, A)‖ ≤ M / (lambda - omega)`. -/
theorem norm_generator_resolvent_le (S : StronglyContinuousSemigroup X) [CompleteSpace X]
    {omega M : ℝ} (hb : S.HasGrowthBound omega M) {lambda : ℝ} (hlambda : omega < lambda) :
    ‖LinearPMap.resolvent S.generator lambda‖ ≤ M / (lambda - omega) := by
  rw [S.generator_resolvent_eq hb hlambda]
  exact S.resolvent_norm_le hb lambda hlambda

/-! ## The resolvent identity -/

/-- Pointwise form of the resolvent identity
`R(lambda) - R(mu) = (mu - lambda) R(lambda) R(mu)`; the abstract
`TauCeti.LinearPMap.resolvent_sub_resolvent_apply` read through the bridge. -/
theorem resolvent_sub_resolvent_apply (S : StronglyContinuousSemigroup X)
    {omegaLambda MLambda omegaMu MMu : ℝ} [CompleteSpace X]
    (hbLambda : S.HasGrowthBound omegaLambda MLambda)
    (hbMu : S.HasGrowthBound omegaMu MMu) (lambda mu : ℝ)
    (hlambda : omegaLambda < lambda) (hmu : omegaMu < mu) (x : X) :
    S.resolvent hbLambda lambda hlambda x - S.resolvent hbMu mu hmu x =
      (mu - lambda) •
        S.resolvent hbLambda lambda hlambda (S.resolvent hbMu mu hmu x) := by
  rw [← S.generator_resolvent_eq hbLambda hlambda, ← S.generator_resolvent_eq hbMu hmu]
  exact LinearPMap.resolvent_sub_resolvent_apply (S.mem_resolventSet_generator hbLambda hlambda)
    (S.mem_resolventSet_generator hbMu hmu) x

/-- The resolvent identity
`R(lambda) - R(mu) = (mu - lambda) R(lambda) R(mu)` as an equality of continuous linear maps. -/
theorem resolvent_sub_resolvent (S : StronglyContinuousSemigroup X)
    {omegaLambda MLambda omegaMu MMu : ℝ} [CompleteSpace X]
    (hbLambda : S.HasGrowthBound omegaLambda MLambda)
    (hbMu : S.HasGrowthBound omegaMu MMu) (lambda mu : ℝ)
    (hlambda : omegaLambda < lambda) (hmu : omegaMu < mu) :
    S.resolvent hbLambda lambda hlambda - S.resolvent hbMu mu hmu =
      (mu - lambda) •
        (S.resolvent hbLambda lambda hlambda ∘L S.resolvent hbMu mu hmu) := by
  rw [← S.generator_resolvent_eq hbLambda hlambda, ← S.generator_resolvent_eq hbMu hmu]
  exact LinearPMap.resolvent_sub_resolvent (S.mem_resolventSet_generator hbLambda hlambda)
    (S.mem_resolventSet_generator hbMu hmu)

/-- The resolvent identity for `resolventFun`, written in the ring `X →L[ℝ] X`. -/
theorem resolventFun_sub_resolventFun (S : StronglyContinuousSemigroup X) {omega M : ℝ}
    [CompleteSpace X] (hb : S.HasGrowthBound omega M) {lambda mu : ℝ}
    (hl : omega < lambda) (hm : omega < mu) :
    S.resolventFun hb lambda - S.resolventFun hb mu
      = (mu - lambda) • (S.resolventFun hb lambda * S.resolventFun hb mu) := by
  rw [S.resolventFun_of_lt hb hl, S.resolventFun_of_lt hb hm]
  exact S.resolvent_sub_resolvent hb hb lambda mu hl hm

/-- Resolvents at two admissible parameters commute. -/
theorem resolvent_comm (S : StronglyContinuousSemigroup X) {omegaLambda MLambda omegaMu MMu : ℝ}
    [CompleteSpace X] (hbLambda : S.HasGrowthBound omegaLambda MLambda)
    (hbMu : S.HasGrowthBound omegaMu MMu) (lambda mu : ℝ)
    (hlambda : omegaLambda < lambda) (hmu : omegaMu < mu) :
    S.resolvent hbLambda lambda hlambda ∘L S.resolvent hbMu mu hmu =
      S.resolvent hbMu mu hmu ∘L S.resolvent hbLambda lambda hlambda := by
  rw [← S.generator_resolvent_eq hbLambda hlambda, ← S.generator_resolvent_eq hbMu hmu]
  exact LinearPMap.resolvent_comm (S.mem_resolventSet_generator hbLambda hlambda)
    (S.mem_resolventSet_generator hbMu hmu)

end StronglyContinuousSemigroup

namespace ContractionSemigroup

/-- The contraction resolvent is a left inverse to `lambda • I - A` on the generator domain. -/
@[simp] theorem resolventLeftInv (S : ContractionSemigroup X) [CompleteSpace X]
    (lambda : ℝ) (hlambda : 0 < lambda) (x : S.toStronglyContinuousSemigroup.domain) :
    S.resolvent lambda hlambda
        (lambda • (x : X) - S.toStronglyContinuousSemigroup.generator
          ⟨x, by rw [StronglyContinuousSemigroup.generator_domain]; exact x.property⟩) = x :=
  by
    rw [S.resolvent_eq_stronglyContinuousSemigroup_resolvent]
    exact S.toStronglyContinuousSemigroup.resolventLeftInv S.hasGrowthBound lambda
      (by simpa using hlambda) x

/-- The resolvent identity for a contraction semigroup. -/
theorem resolvent_sub_resolvent (S : ContractionSemigroup X) [CompleteSpace X]
    (lambda mu : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu) :
    S.resolvent lambda hlambda - S.resolvent mu hmu =
      (mu - lambda) • (S.resolvent lambda hlambda ∘L S.resolvent mu hmu) :=
  by
    rw [S.resolvent_eq_stronglyContinuousSemigroup_resolvent,
      S.resolvent_eq_stronglyContinuousSemigroup_resolvent]
    exact S.toStronglyContinuousSemigroup.resolvent_sub_resolvent
      S.hasGrowthBound S.hasGrowthBound lambda mu
      (by simpa using hlambda) (by simpa using hmu)

/-- Pointwise form of the resolvent identity for a contraction semigroup. -/
theorem resolvent_sub_resolvent_apply (S : ContractionSemigroup X) [CompleteSpace X]
    (lambda mu : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu) (x : X) :
    S.resolvent lambda hlambda x - S.resolvent mu hmu x =
      (mu - lambda) • S.resolvent lambda hlambda (S.resolvent mu hmu x) :=
  by
    rw [S.resolvent_eq_stronglyContinuousSemigroup_resolvent,
      S.resolvent_eq_stronglyContinuousSemigroup_resolvent]
    exact S.toStronglyContinuousSemigroup.resolvent_sub_resolvent_apply
      S.hasGrowthBound S.hasGrowthBound lambda mu
      (by simpa using hlambda) (by simpa using hmu) x

/-- Resolvents of a contraction semigroup commute. -/
theorem resolvent_comm (S : ContractionSemigroup X) [CompleteSpace X]
    (lambda mu : ℝ) (hlambda : 0 < lambda) (hmu : 0 < mu) :
    S.resolvent lambda hlambda ∘L S.resolvent mu hmu =
      S.resolvent mu hmu ∘L S.resolvent lambda hlambda :=
  by
    rw [S.resolvent_eq_stronglyContinuousSemigroup_resolvent,
      S.resolvent_eq_stronglyContinuousSemigroup_resolvent]
    exact S.toStronglyContinuousSemigroup.resolvent_comm
      S.hasGrowthBound S.hasGrowthBound lambda mu
      (by simpa using hlambda) (by simpa using hmu)

/-- Every `lambda > 0` lies in the resolvent set of the generator of a contraction semigroup. -/
theorem mem_resolventSet_generator (S : ContractionSemigroup X) [CompleteSpace X] {lambda : ℝ}
    (hlambda : 0 < lambda) :
    lambda ∈ LinearPMap.resolventSet S.toStronglyContinuousSemigroup.generator :=
  S.toStronglyContinuousSemigroup.mem_resolventSet_generator S.hasGrowthBound
    (by simpa using hlambda)

/-- The resolvent of the generator of a contraction semigroup is its Laplace transform. -/
theorem generator_resolvent_eq (S : ContractionSemigroup X) [CompleteSpace X] {lambda : ℝ}
    (hlambda : 0 < lambda) :
    LinearPMap.resolvent S.toStronglyContinuousSemigroup.generator lambda
      = S.resolvent lambda hlambda := by
  rw [S.resolvent_eq_stronglyContinuousSemigroup_resolvent,
    S.toStronglyContinuousSemigroup.generator_resolvent_eq S.hasGrowthBound
      (by simpa using hlambda)]

end ContractionSemigroup

end TauCeti.Semigroups

end
