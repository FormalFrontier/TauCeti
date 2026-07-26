/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Basic
public import TauCeti.Analysis.Semigroups.Generator.OrbitDerivative

/-!
# The resolvent identity for strongly continuous semigroups

This file proves that the Laplace-transform resolvent is also a left inverse of
`lambda • I - A` on the generator domain. It then derives the resolvent identity
`R(lambda) - R(mu) = (mu - lambda) R(lambda) R(mu)` and commutativity of resolvents.

## References

The argument follows Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
Theorem II.1.10: integration of the derivative of `exp (-lambda * t) • S(t)x` gives the
left-inverse formula, from which the algebraic resolvent identity follows.
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
    {omega M lambda : ℝ} (hb : S.HasGrowthBound omega M) (hlambda : omega < lambda)
    (x : S.domain) :
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

/-- The derivative of an exponentially weighted orbit, using the right derivative supplied
by the C₀-semigroup generator API. -/
private theorem hasDerivWithinAt_exp_neg_smul_realOperator
    (S : StronglyContinuousSemigroup X) (lambda : ℝ) (x : S.domain) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun u : ℝ => Real.exp (-(lambda * u)) • S.realOperator u (x : X))
      (Real.exp (-(lambda * t)) •
        (S.realOperator t (S.generator
          ⟨x, by rw [S.generator_domain]; exact x.property⟩) -
          lambda • S.realOperator t (x : X)))
      (Set.Ioi t) t := by
  have hexp : HasDerivWithinAt (fun u : ℝ => Real.exp (-(lambda * u)))
      (-lambda * Real.exp (-(lambda * t))) (Set.Ioi t) t := by
    have h := (Real.hasDerivAt_exp (t * -lambda)).comp t (hasDerivAt_mul_const (-lambda))
    have heq : (fun u : ℝ => Real.exp (u * -lambda)) =
        fun u => Real.exp (-(lambda * u)) := by
      funext u
      congr 1
      ring
    rw [← heq]
    exact h.hasDerivWithinAt.congr_deriv (by ring_nf)
  have horbit := (S.realOperator_hasDerivWithinAt_map_generator x ht).mono
    (Set.Ioi_subset_Ici_self : Set.Ioi t ⊆ Set.Ici t)
  have h := hexp.smul horbit
  convert h using 1
  · rfl
  · module

/-- The Laplace-transform resolvent is a left inverse to `lambda • I - A` on the generator
domain: `R(lambda) (lambda x - A x) = x`. -/
@[simp] theorem resolventLeftInv (S : StronglyContinuousSemigroup X) {omega M : ℝ}
    [CompleteSpace X]
    (hb : S.HasGrowthBound omega M) (lambda : ℝ) (hlambda : omega < lambda)
    (x : S.domain) :
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
  have hg_deriv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt g (g' t) (Set.Ioi t) t := by
    intro t ht
    simpa only [g, g', Ax] using
      S.hasDerivWithinAt_exp_neg_smul_realOperator lambda x ht.le
  have hg'_cont : ContinuousOn g' (Set.Ici 0) := by
    apply ContinuousOn.smul
    · exact (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg)).continuousOn
    · exact (S.realOperator_continuousOn_Ici Ax).sub
        ((S.realOperator_continuousOn_Ici (x : X)).const_smul lambda)
  have hg'_int : IntegrableOn g' (Set.Ioi 0) := by
    have hAx := S.integrable_resolvent_integrand hb lambda hlambda Ax
    have hx := S.integrable_resolvent_integrand hb lambda hlambda (lambda • (x : X))
    convert hAx.sub hx using 1
    ext t
    simp only [g', Pi.sub_apply, map_smul, smul_sub, smul_smul]
  have hfinite : ∀ T : ℝ, 0 ≤ T → ∫ t in (0 : ℝ)..T, g' t = g T - (x : X) := by
    intro T hT
    have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT
      (hg_cont.mono Set.Icc_subset_Ici_self)
      (fun t ht => hg_deriv t ht.1)
      (hg'_cont.mono (by rw [Set.uIcc_of_le hT]; exact Set.Icc_subset_Ici_self)).intervalIntegrable
    have hg0 : g 0 = (x : X) := by simp only [g, mul_zero, neg_zero, Real.exp_zero,
      S.realOperator_zero_apply, one_smul]
    rwa [hg0] at hftc
  have h_integral : ∫ t in Set.Ioi (0 : ℝ), g' t = -(x : X) := by
    apply tendsto_nhds_unique
      (intervalIntegral_tendsto_integral_Ioi 0 hg'_int Filter.tendsto_id)
    have ht := (S.tendsto_exp_neg_smul_realOperator_atTop hb hlambda x).sub
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (x : X)) Filter.atTop (nhds x))
    have heq : (fun T => ∫ t in (0 : ℝ)..T, g' t) =ᶠ[Filter.atTop]
        (fun T => g T - (x : X)) := by
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
      exact hfinite T hT
    simpa only [id_eq, zero_sub] using ht.congr' heq.symm
  rw [S.resolvent_apply]
  have hpoint : ∀ t : ℝ,
      Real.exp (-(lambda * t)) • S.realOperator t
          (lambda • (x : X) - Ax) = -g' t := by
    intro t
    simp only [g', map_sub, map_smul, smul_sub, smul_smul]
    module
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t _ => hpoint t)]
  rw [MeasureTheory.integral_neg, h_integral, neg_neg]

/-- Pointwise form of the resolvent identity
`R(lambda) - R(mu) = (mu - lambda) R(lambda) R(mu)`. -/
theorem resolvent_sub_resolvent_apply (S : StronglyContinuousSemigroup X)
    {omegaLambda MLambda omegaMu MMu : ℝ}
    [CompleteSpace X]
    (hbLambda : S.HasGrowthBound omegaLambda MLambda)
    (hbMu : S.HasGrowthBound omegaMu MMu) (lambda mu : ℝ)
    (hlambda : omegaLambda < lambda) (hmu : omegaMu < mu) (x : X) :
    S.resolvent hbLambda lambda hlambda x - S.resolvent hbMu mu hmu x =
      (mu - lambda) •
        S.resolvent hbLambda lambda hlambda (S.resolvent hbMu mu hmu x) := by
  let y : S.domain :=
    ⟨S.resolvent hbMu mu hmu x, S.resolvent_mem_domain hbMu mu hmu x⟩
  have hleft := S.resolventLeftInv hbLambda lambda hlambda y
  have hright := S.resolventRightInv hbMu mu hmu x
  simp only [y] at hleft
  have hleft' : lambda • S.resolvent hbLambda lambda hlambda (S.resolvent hbMu mu hmu x) -
      S.resolvent hbLambda lambda hlambda
        (S.generator ⟨S.resolvent hbMu mu hmu x, by
          rw [S.generator_domain]
          exact S.resolvent_mem_domain hbMu mu hmu x⟩) = S.resolvent hbMu mu hmu x := by
    simpa only [map_sub, map_smul] using hleft
  calc
    _ = S.resolvent hbLambda lambda hlambda
          (mu • S.resolvent hbMu mu hmu x -
            S.generator ⟨S.resolvent hbMu mu hmu x, by
              rw [S.generator_domain]
              exact S.resolvent_mem_domain hbMu mu hmu x⟩) -
          S.resolvent hbMu mu hmu x := by rw [hright]
    _ = _ := by
      simp only [map_sub, map_smul]
      calc
        _ = (mu - lambda) •
              S.resolvent hbLambda lambda hlambda (S.resolvent hbMu mu hmu x) +
            (lambda • S.resolvent hbLambda lambda hlambda (S.resolvent hbMu mu hmu x) -
              S.resolvent hbLambda lambda hlambda
                (S.generator ⟨S.resolvent hbMu mu hmu x, by
                  rw [S.generator_domain]
                  exact S.resolvent_mem_domain hbMu mu hmu x⟩) -
              S.resolvent hbMu mu hmu x) := by module
        _ = _ := by rw [hleft']; simp

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
  ext x
  exact S.resolvent_sub_resolvent_apply hbLambda hbMu lambda mu hlambda hmu x

/-- Resolvents at two admissible parameters commute. -/
theorem resolvent_comm (S : StronglyContinuousSemigroup X)
    {omegaLambda MLambda omegaMu MMu : ℝ}
    [CompleteSpace X]
    (hbLambda : S.HasGrowthBound omegaLambda MLambda)
    (hbMu : S.HasGrowthBound omegaMu MMu) (lambda mu : ℝ)
    (hlambda : omegaLambda < lambda) (hmu : omegaMu < mu) :
    S.resolvent hbLambda lambda hlambda ∘L S.resolvent hbMu mu hmu =
      S.resolvent hbMu mu hmu ∘L S.resolvent hbLambda lambda hlambda := by
  ext x
  by_cases h : lambda = mu
  · subst mu
    have heq : S.resolvent hbLambda lambda hlambda = S.resolvent hbMu lambda hmu := by
      ext z
      rw [S.resolvent_apply hbLambda, S.resolvent_apply hbMu]
    rw [heq]
  · have h1 := S.resolvent_sub_resolvent_apply hbLambda hbMu lambda mu hlambda hmu x
    have h2 := S.resolvent_sub_resolvent_apply hbMu hbLambda mu lambda hmu hlambda x
    simp only [ContinuousLinearMap.comp_apply] at ⊢
    have h2' : S.resolvent hbLambda lambda hlambda x - S.resolvent hbMu mu hmu x =
        (mu - lambda) •
          S.resolvent hbMu mu hmu (S.resolvent hbLambda lambda hlambda x) := by
      calc
        _ = -(S.resolvent hbMu mu hmu x - S.resolvent hbLambda lambda hlambda x) := by abel
        _ = -((lambda - mu) •
            S.resolvent hbMu mu hmu (S.resolvent hbLambda lambda hlambda x)) := by rw [h2]
        _ = _ := by module
    have hz : (mu - lambda) •
        (S.resolvent hbLambda lambda hlambda (S.resolvent hbMu mu hmu x) -
          S.resolvent hbMu mu hmu (S.resolvent hbLambda lambda hlambda x)) = 0 := by
      rw [h1] at h2'
      rw [smul_sub, h2', sub_self]
    rcases (smul_eq_zero.mp hz) with hzero | hzero
    · exact (h (sub_eq_zero.mp hzero).symm).elim
    · exact sub_eq_zero.mp hzero

end StronglyContinuousSemigroup

namespace ContractionSemigroup

private theorem resolvent_eq_stronglyContinuousSemigroup_resolvent
    (S : ContractionSemigroup X) [CompleteSpace X] (lambda : ℝ) (hlambda : 0 < lambda) :
    S.resolvent lambda hlambda =
      S.toStronglyContinuousSemigroup.resolvent S.hasGrowthBound lambda
        (by simpa using hlambda) := by
  ext x
  rw [S.resolvent_apply, S.toStronglyContinuousSemigroup.resolvent_apply]

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

end ContractionSemigroup

end TauCeti.Semigroups

end
