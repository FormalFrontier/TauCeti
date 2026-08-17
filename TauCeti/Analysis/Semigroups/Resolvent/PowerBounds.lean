/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Deriv
import TauCeti.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Integral formulas and power bounds for semigroup resolvents

This file proves the integral formula for powers of a Laplace-transform resolvent,

`R(lambda)^(n+1) x = 1 / n! * integral t in (0, infinity), t^n exp (-lambda t) S(t)x dt`,

and derives the sharp iterated Hille--Yosida estimate for a semigroup with growth bound
`(omega, M)` (`norm (S(t)) <= M exp (omega t)` with `M >= 1`):

`norm (R(lambda)^n) <= M / (lambda - omega)^n` for `n >= 1`.

Only one factor of `M` occurs because `R(lambda)^(n+1)` is itself a single weighted orbit
integral, so the growth bound is applied once. This is sharper than applying submultiplicativity
to the first-resolvent bound, which would give `M^n / (lambda - omega)^n`.

For a contraction semigroup, this specializes to

`‖R(lambda)^n‖ ≤ lambda⁻ⁿ`.

Using `generator_resolvent_eq`, the sharp bound is also transported to the generator resolvent,

`‖R(lambda, generator S)^n‖ ≤ M / (lambda - omega)^n`,

with the corresponding contraction-semigroup specialization.

The corresponding pointwise estimates and the bound for the scaled contraction resolvent
`lambda R(lambda)` are also recorded. This is the necessity half of the Hille--Yosida generation
theorem: every C₀-semigroup's Laplace-transform resolvent, and hence its generator resolvent,
satisfies the sharp power bound used by the generation theorem.

The sharp derivative bound obtained from the power formula is recorded here in both the general
growth-bound and contraction cases.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Theorem II.1.10 and
Corollary II.1.11 for the power formula and bound; Theorems II.3.5--II.3.8 for the generation
theorems they support.
-/

public section

noncomputable section

open MeasureTheory
open scoped NNReal Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

variable (S : StronglyContinuousSemigroup X) {omega M : ℝ}

omit [CompleteSpace X] in
/-- A common exponential majorant when the spectral parameter stays above a fixed lower
bound. -/
private theorem norm_neg_pow_mul_resolvent_integrand_le (hb : S.HasGrowthBound omega M)
    (n : ℕ) (x : X) {t l delta : ℝ} (ht : 0 < t) (hdl : delta ≤ l - omega) :
    ‖(-(t ^ n * Real.exp (-(l * t)))) • S.realOperator t x‖ ≤
      M * ‖x‖ * (t ^ n * Real.exp (-(delta * t))) := by
  calc
    ‖(-(t ^ n * Real.exp (-(l * t)))) • S.realOperator t x‖
        = ‖(t ^ n * Real.exp (-(l * t))) • S.realOperator t x‖ := by
          rw [neg_smul, norm_neg]
    _ ≤ M * ‖x‖ * (t ^ n * Real.exp (-((l - omega) * t))) :=
          S.norm_pow_mul_resolvent_integrand_le hb n l x ht.le
    _ ≤ M * ‖x‖ * (t ^ n * Real.exp (-(delta * t))) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (by linarith [hb.one_le]) (norm_nonneg x))
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht.le _)
          exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right hdl ht.le))

omit [CompleteSpace X] in
/-- Differentiating the scalar Laplace weight introduces one power of time and a minus sign. -/
private theorem hasDerivAt_pow_mul_resolvent_integrand (n : ℕ) (t l : ℝ) (x : X) :
    HasDerivAt
      (fun y => (t ^ n * Real.exp (-(y * t))) • S.realOperator t x)
      ((-(t ^ (n + 1) * Real.exp (-(l * t)))) • S.realOperator t x) l := by
  have hinner : HasDerivAt (fun y : ℝ => -y * t) (-t) l := by
    have h' : HasDerivAt (fun y : ℝ => -y * t) (-1 * t) l := by
      simpa only [Pi.neg_apply, id_eq] using (hasDerivAt_id l).neg.mul_const t
    exact h'.congr_deriv (by ring)
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y * t))
      (Real.exp (-l * t) * -t) l := by
    exact (Real.hasDerivAt_exp (-l * t)).comp l hinner
  have hscalar : HasDerivAt (fun y => t ^ n * Real.exp (-y * t))
      (-(t ^ (n + 1) * Real.exp (-l * t))) l :=
    (hexp.const_mul (t ^ n)).congr_deriv (by ring)
  simpa only [neg_mul] using hscalar.smul_const (S.realOperator t x)

/-- The `n`-th weighted Laplace moment of a semigroup orbit. -/
private noncomputable def resolventMoment (S : StronglyContinuousSemigroup X) (n : ℕ)
    (lambda : ℝ) (x : X) : X :=
  ∫ t in Set.Ioi 0, (t ^ n * Real.exp (-(lambda * t))) • S.realOperator t x

/-- Differentiating a weighted Laplace moment introduces the next power of time and a minus
sign. -/
private theorem hasDerivAt_resolventMoment (hb : S.HasGrowthBound omega M) (n : ℕ)
    {lambda : ℝ} (hlambda : omega < lambda) (x : X) :
    HasDerivAt (fun l => S.resolventMoment n l x) (-(S.resolventMoment (n + 1) lambda x))
      lambda := by
  -- Feed the dominated differentiation theorem, using half the distance to `omega` as a
  -- neighborhood radius so every derivative integrand has one uniform exponential majorant.
  let delta := (lambda - omega) / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  let U := Metric.ball lambda delta
  let F : ℝ → ℝ → X := fun l t =>
    (t ^ n * Real.exp (-(l * t))) • S.realOperator t x
  let F' : ℝ → ℝ → X := fun l t =>
    -(t ^ (n + 1) * Real.exp (-(l * t))) • S.realOperator t x
  let bound : ℝ → ℝ := fun t =>
    M * ‖x‖ * (t ^ (n + 1) * Real.exp (-(delta * t)))
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi 0)) := by
    exact (integrableOn_pow_mul_exp_neg_mul_Ioi (n + 1) hdelta).integrable.const_mul
      (M * ‖x‖)
  have hF_meas : ∀ᶠ l in 𝓝 lambda,
      AEStronglyMeasurable (F l) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards [isOpen_Ioi.eventually_mem hlambda] with l hl
    exact (S.integrableOn_pow_mul_resolvent_integrand hb n l hl x).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' lambda) (volume.restrict (Set.Ioi 0)) := by
    have hmeas : AEStronglyMeasurable
        (fun t : ℝ => (t ^ (n + 1) * Real.exp (-(lambda * t))) • S.realOperator t x)
        (volume.restrict (Set.Ioi 0)) :=
      (S.integrableOn_pow_mul_resolvent_integrand hb (n + 1) lambda hlambda x).aestronglyMeasurable
    refine hmeas.neg.congr (ae_of_all _ fun t => ?_)
    simp only [F', neg_smul, Pi.neg_apply]
  have hdom : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), ∀ l ∈ U, ‖F' l t‖ ≤ bound t := by
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t ht l hl
    have hdl : delta ≤ l - omega := by
      rw [Metric.mem_ball, Real.dist_eq] at hl
      have hlower := neg_lt_of_abs_lt hl
      dsimp only [delta] at hlower ⊢
      linarith
    dsimp only [F', bound]
    exact S.norm_neg_pow_mul_resolvent_integrand_le hb (n + 1) x ht hdl
  have hdiff : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), ∀ l ∈ U,
      HasDerivAt (F · t) (F' l t) l := by
    filter_upwards [] with t l hl
    dsimp only [F, F']
    exact S.hasDerivAt_pow_mul_resolvent_integrand n t l x
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0)) (F := F) (F' := F') (bound := bound)
    (Metric.ball_mem_nhds lambda hdelta) hF_meas
    (S.integrableOn_pow_mul_resolvent_integrand hb n lambda hlambda x).integrable hF'_meas hdom
    hbound_int hdiff
  simpa only [resolventMoment, F, F', neg_smul, integral_neg] using h.2

/-- Pointwise iterated derivatives of the resolvent are the signed weighted Laplace moments. -/
private theorem iteratedDeriv_resolventFun_apply_eq_resolventMoment
    (hb : S.HasGrowthBound omega M) (n : ℕ) {lambda : ℝ} (hlambda : omega < lambda) (x : X) :
    iteratedDeriv n (fun l => S.resolventFun hb l x) lambda =
      (-1 : ℝ) ^ n • S.resolventMoment n lambda x := by
  induction n generalizing lambda with
  | zero =>
      simp [resolventMoment, S.resolventFun_apply hb hlambda]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n (fun l => S.resolventFun hb l x) =ᶠ[𝓝 lambda]
          ((-1 : ℝ) ^ n • fun l => S.resolventMoment n l x) := by
        filter_upwards [isOpen_Ioi.eventually_mem hlambda] with l hl
        simpa only [Pi.smul_apply] using ih hl
      have hderiv :=
        (S.hasDerivAt_resolventMoment hb n hlambda x).const_smul ((-1 : ℝ) ^ n)
      rw [heq.deriv_eq, hderiv.deriv]
      rw [pow_succ]
      module

/-- Iterated differentiation commutes with evaluation of the operator-valued resolvent. -/
private theorem iteratedDeriv_resolventFun_apply
    (hb : S.HasGrowthBound omega M) (n : ℕ) {lambda : ℝ} (hlambda : omega < lambda) (x : X) :
    iteratedDeriv n (fun l => S.resolventFun hb l x) lambda =
      (iteratedDeriv n (S.resolventFun hb) lambda) x := by
  let ev := ContinuousLinearMap.apply ℝ X x
  have hcont := (S.contDiffOn_resolventFun hb).contDiffAt (isOpen_Ioi.mem_nhds hlambda)
  have h := ev.iteratedFDeriv_comp_left hcont (i := n) (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  have hcomp : (fun l => S.resolventFun hb l x) = ev ∘ S.resolventFun hb := by
    funext l
    simp [ev]
  rw [hcomp, h]
  simp only [ev, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, ContinuousLinearMap.apply_apply]

/-- Pointwise iterated derivatives of the resolvent are scalar multiples of resolvent powers. -/
private theorem iteratedDeriv_resolventFun_apply_eq_pow
    (hb : S.HasGrowthBound omega M) (n : ℕ) {lambda : ℝ} (hlambda : omega < lambda) (x : X) :
    iteratedDeriv n (fun l => S.resolventFun hb l x) lambda =
      ((-1 : ℝ) ^ n * n.factorial) • (S.resolventFun hb lambda ^ (n + 1)) x := by
  rw [S.iteratedDeriv_resolventFun_apply hb n hlambda x,
    S.iteratedDeriv_resolventFun hb n hlambda, smul_apply]

/-- The pointwise power formula for a semigroup resolvent:
`R(lambda)^(n+1)x = 1/n! integral t^n exp(-lambda t) S(t)x dt`. -/
theorem resolvent_pow_succ_apply (hb : S.HasGrowthBound omega M) (n : ℕ) {lambda : ℝ}
    (hlambda : omega < lambda) (x : X) :
    (S.resolvent hb lambda hlambda ^ (n + 1)) x =
      (1 / (n.factorial : ℝ)) •
        ∫ t in Set.Ioi 0, (t ^ n * Real.exp (-(lambda * t))) • S.realOperator t x := by
  have halg := S.iteratedDeriv_resolventFun_apply_eq_pow hb n hlambda x
  have hint := S.iteratedDeriv_resolventFun_apply_eq_resolventMoment hb n hlambda x
  rw [hint] at halg
  rw [S.resolventFun_of_lt hb hlambda] at halg
  have hsign : IsUnit ((-1 : ℝ) ^ n) := isUnit_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))
  have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hcancel : (n.factorial : ℝ) • (S.resolvent hb lambda hlambda ^ (n + 1)) x =
      S.resolventMoment n lambda x := by
    apply hsign.smul_left_cancel.mp
    simpa only [smul_smul] using halg.symm
  calc
    (S.resolvent hb lambda hlambda ^ (n + 1)) x
        = (n.factorial : ℝ)⁻¹ •
            ((n.factorial : ℝ) • (S.resolvent hb lambda hlambda ^ (n + 1)) x) := by
            rw [smul_smul, inv_mul_cancel₀ hfac, one_smul]
    _ = (1 / (n.factorial : ℝ)) • S.resolventMoment n lambda x := by
          rw [hcancel, one_div]
    _ = (1 / (n.factorial : ℝ)) •
        ∫ t in Set.Ioi 0, (t ^ n * Real.exp (-(lambda * t))) •
          S.realOperator t x := by rw [resolventMoment]

/-- Pointwise form of the sharp Hille--Yosida power bound. -/
theorem norm_resolvent_pow_succ_apply_le (hb : S.HasGrowthBound omega M) (n : ℕ)
    {lambda : ℝ} (hlambda : omega < lambda) (x : X) :
    ‖(S.resolvent hb lambda hlambda ^ (n + 1)) x‖ ≤
      M / (lambda - omega) ^ (n + 1) * ‖x‖ := by
  have ha : 0 < lambda - omega := sub_pos.mpr hlambda
  have hscalar : IntegrableOn
      (fun t : ℝ => M * ‖x‖ * (t ^ n * Real.exp (-((lambda - omega) * t))))
      (Set.Ioi 0) := by
    exact (integrableOn_pow_mul_exp_neg_mul_Ioi n ha).integrable.const_mul (M * ‖x‖)
  rw [S.resolvent_pow_succ_apply hb n hlambda x, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg n.factorial))]
  calc
    1 / (n.factorial : ℝ) *
          ‖∫ t in Set.Ioi 0, (t ^ n * Real.exp (-(lambda * t))) • S.realOperator t x‖
        ≤ 1 / (n.factorial : ℝ) *
            ∫ t in Set.Ioi 0,
              M * ‖x‖ * (t ^ n * Real.exp (-((lambda - omega) * t))) := by
          apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr (Nat.cast_nonneg _))
          apply MeasureTheory.norm_integral_le_of_norm_le hscalar.integrable
          apply (ae_restrict_mem measurableSet_Ioi).mono
          intro t ht
          exact S.norm_pow_mul_resolvent_integrand_le hb n lambda x ht.le
    _ = M / (lambda - omega) ^ (n + 1) * ‖x‖ := by
      rw [MeasureTheory.integral_const_mul,
        integral_pow_mul_exp_neg_mul_Ioi n ha]
      have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      field_simp

/-- The sharp iterated Hille--Yosida estimate for a semigroup with growth bound `(omega, M)`:
`norm (R(lambda)^n) <= M / (lambda - omega)^n`. -/
theorem resolvent_pow_norm_le (hb : S.HasGrowthBound omega M) (n : ℕ)
    {lambda : ℝ} (hlambda : omega < lambda) :
    ‖S.resolvent hb lambda hlambda ^ n‖ ≤ M / (lambda - omega) ^ n := by
  cases n with
  | zero => exact ContinuousLinearMap.norm_id_le.trans (by simpa using hb.one_le)
  | succ n =>
      apply ContinuousLinearMap.opNorm_le_bound
      · exact div_nonneg (by linarith [hb.one_le]) (pow_nonneg (by linarith) _)
      · intro x
        exact S.norm_resolvent_pow_succ_apply_le hb n hlambda x

/-- **Sharp Hille--Yosida power bound for the generator resolvent.** For a C₀-semigroup with
growth bound `(omega, M)` and `lambda > omega`,
`‖R(lambda, generator S) ^ n‖ ≤ M / (lambda - omega) ^ n`.

This is the necessity estimate in exactly the form consumed by the Hille--Yosida generation
theorem. -/
theorem norm_generator_resolvent_pow_le (hb : S.HasGrowthBound omega M)
    {lambda : ℝ} (hlambda : omega < lambda) (n : ℕ) :
    ‖LinearPMap.resolvent S.generator lambda ^ n‖ ≤ M / (lambda - omega) ^ n := by
  rw [S.generator_resolvent_eq hb hlambda]
  exact S.resolvent_pow_norm_le hb n hlambda

/-- The sharp Hille--Yosida derivative bound obtained from the resolvent power formula. -/
theorem norm_iteratedDeriv_resolventFun_le (hb : S.HasGrowthBound omega M) (n : ℕ)
    {lambda : ℝ} (hlambda : omega < lambda) :
    ‖iteratedDeriv n (S.resolventFun hb) lambda‖ ≤
      n.factorial * M / (lambda - omega) ^ (n + 1) := by
  have hscalar : ‖((-1 : ℝ) ^ n * n.factorial)‖ = (n.factorial : ℝ) := by simp
  rw [S.iteratedDeriv_resolventFun hb n hlambda, norm_smul, hscalar]
  calc
    (n.factorial : ℝ) * ‖S.resolventFun hb lambda ^ (n + 1)‖
        ≤ (n.factorial : ℝ) * (M / (lambda - omega) ^ (n + 1)) := by
          gcongr
          rw [S.resolventFun_of_lt hb hlambda]
          exact S.resolvent_pow_norm_le hb (n + 1) hlambda
    _ = n.factorial * M / (lambda - omega) ^ (n + 1) := by ring

end StronglyContinuousSemigroup

namespace ContractionSemigroup

/-- The pointwise power formula for a contraction-semigroup resolvent:
`R(lambda)^(n+1)x = 1/n! integral t^n exp(-lambda t) S(t)x dt`. -/
theorem resolvent_pow_succ_apply (S : ContractionSemigroup X) (n : ℕ) {lambda : ℝ}
    (hlambda : 0 < lambda) (x : X) :
    (S.resolvent lambda hlambda ^ (n + 1)) x =
      (1 / (n.factorial : ℝ)) •
        ∫ t in Set.Ioi 0, (t ^ n * Real.exp (-(lambda * t))) • S.realOperator t x := by
  rw [S.resolvent_eq_stronglyContinuousSemigroup_resolvent]
  exact S.toStronglyContinuousSemigroup.resolvent_pow_succ_apply
    S.hasGrowthBound n hlambda x

/-- The iterated Hille--Yosida bound for a contraction semigroup:
`‖R(lambda)^n‖ ≤ lambda⁻ⁿ`. -/
theorem resolvent_pow_norm_le (S : ContractionSemigroup X) (lambda : ℝ) (hlambda : 0 < lambda)
    (n : ℕ) :
    ‖S.resolvent lambda hlambda ^ n‖ ≤ (1 / lambda) ^ n := by
  have h := S.toStronglyContinuousSemigroup.resolvent_pow_norm_le S.hasGrowthBound n hlambda
  rw [← S.resolvent_eq_stronglyContinuousSemigroup_resolvent] at h
  simpa only [sub_zero, one_div_pow] using h

/-- The sharp Hille--Yosida power bound for the generator of a contraction semigroup:
`‖R(lambda, generator S) ^ n‖ ≤ lambda⁻ⁿ` for `lambda > 0`. -/
theorem norm_generator_resolvent_pow_le (S : ContractionSemigroup X) {lambda : ℝ}
    (hlambda : 0 < lambda) (n : ℕ) :
    ‖LinearPMap.resolvent S.toStronglyContinuousSemigroup.generator lambda ^ n‖
      ≤ (1 / lambda) ^ n := by
  have h := S.toStronglyContinuousSemigroup.norm_generator_resolvent_pow_le
    S.hasGrowthBound hlambda n
  simpa only [sub_zero, one_div_pow] using h

/-- The Hille--Yosida derivative bound in the contraction case. -/
theorem norm_iteratedDeriv_resolventFun_le (S : ContractionSemigroup X) (n : ℕ)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    ‖iteratedDeriv n S.resolventFun lambda‖ ≤ n.factorial * (1 / lambda) ^ (n + 1) := by
  have h := S.toStronglyContinuousSemigroup.norm_iteratedDeriv_resolventFun_le
    S.hasGrowthBound n hlambda
  rw [sub_zero] at h
  rw [S.resolventFun_eq]
  simpa only [one_mul, one_div, div_eq_mul_inv, mul_assoc, inv_pow] using h

/-- Pointwise form of the iterated contraction resolvent bound. -/
theorem norm_resolvent_pow_apply_le (S : ContractionSemigroup X) (lambda : ℝ)
    (hlambda : 0 < lambda) (n : ℕ) (x : X) :
    ‖(S.resolvent lambda hlambda ^ n) x‖ ≤ (1 / lambda) ^ n * ‖x‖ := by
  exact (S.resolvent lambda hlambda ^ n).le_of_opNorm_le
    (S.resolvent_pow_norm_le lambda hlambda n) x

/-- Every power of the scaled contraction resolvent `lambda R(lambda)` has norm at most one. -/
theorem norm_smul_resolvent_pow_le_one (S : ContractionSemigroup X) (lambda : ℝ)
    (hlambda : 0 < lambda) (n : ℕ) :
    ‖(lambda • S.resolvent lambda hlambda) ^ n‖ ≤ 1 := by
  rw [smul_pow, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlambda.le n)]
  calc
    lambda ^ n * ‖S.resolvent lambda hlambda ^ n‖
        ≤ lambda ^ n * (1 / lambda) ^ n := by
          gcongr
          exact S.resolvent_pow_norm_le lambda hlambda n
    _ = 1 := by rw [← mul_pow, one_div, mul_inv_cancel₀ hlambda.ne', one_pow]

/-- Pointwise form of the power bound for the scaled contraction resolvent. -/
theorem norm_smul_resolvent_pow_apply_le (S : ContractionSemigroup X) (lambda : ℝ)
    (hlambda : 0 < lambda) (n : ℕ) (x : X) :
    ‖((lambda • S.resolvent lambda hlambda) ^ n) x‖ ≤ ‖x‖ := by
  simpa using ((lambda • S.resolvent lambda hlambda) ^ n).le_of_opNorm_le
    (S.norm_smul_resolvent_pow_le_one lambda hlambda n) x

end ContractionSemigroup

end TauCeti.Semigroups

end
