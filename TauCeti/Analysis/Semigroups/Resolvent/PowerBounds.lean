/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.Resolvent.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Integral formulas and power bounds for semigroup resolvents

This file proves the integral formula for powers of a Laplace-transform resolvent,

`R(lambda)^(n+1) x = 1 / n! * integral t in (0, infinity), t^n exp (-lambda t) S(t)x dt`,

and derives the sharp iterated Hille--Yosida estimate for a semigroup with growth bound
`norm (S(t)) <= M exp (omega t)`:

`norm (R(lambda)^n) <= M / (lambda - omega)^n` for `n >= 1`.

Only one factor of `M` occurs because the semigroup law collapses a product of operators to a
single orbit operator. This is sharper than applying submultiplicativity to the first-resolvent
bound, which would give `M^n / (lambda - omega)^n`.

For a contraction semigroup, this specializes to

`‖R(lambda)^n‖ ≤ lambda⁻ⁿ`.

The corresponding pointwise estimates and the bound for the scaled contraction resolvent
`lambda R(lambda)` are also recorded. The sharp general estimate is exactly the resolvent-power
hypothesis used in the Hille--Yosida generation theorem.

## References

Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Theorem II.3.5.
-/

public section

noncomputable section

open MeasureTheory
open scoped NNReal Topology

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

variable (S : StronglyContinuousSemigroup X) {omega M : ℝ}

/-- The elementary Gamma-integral evaluation used in the resolvent-power estimate. -/
private theorem integral_pow_mul_exp_neg_mul_Ioi (n : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ in Set.Ioi 0, t ^ n * Real.exp (-a * t) = n.factorial / a ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((n + 1 : ℕ) : ℝ)) (r := a) (by positivity) ha
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
    Real.Gamma_nat_eq_factorial] at h
  have hcast : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by norm_num
  rw [hcast, Real.rpow_natCast] at h
  have h' : ∫ t : ℝ in Set.Ioi 0, t ^ n * Real.exp (-a * t) =
      (1 / a) ^ (n + 1) * n.factorial := by
    rw [← h]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp
    rw [Real.rpow_natCast t n, neg_mul]
  rw [h', one_div, div_eq_mul_inv, inv_pow]
  ring

/-- The polynomially weighted Laplace integrand is integrable above the growth exponent. -/
theorem integrableOn_pow_mul_resolvent_integrand (hb : S.HasGrowthBound omega M) (n : ℕ)
    {lambda : ℝ} (hlambda : omega < lambda) (x : X) :
    IntegrableOn
      (fun t : ℝ => (t ^ n * Real.exp (-lambda * t)) • S.realOperator t x) (Set.Ioi 0) := by
  have hscalar : IntegrableOn
      (fun t : ℝ => t ^ n * Real.exp (-(lambda - omega) * t)) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (n : ℝ)) (b := lambda - omega)
      (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)) one_pos (by linarith)
    simpa only [Real.rpow_one, Real.rpow_natCast] using h
  apply Integrable.mono'
    (hscalar.integrable.const_mul (M * ‖x‖))
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.smul
    · fun_prop
    · have hcont : ContinuousOn (fun t => S.realOperator t x) (Set.Ici 0) :=
        fun t ht => S.realOperator_continuousWithinAt x t ht
      exact hcont.mono Set.Ioi_subset_Ici_self
  · apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg ht.le n)
      (Real.exp_pos _).le)]
    calc
      t ^ n * Real.exp (-lambda * t) * ‖S.realOperator t x‖
          ≤ t ^ n * Real.exp (-lambda * t) *
              (M * Real.exp (omega * t) * ‖x‖) := by
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg (pow_nonneg ht.le _) (Real.exp_pos _).le)
            exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (hb.bound t ht.le) (norm_nonneg x))
      _ = M * ‖x‖ * (t ^ n * Real.exp (-(lambda - omega) * t)) := by
            have hexponent : -(lambda - omega) * t = -lambda * t + omega * t := by ring
            rw [hexponent, Real.exp_add]
            ring

/-- The `n`-th weighted Laplace moment of a semigroup orbit. -/
private noncomputable def resolventMoment (S : StronglyContinuousSemigroup X) (n : ℕ)
    (lambda : ℝ) (x : X) : X :=
  ∫ t in Set.Ioi 0, (t ^ n * Real.exp (-lambda * t)) • S.realOperator t x

/-- Differentiating a weighted Laplace moment introduces the next power of time and a minus
sign. -/
private theorem hasDerivAt_resolventMoment (hb : S.HasGrowthBound omega M) (n : ℕ)
    {lambda : ℝ} (hlambda : omega < lambda) (x : X) :
    HasDerivAt (fun l => S.resolventMoment n l x) (-(S.resolventMoment (n + 1) lambda x))
      lambda := by
  let delta := (lambda - omega) / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  let U := Metric.ball lambda delta
  let F : ℝ → ℝ → X := fun l t =>
    (t ^ n * Real.exp (-l * t)) • S.realOperator t x
  let F' : ℝ → ℝ → X := fun l t =>
    -(t ^ (n + 1) * Real.exp (-l * t)) • S.realOperator t x
  let bound : ℝ → ℝ := fun t =>
    M * ‖x‖ * (t ^ (n + 1) * Real.exp (-delta * t))
  have hbound_int : Integrable bound (volume.restrict (Set.Ioi 0)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := ((n + 1 : ℕ) : ℝ)) (b := delta)
      (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg (n + 1))) one_pos hdelta
    have h' : IntegrableOn (fun t : ℝ => t ^ (n + 1) * Real.exp (-delta * t))
        (Set.Ioi 0) := by
      simpa only [Real.rpow_one, Real.rpow_natCast, neg_mul] using h
    exact h'.integrable.const_mul (M * ‖x‖)
  have hF_meas : ∀ᶠ l in 𝓝 lambda,
      AEStronglyMeasurable (F l) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards [] with l
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.smul
    · fun_prop
    · have hcont : ContinuousOn (fun t => S.realOperator t x) (Set.Ici 0) :=
        fun t ht => S.realOperator_continuousWithinAt x t ht
      exact hcont.mono Set.Ioi_subset_Ici_self
  have hF'_meas : AEStronglyMeasurable (F' lambda) (volume.restrict (Set.Ioi 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
    apply ContinuousOn.smul
    · fun_prop
    · have hcont : ContinuousOn (fun t => S.realOperator t x) (Set.Ici 0) :=
        fun t ht => S.realOperator_continuousWithinAt x t ht
      exact hcont.mono Set.Ioi_subset_Ici_self
  have hdom : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), ∀ l ∈ U, ‖F' l t‖ ≤ bound t := by
    apply (ae_restrict_mem measurableSet_Ioi).mono
    intro t ht l hl
    have hlower : omega + delta < l := by
      rw [Metric.mem_ball, Real.dist_eq] at hl
      have := neg_lt_of_abs_lt hl
      dsimp [delta] at *
      linarith
    dsimp only [F', bound]
    rw [norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (mul_nonneg (pow_nonneg ht.le (n + 1)) (Real.exp_pos _).le)]
    calc
      t ^ (n + 1) * Real.exp (-l * t) * ‖S.realOperator t x‖
          ≤ t ^ (n + 1) * Real.exp (-l * t) *
              (M * Real.exp (omega * t) * ‖x‖) := by
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg (pow_nonneg ht.le _) (Real.exp_pos _).le)
            exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right (hb.bound t ht.le) (norm_nonneg x))
      _ = M * ‖x‖ * (t ^ (n + 1) * Real.exp (-(l - omega) * t)) := by
            have hexponent : -(l - omega) * t = -l * t + omega * t := by ring
            rw [hexponent, Real.exp_add]
            ring
      _ ≤ M * ‖x‖ * (t ^ (n + 1) * Real.exp (-delta * t)) := by
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg (by linarith [hb.one_le]) (norm_nonneg x))
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg ht.le _)
            have hdl : delta ≤ l - omega := by linarith
            apply Real.exp_le_exp.mpr
            simpa only [neg_mul] using
              neg_le_neg (mul_le_mul_of_nonneg_right hdl ht.le)
  have hdiff : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), ∀ l ∈ U,
      HasDerivAt (F · t) (F' l t) l := by
    filter_upwards [] with t l hl
    dsimp only [F, F']
    have hinner : HasDerivAt (fun y : ℝ => -y * t) (-t) l := by
      have h := (hasDerivAt_id l).neg.mul_const t
      have h' : HasDerivAt (fun y : ℝ => -y * t) (-1 * t) l := by
        simpa only [Pi.neg_apply, id_eq] using h
      exact h'.congr_deriv (by ring)
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-y * t))
        (Real.exp (-l * t) * -t) l := by
      exact (Real.hasDerivAt_exp (-l * t)).comp l hinner
    have hscalar : HasDerivAt (fun y => t ^ n * Real.exp (-y * t))
        (-(t ^ (n + 1) * Real.exp (-l * t))) l := by
      exact (hexp.const_mul (t ^ n)).congr_deriv (by ring)
    exact hscalar.smul_const (S.realOperator t x)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0)) (F := F) (F' := F') (bound := bound)
    (Metric.ball_mem_nhds lambda hdelta) hF_meas
    (S.integrableOn_pow_mul_resolvent_integrand hb n hlambda x).integrable hF'_meas hdom
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

/-- Pointwise iterated derivatives of the resolvent are scalar multiples of resolvent powers. -/
private theorem iteratedDeriv_resolventFun_apply_eq_pow
    (hb : S.HasGrowthBound omega M) (n : ℕ) {lambda : ℝ} (hlambda : omega < lambda) (x : X) :
    iteratedDeriv n (fun l => S.resolventFun hb l x) lambda =
      ((-1 : ℝ) ^ n * n.factorial) • (S.resolventFun hb lambda ^ (n + 1)) x := by
  induction n generalizing lambda with
  | zero => simp
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n (fun l => S.resolventFun hb l x) =ᶠ[𝓝 lambda]
          (((-1 : ℝ) ^ n * n.factorial) •
            fun l => (S.resolventFun hb l ^ (n + 1)) x) := by
        filter_upwards [isOpen_Ioi.eventually_mem hlambda] with l hl
        simpa only [Pi.smul_apply] using ih hl
      have hpow := (S.hasDerivAt_resolventFun_pow hb hlambda (n + 1)).clm_apply
        (hasDerivAt_const lambda x)
      have hpow' : HasDerivAt (fun y => (S.resolventFun hb y ^ (n + 1)) x)
          (-((n + 1) • (S.resolventFun hb lambda ^ (n + 1 + 1)) x)) lambda :=
        hpow.congr_deriv (by simp; module)
      have hderiv := hpow'.const_smul ((-1 : ℝ) ^ n * n.factorial)
      rw [heq.deriv_eq, hderiv.deriv]
      push_cast [Nat.factorial_succ]
      rw [pow_succ]
      module

/-- The pointwise power formula for a semigroup resolvent:
`R(lambda)^(n+1)x = 1/n! integral t^n exp(-lambda t) S(t)x dt`. -/
theorem resolvent_pow_succ_apply (hb : S.HasGrowthBound omega M) (n : ℕ) {lambda : ℝ}
    (hlambda : omega < lambda) (x : X) :
    (S.resolvent hb lambda hlambda ^ (n + 1)) x =
      (1 / (n.factorial : ℝ)) •
        ∫ t in Set.Ioi 0, (t ^ n * Real.exp (-lambda * t)) • S.realOperator t x := by
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
    _ = _ := rfl

/-- Pointwise form of the sharp Hille--Yosida power bound. -/
theorem norm_resolvent_pow_succ_apply_le (hb : S.HasGrowthBound omega M) (n : ℕ)
    {lambda : ℝ} (hlambda : omega < lambda) (x : X) :
    ‖(S.resolvent hb lambda hlambda ^ (n + 1)) x‖ ≤
      M / (lambda - omega) ^ (n + 1) * ‖x‖ := by
  have ha : 0 < lambda - omega := sub_pos.mpr hlambda
  have hscalar : IntegrableOn
      (fun t : ℝ => M * ‖x‖ * (t ^ n * Real.exp (-(lambda - omega) * t)))
      (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := (n : ℝ)) (b := lambda - omega)
      (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)) one_pos ha
    have h' : IntegrableOn
        (fun t : ℝ => t ^ n * Real.exp (-(lambda - omega) * t)) (Set.Ioi 0) := by
      simpa only [Real.rpow_one, Real.rpow_natCast] using h
    exact h'.integrable.const_mul (M * ‖x‖)
  rw [S.resolvent_pow_succ_apply hb n hlambda x, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (one_div_nonneg.mpr (Nat.cast_nonneg n.factorial))]
  calc
    1 / (n.factorial : ℝ) *
          ‖∫ t in Set.Ioi 0, (t ^ n * Real.exp (-lambda * t)) • S.realOperator t x‖
        ≤ 1 / (n.factorial : ℝ) *
            ∫ t in Set.Ioi 0,
              M * ‖x‖ * (t ^ n * Real.exp (-(lambda - omega) * t)) := by
          apply mul_le_mul_of_nonneg_left _ (one_div_nonneg.mpr (Nat.cast_nonneg _))
          apply MeasureTheory.norm_integral_le_of_norm_le hscalar.integrable
          apply (ae_restrict_mem measurableSet_Ioi).mono
          intro t ht
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (pow_nonneg ht.le n) (Real.exp_pos _).le)]
          calc
            t ^ n * Real.exp (-lambda * t) * ‖S.realOperator t x‖
                ≤ t ^ n * Real.exp (-lambda * t) *
                    (M * Real.exp (omega * t) * ‖x‖) := by
                  apply mul_le_mul_of_nonneg_left _
                    (mul_nonneg (pow_nonneg ht.le _) (Real.exp_pos _).le)
                  exact (ContinuousLinearMap.le_opNorm _ _).trans
                    (mul_le_mul_of_nonneg_right (hb.bound t ht.le) (norm_nonneg x))
            _ = M * ‖x‖ * (t ^ n * Real.exp (-(lambda - omega) * t)) := by
                  have hexponent : -(lambda - omega) * t = -lambda * t + omega * t := by ring
                  rw [hexponent, Real.exp_add]
                  ring
    _ = M / (lambda - omega) ^ (n + 1) * ‖x‖ := by
      rw [MeasureTheory.integral_const_mul,
        integral_pow_mul_exp_neg_mul_Ioi n ha]
      have hfac : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
      field_simp

/-- The sharp iterated Hille--Yosida estimate for a semigroup with growth bound `(omega, M)`:
`norm (R(lambda)^n) <= M / (lambda - omega)^n` for every positive `n`. -/
theorem resolvent_pow_norm_le (hb : S.HasGrowthBound omega M) {n : ℕ} (hn : 1 ≤ n)
    {lambda : ℝ} (hlambda : omega < lambda) :
    ‖S.resolvent hb lambda hlambda ^ n‖ ≤ M / (lambda - omega) ^ n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply ContinuousLinearMap.opNorm_le_bound
  · exact div_nonneg (by linarith [hb.one_le]) (pow_nonneg (by linarith) _)
  · intro x
    exact S.norm_resolvent_pow_succ_apply_le hb n hlambda x

end StronglyContinuousSemigroup

namespace ContractionSemigroup

/-- The iterated Hille--Yosida bound for a contraction semigroup:
`‖R(lambda)^n‖ ≤ lambda⁻ⁿ`. -/
theorem resolvent_pow_norm_le (S : ContractionSemigroup X) (lambda : ℝ) (hlambda : 0 < lambda)
    (n : ℕ) :
    ‖S.resolvent lambda hlambda ^ n‖ ≤ (1 / lambda) ^ n := by
  cases n with
  | zero => exact ContinuousLinearMap.norm_id_le
  | succ n =>
      have h := S.toStronglyContinuousSemigroup.resolvent_pow_norm_le S.hasGrowthBound
        (n := n + 1) n.succ_pos hlambda
      have heq : S.toStronglyContinuousSemigroup.resolvent S.hasGrowthBound lambda hlambda =
          S.resolvent lambda hlambda := by
        ext x
        rw [StronglyContinuousSemigroup.resolvent_apply, S.resolvent_apply]
      rw [heq] at h
      simpa only [sub_zero, one_div_pow] using h

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
