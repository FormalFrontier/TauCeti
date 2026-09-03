/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gamma.Basic
public import TauCeti.Probability.Distributions.NegativeBinomial
public import Mathlib.Probability.Distributions.Poisson.Basic
import TauCeti.Probability.Distributions.Measurability

/-!
# Gamma mixtures of Poisson distributions

Mixing a Poisson rate against a Gamma law produces a negative-binomial distribution. More
precisely, a Gamma mixing law of shape `r` and rate `p / (1 - p)` gives the negative-binomial law
of shape `r` and success probability `p`.

The proof compares singleton masses. The Poisson mass contributes `exp (-x) * x ^ k / k!` to
the Gamma density, changing its rate from `p / (1 - p)` to `1 / (1 - p)` and its shape from `r`
to `r + k`. Euler's Gamma integral then gives exactly the negative-binomial mass.

## Main result

* `TauCeti.Probability.bind_gammaMeasure_poissonMeasure` — a Gamma mixture of Poisson laws is
  negative-binomial.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley
  (2005), ch. 6.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti

namespace Probability

private lemma integral_poissonMass_gammaMeasure {r p : ℝ} (hr : 0 < r) (hp : 0 < p)
    (hp1 : p < 1) (k : ℕ) :
    ∫ x, Real.exp (-x) * x ^ k / k.factorial ∂gammaMeasure r (p / (1 - p)) =
      negativeBinomialWeightReal r p k := by
  have h1mp : 0 < 1 - p := sub_pos.mpr hp1
  have hrate : 0 < p / (1 - p) := div_pos hp h1mp
  have hshape : 0 < r + (k : ℝ) := by positivity
  have hcombined : p / (1 - p) + 1 = (1 - p)⁻¹ := by
    field_simp [h1mp.ne']
    ring
  -- Collect the Poisson mass with the Gamma density on its positive support.
  rw [TauCeti.integral_gammaMeasure_eq hr hrate]
  -- In this real-valued specialization, scalar multiplication is ordinary multiplication.
  change (∫ x in Ioi 0,
    ((p / (1 - p)) ^ r / Real.Gamma r * x ^ (r - 1) *
      Real.exp (-(p / (1 - p) * x))) *
        (Real.exp (-x) * x ^ k / k.factorial)) = _
  have hcongr : ∀ x ∈ Ioi (0 : ℝ),
      (p / (1 - p)) ^ r / Real.Gamma r * x ^ (r - 1) *
          Real.exp (-(p / (1 - p) * x)) * (Real.exp (-x) * x ^ k / k.factorial) =
        ((p / (1 - p)) ^ r / (Real.Gamma r * k.factorial)) *
          (x ^ (r + (k : ℝ) - 1) *
            Real.exp (-((p / (1 - p) + 1) * x))) := by
    intro x hx
    have hxpow : x ^ (r - 1) * x ^ k = x ^ (r + (k : ℝ) - 1) := by
      rw [← Real.rpow_natCast x k, ← Real.rpow_add hx]
      congr 1
      ring
    have hexp : Real.exp (-(p / (1 - p) * x)) * Real.exp (-x) =
        Real.exp (-((p / (1 - p) + 1) * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      (p / (1 - p)) ^ r / Real.Gamma r * x ^ (r - 1) *
            Real.exp (-(p / (1 - p) * x)) *
          (Real.exp (-x) * x ^ k / k.factorial) =
          ((p / (1 - p)) ^ r / (Real.Gamma r * k.factorial)) *
            ((x ^ (r - 1) * x ^ k) *
              (Real.exp (-(p / (1 - p) * x)) * Real.exp (-x))) := by ring
      _ = _ := by rw [hxpow, hexp]
  -- Euler's Gamma integral evaluates the kernel with shifted shape `r + k`.
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hshape (by positivity : 0 < p / (1 - p) + 1),
    hcombined]
  -- Normalize the remaining constants to the defining negative-binomial mass.
  rw [negativeBinomialWeightReal_eq_gamma hr.ne' k]
  have hrpow_div : (p / (1 - p)) ^ r = p ^ r / (1 - p) ^ r := by
    exact Real.div_rpow hp.le h1mp.le r
  have hrpow_add : (1 / (1 - p)⁻¹) ^ (r + (k : ℝ)) =
      (1 - p) ^ r * (1 - p) ^ k := by
    rw [one_div, inv_inv, Real.rpow_add h1mp, Real.rpow_natCast]
  rw [hrpow_div, hrpow_add]
  have hGamma : Real.Gamma r ≠ 0 := (Real.Gamma_pos_of_pos hr).ne'
  have hfac : (k.factorial : ℝ) ≠ 0 := by positivity
  have hpow : (1 - p) ^ r ≠ 0 := (Real.rpow_pos_of_pos h1mp r).ne'
  have hGammaArg : r + (k : ℝ) = (k : ℝ) + r := by ring
  rw [hGammaArg]
  field_simp
  exact (Real.rpow_eq_pow p r).symm

/-- **A Gamma mixture of Poisson laws is negative-binomial.**

If the Poisson rate is mixed according to the Gamma law of shape `r` and rate
`p / (1 - p)`, the resulting count law is negative-binomial with shape `r` and success
probability `p`. -/
@[simp]
theorem bind_gammaMeasure_poissonMeasure {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hp1 : p < 1) :
    (gammaMeasure r (p / (1 - p))).bind
        (fun lam => poissonMeasure (Real.toNNReal lam)) =
      negativeBinomialMeasure r p := by
  have hrate : 0 < p / (1 - p) := div_pos hp (sub_pos.mpr hp1)
  have hkernelMeas : Measurable (fun lam : ℝ => poissonMeasure (Real.toNNReal lam)) := by
    fun_prop
  have hkernel : AEMeasurable (fun lam : ℝ => poissonMeasure (Real.toNNReal lam))
      (gammaMeasure r (p / (1 - p))) := hkernelMeas.aemeasurable
  let _ : IsProbabilityMeasure (gammaMeasure r (p / (1 - p))) :=
    isProbabilityMeasure_gammaMeasure hr hrate
  let _ : IsProbabilityMeasure
      ((gammaMeasure r (p / (1 - p))).bind
        (fun lam => poissonMeasure (Real.toNNReal lam))) :=
    isProbabilityMeasure_bind hkernel (ae_of_all _ fun _ => inferInstance)
  let _ : IsProbabilityMeasure (negativeBinomialMeasure r p) :=
    isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1.le
  refine MeasureTheory.ext_iff_measureReal_singleton.mpr fun k => ?_
  rw [negativeBinomialMeasure_real_singleton hr.le hp hp1.le, measureReal_def,
    Measure.bind_apply (measurableSet_singleton k) hkernel]
  have hmassMeas : AEMeasurable
      (fun lam : ℝ => poissonMeasure (Real.toNNReal lam) {k})
      (gammaMeasure r (p / (1 - p))) :=
    ((Measure.measurable_coe (measurableSet_singleton k)).comp hkernelMeas).aemeasurable
  rw [← integral_toReal hmassMeas (ae_of_all _ fun lam => measure_lt_top _ _)]
  simp_rw [← measureReal_def, poissonMeasure_real_singleton]
  rw [integral_congr_ae (by
    filter_upwards [TauCeti.ae_pos_gammaMeasure r (p / (1 - p))] with lam hlam
    rw [Real.coe_toNNReal lam hlam.le])]
  exact integral_poissonMass_gammaMeasure hr hp hp1 k

end Probability

end TauCeti
