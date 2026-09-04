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

## Main results

* `TauCeti.Probability.bind_gammaMeasure_poissonMeasure` — a Gamma mixture of Poisson laws is
  negative-binomial.
* `Real.gammaKernel_mul_exp_mul_pow_div_factorial` — the pointwise algebra it runs on: at a
  nonzero point, `c ^ r / Γ r * x ^ (r - 1) * exp (-(c * x))` times `exp (-x) * x ^ k / k !`
  collects into `c ^ r / (Γ r * k !) * (x ^ (r + k - 1) * exp (-((c + 1) * x)))`. The identity is
  algebraic — it carries no positivity hypotheses — and the mixture below supplies the
  probabilistic reading of its two sides.

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


/-- Collecting `c ^ r / Γ r * x ^ (r - 1) * exp (-(c * x))` against `exp (-x) * x ^ k / k !` at a
nonzero point: the two powers of `x` and the two exponentials each combine, leaving
`x ^ (r + k - 1) * exp (-((c + 1) * x))` under the constant `c ^ r / (Γ r * k !)`.

The identity is algebraic. Nothing here is assumed positive except that `x` is nonzero, so neither
side need be a probability density, and the surviving constant is `c ^ r / (Γ r * k !)` rather than
the `(c + 1) ^ (r + k) / Γ (r + k)` that would normalise the `x`-dependent factor into a gamma
kernel of shape `r + k` and rate `c + 1`. The gamma--Poisson mixture below instantiates the
identity pointwise at whatever rate its gamma law carries, and it is there that the two factors
are the densities their shapes suggest. -/
-- The factors are written out rather than as `gammaPDFReal` and `poissonPMFReal`: the former
-- carries an `if 0 ≤ x` guard that is not definitional at a bound variable, and the latter is
-- indexed by `ℝ≥0`, so either would cost the consumer a congruence step under its integral.
theorem _root_.Real.gammaKernel_mul_exp_mul_pow_div_factorial (c r : ℝ) (k : ℕ) {x : ℝ}
    (hx : x ≠ 0) :
    c ^ r / Real.Gamma r * x ^ (r - 1) * Real.exp (-(c * x)) *
        (Real.exp (-x) * x ^ k / k.factorial) =
      c ^ r / (Real.Gamma r * k.factorial) *
        (x ^ (r + (k : ℝ) - 1) * Real.exp (-((c + 1) * x))) := by
  have hxpow : x ^ (r - 1) * x ^ k = x ^ (r + (k : ℝ) - 1) := by
    -- `Real.rpow_add_natCast` fires only on an exponent already in the shape `y + (n : ℕ)`,
    -- so reassociate `r + k - 1` into `(r - 1) + k` before rewriting.
    rw [show r + (k : ℝ) - 1 = r - 1 + (k : ℕ) by ring,
      Real.rpow_add_natCast hx]
  have hexp : Real.exp (-(c * x)) * Real.exp (-x) = Real.exp (-((c + 1) * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    c ^ r / Real.Gamma r * x ^ (r - 1) * Real.exp (-(c * x)) *
        (Real.exp (-x) * x ^ k / k.factorial) =
        c ^ r / (Real.Gamma r * k.factorial) *
          ((x ^ (r - 1) * x ^ k) * (Real.exp (-(c * x)) * Real.exp (-x))) := by ring
    _ = _ := by rw [hxpow, hexp]

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
  have hcongr := fun x (hx : x ∈ Ioi (0 : ℝ)) =>
    Real.gammaKernel_mul_exp_mul_pow_div_factorial (p / (1 - p)) r k hx.ne'
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
