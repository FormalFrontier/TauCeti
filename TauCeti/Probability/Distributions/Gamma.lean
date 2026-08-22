/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Probability.Distributions.PDFInstances

/-!
# Elementary theory of the gamma distribution

This file develops the elementary moment theory of Mathlib's gamma distribution. For a positive
shape `a` and a positive rate `r` it computes every natural raw moment, the mean and the variance,
the exact set of rates at which an exponential moment exists, and the moment- and
cumulant-generating functions on that set. It also identifies the law of a positive rescaling: only
the rate moves, and it moves by the scaling factor.

The moment and transform computations go through the same two reductions. The measure
`gammaMeasure a r` is
`volume.withDensity` of a density carried by `[0, ∞)`, so an integral against it is a set integral
of the weighted integrand over `(0, ∞)`, and integrability against it is integrability of that same
weighted integrand over `(0, ∞)`. Raw moments and exponential moments then both reduce to Euler's
integral through `Real.integral_rpow_mul_exp_neg_mul_Ioi`, whose shape
`x ^ (s - 1) * exp (-(b * x))` they match after collecting exponents: a factor `x ^ n` shifts the
shape from `a` to `a + n`, and a factor `exp (t * x)` shifts the rate from `r` to `r - t`. The
second shift explains the exponential moment domain: it is exactly the half-line on which the
shifted rate is still positive.

## Main results

* `TauCeti.integral_pow_gammaMeasure` — the natural raw moments, `Γ (a + n) / (Γ a * r ^ n)`, with
  `TauCeti.integral_id_gammaMeasure` and `TauCeti.integral_sq_gammaMeasure` as the first two cases;
* `TauCeti.variance_id_gammaMeasure` — the variance is `a / r ^ 2`;
* `TauCeti.integrable_exp_mul_id_gammaMeasure` and
  `TauCeti.not_integrable_exp_mul_id_gammaMeasure` —
  the exponential moment of rate `t` exists exactly when `t < r`, recorded as an equality of sets
  in `TauCeti.integrableExpSet_id_gammaMeasure`;
* `TauCeti.mgf_id_gammaMeasure` — the moment-generating function is `(1 - t / r) ^ (-a)` there;
* `TauCeti.cgf_id_gammaMeasure` — the cumulant-generating function is `-a * log (1 - t / r)`
  there, the real logarithm of the previous formula;
* `TauCeti.gammaMeasure_map_const_mul` — scaling by `c > 0` sends the rate `r` to `r / c`.

## References

* Tau Ceti roadmap, `StandardDistributions`, Layer 1, "Gamma".
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, ch. 17.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Real Set

variable {a r : ℝ}

/-! ### Reduction to the positive half-line -/

/-- On the positive half-line the gamma density is given by its closed formula. -/
private lemma gammaPDFReal_of_pos {x : ℝ} (hx : 0 < x) :
    gammaPDFReal a r x = r ^ a / Real.Gamma a * x ^ (a - 1) * exp (-(r * x)) := by
  rw [gammaPDFReal, ite_eq_left hx.le]

/-- An integral against the gamma law is the set integral of the weighted integrand over
`(0, ∞)`. -/
private lemma integral_gammaMeasure_eq (ha : 0 < a) (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ x, f x ∂gammaMeasure a r =
      ∫ x in Ioi 0, r ^ a / Real.Gamma a * x ^ (a - 1) * exp (-(r * x)) * f x := by
  have hcompl : ∀ x ∉ Ici (0 : ℝ), gammaPDFReal a r x * f x = 0 := by
    intro x hx
    rw [gammaPDFReal, ite_eq_right (by simpa using hx), zero_mul]
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul
    (Probability.measurable_gammaPDF a r) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) f]
  simp_rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl, integral_Ici_eq_integral_Ioi]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ by rw [gammaPDFReal_of_pos hx]

/-- Integrability against the gamma law is integrability of the weighted integrand over
`(0, ∞)`. -/
private lemma integrable_gammaMeasure_iff (ha : 0 < a) (hr : 0 < r) (f : ℝ → ℝ) :
    Integrable f (gammaMeasure a r) ↔
      IntegrableOn
        (fun x ↦ r ^ a / Real.Gamma a * x ^ (a - 1) * exp (-(r * x)) * f x) (Ioi 0) := by
  have hpos : ∀ x ∈ Ioi (0 : ℝ), f x * gammaPDFReal a r x =
      r ^ a / Real.Gamma a * x ^ (a - 1) * exp (-(r * x)) * f x := fun x hx ↦ by
    rw [gammaPDFReal_of_pos hx, mul_comm]
  have hneg : IntegrableOn (fun x ↦ f x * gammaPDFReal a r x) (Iio 0) := by
    refine integrableOn_zero.congr_fun (fun x hx ↦ ?_) measurableSet_Iio
    rw [gammaPDFReal, ite_eq_right (not_le.mpr hx), mul_zero]
  rw [gammaMeasure, integrable_withDensity_iff
    (Probability.measurable_gammaPDF a r) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)]
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨fun h ↦ h.2.congr_fun hpos measurableSet_Ioi,
    fun h ↦ ⟨hneg, h.congr_fun (fun x hx ↦ (hpos x hx).symm) measurableSet_Ioi⟩⟩

/-- A constant multiple of Euler's Gamma integral, in quotient form. -/
private lemma integral_const_mul_gammaKernel (C s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    ∫ x in Ioi 0, C * (x ^ (s - 1) * exp (-(b * x))) = C * Real.Gamma s / b ^ s := by
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hs hb, one_div,
    Real.inv_rpow hb.le, div_eq_mul_inv]
  ring

/-! ### Raw moments, mean and variance -/

/-- The `n`th raw moment of a gamma law with positive shape and rate. -/
@[simp]
theorem integral_pow_gammaMeasure (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    ∫ x, x ^ n ∂gammaMeasure a r = Real.Gamma (a + n) / (Real.Gamma a * r ^ n) := by
  have han : 0 < a + (n : ℝ) := by positivity
  have hcongr : ∀ x ∈ Ioi (0 : ℝ),
      r ^ a / Real.Gamma a * x ^ (a - 1) * exp (-(r * x)) * x ^ n =
        r ^ a / Real.Gamma a * (x ^ (a + (n : ℝ) - 1) * exp (-(r * x))) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hrpow : x ^ (a - 1) * x ^ n = x ^ (a + (n : ℝ) - 1) := by
      rw [← Real.rpow_natCast x n, ← Real.rpow_add hx0]
      congr 1
      ring
    calc r ^ a / Real.Gamma a * x ^ (a - 1) * exp (-(r * x)) * x ^ n
        = r ^ a / Real.Gamma a * (x ^ (a - 1) * x ^ n * exp (-(r * x))) := by ring
      _ = r ^ a / Real.Gamma a * (x ^ (a + (n : ℝ) - 1) * exp (-(r * x))) := by rw [hrpow]
  have hGa := (Real.Gamma_pos_of_pos ha).ne'
  have hra := (Real.rpow_pos_of_pos hr a).ne'
  have hrn := (pow_pos hr n).ne'
  rw [integral_gammaMeasure_eq ha hr, setIntegral_congr_fun measurableSet_Ioi hcongr,
    integral_const_mul_gammaKernel _ _ _ han hr, Real.rpow_add hr, Real.rpow_natCast]
  field_simp

/-- The mean of a gamma law with positive shape and rate is `a / r`. -/
@[simp]
theorem integral_id_gammaMeasure (ha : 0 < a) (hr : 0 < r) :
    ∫ x, x ∂gammaMeasure a r = a / r := by
  have h := integral_pow_gammaMeasure ha hr 1
  simp only [pow_one, Nat.cast_one] at h
  rw [h, Real.Gamma_add_one ha.ne']
  field_simp [(Real.Gamma_pos_of_pos ha).ne']

/-- The second raw moment of a gamma law with positive shape and rate is `a * (a + 1) / r ^ 2`. -/
@[simp high]
theorem integral_sq_gammaMeasure (ha : 0 < a) (hr : 0 < r) :
    ∫ x, x ^ 2 ∂gammaMeasure a r = a * (a + 1) / r ^ 2 := by
  have hGa := (Real.Gamma_pos_of_pos ha).ne'
  have h := integral_pow_gammaMeasure ha hr 2
  have hGamma_arg : a + 2 = a + 1 + 1 := by ring
  norm_num only [Nat.cast_ofNat] at h
  rw [h, hGamma_arg, Real.Gamma_add_one (by positivity : a + 1 ≠ 0),
    Real.Gamma_add_one ha.ne']
  field_simp

/-! ### Exponential moments -/

/-- Multiplying the gamma integrand by `exp (t * x)` shifts the rate from `r` to `r - t`. -/
private lemma gammaWeight_mul_exp (a r t x : ℝ) :
    r ^ a / Real.Gamma a * x ^ (a - 1) * exp (-(r * x)) * exp (t * x) =
      r ^ a / Real.Gamma a * (x ^ (a - 1) * exp (-((r - t) * x))) := by
  have hexponent : -(r * x) + t * x = -((r - t) * x) := by ring
  rw [mul_assoc, ← Real.exp_add, hexponent]
  ring

/-- Below the rate of a gamma law, its exponential moments exist. -/
theorem integrable_exp_mul_id_gammaMeasure (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : t < r) :
    Integrable (fun x ↦ exp (t * x)) (gammaMeasure a r) := by
  rw [integrable_gammaMeasure_iff ha hr]
  refine IntegrableOn.congr_fun ?_ (fun x _ ↦ (gammaWeight_mul_exp a r t x).symm)
    measurableSet_Ioi
  have h : IntegrableOn (fun x : ℝ ↦ x ^ (a - 1) * exp (-((r - t) * x))) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := a - 1) (b := r - t)
      (by linarith : (-1 : ℝ) < a - 1) one_pos (sub_pos.mpr ht)
  exact h.const_mul _

/-- Every natural power is integrable under a gamma law with positive shape and rate. -/
theorem integrable_pow_gammaMeasure (ha : 0 < a) (hr : 0 < r) (n : ℕ) :
    Integrable (fun x ↦ x ^ n) (gammaMeasure a r) :=
  integrable_pow_of_integrable_exp_mul (by positivity : (r / 2 : ℝ) ≠ 0)
    (integrable_exp_mul_id_gammaMeasure ha hr (by linarith : r / 2 < r))
    (integrable_exp_mul_id_gammaMeasure ha hr (by linarith : -(r / 2) < r)) n

/-- The identity function belongs to `L²` of a gamma law with positive shape and rate. -/
theorem memLp_id_gammaMeasure (ha : 0 < a) (hr : 0 < r) :
    MemLp id 2 (gammaMeasure a r) :=
  (memLp_two_iff_integrable_sq measurable_id'.aestronglyMeasurable).2
    (by simpa using integrable_pow_gammaMeasure ha hr 2)

/-- At or above the rate of a gamma law, its exponential moments do not exist. -/
theorem not_integrable_exp_mul_id_gammaMeasure (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : r ≤ t) :
    ¬ Integrable (fun x ↦ exp (t * x)) (gammaMeasure a r) := by
  have hGa := Real.Gamma_pos_of_pos ha
  have hC : (0 : ℝ) < r ^ a / Real.Gamma a := by positivity
  rw [integrable_gammaMeasure_iff ha hr]
  intro h
  have hmono : IntegrableOn (fun x : ℝ ↦ r ^ a / Real.Gamma a * x ^ (a - 1)) (Ioi 1) := by
    have h1 : IntegrableOn
        (fun x ↦ r ^ a / Real.Gamma a * x ^ (a - 1) * exp (-(r * x)) * exp (t * x)) (Ioi 1) :=
      h.mono_set (Ioi_subset_Ioi zero_le_one)
    refine Integrable.mono h1 (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx1 : (1 : ℝ) < x := hx
    have hxa : (0 : ℝ) < x ^ (a - 1) := Real.rpow_pos_of_pos (by linarith) _
    have hexp : (1 : ℝ) ≤ exp (-(r * x)) * exp (t * x) := by
      rw [← Real.exp_add]
      simpa using Real.exp_le_exp.mpr (by nlinarith : (0 : ℝ) ≤ -(r * x) + t * x)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    calc r ^ a / Real.Gamma a * x ^ (a - 1)
        = r ^ a / Real.Gamma a * x ^ (a - 1) * 1 := by ring
      _ ≤ r ^ a / Real.Gamma a * x ^ (a - 1) * (exp (-(r * x)) * exp (t * x)) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = r ^ a / Real.Gamma a * x ^ (a - 1) * exp (-(r * x)) * exp (t * x) := by ring
  have hfinal : IntegrableOn (fun x : ℝ ↦ x ^ (a - 1)) (Ioi 1) := by
    have hscaled := hmono.const_mul (r ^ a / Real.Gamma a)⁻¹
    refine IntegrableOn.congr_fun hscaled (fun x _ ↦ ?_) measurableSet_Ioi
    rw [inv_mul_cancel_left₀ hC.ne']
  rw [integrableOn_Ioi_rpow_iff one_pos] at hfinal
  linarith

/-- The exponential moments of a gamma law of rate `r` are exactly those of rate `t < r`. -/
@[simp]
theorem integrableExpSet_id_gammaMeasure (ha : 0 < a) (hr : 0 < r) :
    integrableExpSet id (gammaMeasure a r) = Iio r := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, id_eq, mem_Iio]
  refine ⟨fun h ↦ ?_, integrable_exp_mul_id_gammaMeasure ha hr⟩
  by_contra hc
  exact not_integrable_exp_mul_id_gammaMeasure ha hr (not_lt.mp hc) h

/-- The moment-generating function of a gamma law on the half-line where its exponential moment
is integrable, namely `t < r`. -/
@[simp]
theorem mgf_id_gammaMeasure (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : t < r) :
    mgf id (gammaMeasure a r) t = (1 - t / r) ^ (-a) := by
  have hrt : 0 < r - t := sub_pos.mpr ht
  have hGa := (Real.Gamma_pos_of_pos ha).ne'
  have hra := (Real.rpow_pos_of_pos hr a).ne'
  have hrta := (Real.rpow_pos_of_pos hrt a).ne'
  have hone_sub : (1 : ℝ) - t / r = (r - t) / r := by field_simp
  rw [mgf]
  simp only [id_eq]
  rw [integral_gammaMeasure_eq ha hr,
    setIntegral_congr_fun measurableSet_Ioi (fun x _ ↦ gammaWeight_mul_exp a r t x),
    integral_const_mul_gammaKernel _ _ _ ha hrt, hone_sub,
    Real.rpow_neg (by positivity), Real.div_rpow hrt.le hr.le]
  field_simp

/-- The cumulant-generating function of a gamma law on the half-line where its exponential moment
is integrable, namely `t < r`. It is the real logarithm of `TauCeti.mgf_id_gammaMeasure`. -/
@[simp]
theorem cgf_id_gammaMeasure (ha : 0 < a) (hr : 0 < r) {t : ℝ} (ht : t < r) :
    cgf id (gammaMeasure a r) t = -a * Real.log (1 - t / r) := by
  have h : (0 : ℝ) < 1 - t / r := by
    rw [sub_pos, div_lt_one hr]
    exact ht
  rw [cgf, mgf_id_gammaMeasure ha hr ht, Real.log_rpow h]

/-- The variance of a gamma law with positive shape and rate is `a / r ^ 2`. -/
@[simp]
theorem variance_id_gammaMeasure (ha : 0 < a) (hr : 0 < r) :
    variance id (gammaMeasure a r) = a / r ^ 2 := by
  have _ : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  rw [variance_eq_sub (memLp_id_gammaMeasure ha hr)]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_gammaMeasure ha hr, integral_id_gammaMeasure ha hr]
  field_simp
  ring

/-! ### Scaling -/

/-- Scaling a gamma density by `c > 0` divides its rate by `c`: the two densities differ by the
Jacobian factor `c`. -/
private lemma ofReal_mul_gammaPDF_const_mul (ha : 0 < a) (hr : 0 < r) {c : ℝ} (hc : 0 < c)
    (x : ℝ) : ENNReal.ofReal c * gammaPDF a (r / c) (c * x) = gammaPDF a r x := by
  rcases le_or_gt 0 x with hx | hx
  · rw [gammaPDF_of_nonneg hx, gammaPDF_of_nonneg (by positivity : (0 : ℝ) ≤ c * x),
      ← ENNReal.ofReal_mul hc.le]
    congr 1
    have hca := (Real.rpow_pos_of_pos hc a).ne'
    have hGa := (Real.Gamma_pos_of_pos ha).ne'
    have hrate : r / c * (c * x) = r * x := by field_simp
    rw [Real.mul_rpow hc.le hx, Real.div_rpow hr.le hc.le,
      hrate, Real.rpow_sub hc a 1, Real.rpow_one]
    field_simp
  · rw [gammaPDF_of_neg hx, gammaPDF_of_neg (mul_neg_of_pos_of_neg hc hx), mul_zero]

/-- Scaling a gamma variable by `c > 0` divides its rate by `c`. -/
@[simp]
theorem gammaMeasure_map_const_mul (ha : 0 < a) (hr : 0 < r) {c : ℝ} (hc : 0 < c) :
    (gammaMeasure a r).map (c * ·) = gammaMeasure a (r / c) := by
  have hT : Measurable fun x : ℝ ↦ c * x := measurable_const_mul c
  ext s hs
  rw [Measure.map_apply hT hs, gammaMeasure, gammaMeasure, withDensity_apply _ (hT hs),
    withDensity_apply _ hs]
  calc ∫⁻ x in (c * ·) ⁻¹' s, gammaPDF a r x
      = ∫⁻ x in (c * ·) ⁻¹' s, ENNReal.ofReal c * gammaPDF a (r / c) (c * x) := by
        simp_rw [ofReal_mul_gammaPDF_const_mul ha hr hc]
    _ = ENNReal.ofReal c * ∫⁻ x in (c * ·) ⁻¹' s, gammaPDF a (r / c) (c * x) :=
        lintegral_const_mul _ ((Probability.measurable_gammaPDF a (r / c)).comp hT)
    _ = ENNReal.ofReal c * ∫⁻ y in s, gammaPDF a (r / c) y ∂(volume.map (c * ·)) := by
        rw [setLIntegral_map hs (Probability.measurable_gammaPDF a (r / c)) hT]
    _ = ∫⁻ y in s, gammaPDF a (r / c) y := by
        rw [Real.map_volume_mul_left hc.ne', setLIntegral_smul_measure, smul_eq_mul, ← mul_assoc,
          ← ENNReal.ofReal_mul hc.le, abs_of_pos (inv_pos.mpr hc), mul_inv_cancel₀ hc.ne',
          ENNReal.ofReal_one, one_mul]

end TauCeti
