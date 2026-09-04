/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import TauCeti.Probability.Distributions.Weibull.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Probability.Distributions.Exponential

/-!
# Exponential moments of the Weibull distribution

The exponential moments of a Weibull law exhibit three different regimes according to its shape
`k`. They are finite at every real argument when `1 < k`, finite precisely below the reciprocal
scale when `k = 1`, and finite precisely at nonpositive arguments when `0 < k < 1`.

This file proves that trichotomy. The superlinear case follows by comparison with a Weibull tail
whose exponent has been halved; the sublinear case follows because every positive exponential
eventually dominates the density's stretched-exponential decay. At shape one, identifying the
Weibull law with an exponential law also gives the mgf `(1 - lam * t)⁻¹` and cgf
`-log (1 - lam * t)`.

## Main results

* `TauCeti.Probability.integrable_exp_mul_id_weibullMeasure_of_nonpos`: every nonpositive
  exponential rate is integrable;
* `TauCeti.Probability.integrable_exp_mul_id_weibullMeasure_of_one_lt` and
  `TauCeti.Probability.not_integrable_exp_mul_id_weibullMeasure_of_lt_one`: the one-sided
  statements in the superlinear and sublinear regimes;
* `TauCeti.Probability.integrable_exp_mul_id_weibullMeasure_iff_of_lt_one` and
  `TauCeti.Probability.integrable_exp_mul_id_weibullMeasure_one_iff`: the exact integrability
  criteria in the sublinear and shape-one regimes;
* `TauCeti.Probability.integrableExpSet_id_weibullMeasure`: the complete three-regime
  exponential-integrability trichotomy;
* `TauCeti.Probability.integrableExpSet_id_weibullMeasure_of_one_lt` and
  `TauCeti.Probability.integrableExpSet_id_weibullMeasure_of_lt_one`: the superlinear and
  sublinear domains;
* `TauCeti.Probability.integrableExpSet_id_weibullMeasure_one`: the shape-one domain is
  `(-∞, lam⁻¹)`;
* `TauCeti.Probability.mgf_id_weibullMeasure_one` and
  `TauCeti.Probability.cgf_id_weibullMeasure_one`: the shape-one transforms.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), chapter on Weibull distributions.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

open scoped Topology

namespace TauCeti

namespace Probability

variable {k lam t : ℝ}

/-- Normalize the quotient used in the superlinear power comparison. -/
private lemma mul_div_rpow_eq (hx : 0 < x) (hlam : 0 < lam) (k t : ℝ) :
    t * x / (x / lam) ^ k = (t * lam ^ k) * x ^ (-(k - 1)) := by
  rw [Real.div_rpow hx.le hlam.le, Real.rpow_neg hx.le, Real.rpow_sub_one hx.ne']
  field_simp [hx.ne', hlam.ne']

/-- Normalize the quotient used in the sublinear power comparison. -/
private lemma rpow_div_eq (hx : 0 < x) (hlam : 0 < lam) (k : ℝ) :
    (x / lam) ^ k / x = lam ^ (-k) * x ^ (-(1 - k)) := by
  have hsub : 1 - k = -(k - 1) := by ring
  rw [Real.div_rpow hx.le hlam.le, Real.rpow_neg hlam.le, hsub,
    Real.rpow_neg hx.le, Real.rpow_neg hx.le, Real.rpow_sub_one hx.ne']
  field_simp [hx.ne', hlam.ne']

/-- Normalize the prefactor used in the exponential comparison. -/
private lemma mul_rpow_mul_exp_eq (hx : 0 < x) (hlam : 0 < lam) (k t : ℝ) :
    (k / lam) * (x / lam) ^ (k - 1) * Real.exp ((t / 2) * x) =
      ((k / lam) / lam ^ (k - 1)) *
        (Real.exp ((t / 2) * x) / x ^ (1 - k)) := by
  have hsub : 1 - k = -(k - 1) := by ring
  rw [Real.div_rpow hx.le hlam.le, hsub, Real.rpow_neg hx.le]
  field_simp [hx.ne', hlam.ne']

/-- For superlinear powers, a linear function is negligible compared with the scaled power. -/
private lemma tendsto_mul_div_rpow_atTop (hk : 1 < k) (hlam : 0 < lam) (t : ℝ) :
    Tendsto (fun x : ℝ => t * x / (x / lam) ^ k) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hk)).const_mul (t * lam ^ k)
  have h' : Tendsto (fun x : ℝ => (t * lam ^ k) * x ^ (-(k - 1))) atTop (𝓝 0) := by
    simpa using h
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (mul_div_rpow_eq hx hlam k t).symm

/-- A sublinear scaled power is negligible compared with the identity. -/
private lemma tendsto_rpow_div_id_atTop (hk : k < 1) (hlam : 0 < lam) :
    Tendsto (fun x : ℝ => (x / lam) ^ k / x) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hk)).const_mul (lam ^ (-k))
  have h' : Tendsto (fun x : ℝ => lam ^ (-k) * x ^ (-(1 - k))) atTop (𝓝 0) := by
    simpa using h
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (rpow_div_eq hx hlam k).symm

/-- A positive exponential dominates the polynomial prefactor in a sublinear Weibull density. -/
private lemma tendsto_mul_rpow_mul_exp_atTop (hk : 0 < k)
    (hlam : 0 < lam) (ht : 0 < t) :
    Tendsto (fun x : ℝ =>
      (k / lam) * (x / lam) ^ (k - 1) * Real.exp ((t / 2) * x)) atTop atTop := by
  have hbase := tendsto_exp_mul_div_rpow_atTop (1 - k) (t / 2) (by positivity)
  have hcoef : 0 < (k / lam) / lam ^ (k - 1) := by positivity
  have h := hbase.const_mul_atTop hcoef
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (mul_rpow_mul_exp_eq hx hlam k t).symm

/-- Halving the Weibull decay only rescales the law: it is twice the Weibull density at scale
`lam * 2 ^ k⁻¹`, whose integrability is `integrable_weibullPDFReal`. -/
private lemma two_mul_weibullPDFReal_scale_eq (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x) :
    2 * weibullPDFReal k (lam * 2 ^ k⁻¹) x =
      (k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k / 2) := by
  have hc : (0 : ℝ) < (2 : ℝ) ^ k⁻¹ := Real.rpow_pos_of_pos two_pos _
  have hck : ((2 : ℝ) ^ k⁻¹) ^ k = 2 := by
    rw [← Real.rpow_mul zero_le_two, inv_mul_cancel₀ hk.ne', Real.rpow_one]
  have hpow : ∀ y : ℝ, (x / (lam * 2 ^ k⁻¹)) ^ y
      = (x / lam) ^ y / ((2 : ℝ) ^ k⁻¹) ^ y := fun y => by
    rw [Real.div_rpow hx.le (by positivity), Real.mul_rpow hlam.le hc.le,
      Real.div_rpow hx.le hlam.le]
    ring
  rw [weibullPDFReal_of_pos hk (by positivity) hx, hpow k, hck, hpow (k - 1),
    Real.rpow_sub hc, hck, Real.rpow_one]
  field_simp

/-- Regroup the two exponential factors in a density comparison. -/
private lemma exp_mul_mul_exp_neg (c t x p : ℝ) :
    Real.exp (t * x) * (c * Real.exp (-p)) = c * Real.exp (t * x - p) := by
  rw [sub_eq_add_neg, Real.exp_add]
  ring

/-- Every nonpositive exponential rate is integrable under a Weibull measure. -/
theorem integrable_exp_mul_id_weibullMeasure_of_nonpos (k lam : ℝ) (ht : t ≤ 0) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (weibullMeasure k lam) := by
  have h := integrable_exp_mul_of_le (μ := weibullMeasure k lam) (X := fun x : ℝ => -x)
    (-t) 0 (neg_nonneg.mpr ht) (measurable_id.neg.aemeasurable)
    ((ae_pos_weibullMeasure k lam).mono fun _ hx => neg_nonpos.mpr hx.le)
  simpa only [neg_mul_neg] using h

private lemma integrable_exp_mul_id_weibullMeasure_of_one_lt_of_scale_pos
    (hk : 1 < k) (hlam : 0 < lam) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (weibullMeasure k lam) := by
  by_cases ht : t ≤ 0
  · exact integrable_exp_mul_id_weibullMeasure_of_nonpos k lam ht
  have htpos : 0 < t := lt_of_not_ge ht
  rw [integrable_weibullMeasure_iff]
  have hratio : ∀ᶠ x in atTop, t * x / (x / lam) ^ k < (1 / 2 : ℝ) :=
    (tendsto_order.1 (tendsto_mul_div_rpow_atTop hk hlam t)).2 _ (by norm_num)
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hratio.and (eventually_gt_atTop (0 : ℝ)))
  -- The integrand is bounded by a constant times the density on the bounded initial interval.
  have hlocal : IntegrableOn
      (fun x : ℝ => Real.exp (t * x) * weibullPDFReal k lam x) (Iic a) := by
    refine (integrable_weibullPDFReal k lam).integrableOn.bdd_mul
      (c := Real.exp (t * a)) (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx htpos.le)
  -- On the tail, superlinear decay dominates the positive exponential factor.
  have htail : IntegrableOn
      (fun x : ℝ => Real.exp (t * x) * weibullPDFReal k lam x) (Ioi a) := by
    have hdom := ((integrable_weibullPDFReal k (lam * 2 ^ k⁻¹)).const_mul 2).integrableOn
      (s := Ioi a)
    refine Integrable.mono' hdom (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxa : a ≤ x := le_of_lt hx
    have hxpos : 0 < x := (ha x hxa).2
    have hpower : 0 < (x / lam) ^ k := Real.rpow_pos_of_pos (div_pos hxpos hlam) k
    have hlin : t * x ≤ (x / lam) ^ k / 2 := by
      linarith [(div_le_iff₀ hpower).mp (ha x hxa).1.le]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (weibullPDFReal_nonneg k lam x)),
      weibullPDFReal_of_pos (lt_trans zero_lt_one hk) hlam hxpos]
    have hcoef : 0 ≤ (k / lam) * (x / lam) ^ (k - 1) := by positivity
    calc
      Real.exp (t * x) *
          ((k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k))
          = ((k / lam) * (x / lam) ^ (k - 1)) *
              Real.exp (t * x - (x / lam) ^ k) :=
            exp_mul_mul_exp_neg ((k / lam) * (x / lam) ^ (k - 1)) t x
              ((x / lam) ^ k)
      _ ≤ ((k / lam) * (x / lam) ^ (k - 1)) *
              Real.exp (-(x / lam) ^ k / 2) := by
            gcongr
            linarith
      _ = 2 * weibullPDFReal k (lam * 2 ^ k⁻¹) x :=
            (two_mul_weibullPDFReal_scale_eq (lt_trans zero_lt_one hk) hlam hxpos).symm
  have hunion : Integrable (fun x : ℝ => Real.exp (t * x) * weibullPDFReal k lam x) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := a)]
    exact hlocal.union htail
  exact hunion.congr (ae_of_all _ fun x => by simp only [smul_eq_mul, mul_comm])

/-- Every real exponential rate is integrable when the Weibull shape is superlinear. This also
holds at an invalid scale, where the Weibull measure is zero. -/
theorem integrable_exp_mul_id_weibullMeasure_of_one_lt (hk : 1 < k) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (weibullMeasure k lam) := by
  by_cases hlam : 0 < lam
  · exact integrable_exp_mul_id_weibullMeasure_of_one_lt_of_scale_pos hk hlam t
  · rw [weibullMeasure_of_not_pos (by simp [hlam])]
    exact integrable_zero_measure

/-- For a superlinear Weibull law, the exponential-integrability domain is all of `ℝ`. -/
@[simp]
theorem integrableExpSet_id_weibullMeasure_of_one_lt (hk : 1 < k) :
    integrableExpSet id (weibullMeasure k lam) = univ := by
  ext t
  simp [integrableExpSet, integrable_exp_mul_id_weibullMeasure_of_one_lt hk]

/-- Positive exponential rates are not integrable when the Weibull shape is sublinear. -/
theorem not_integrable_exp_mul_id_weibullMeasure_of_lt_one (hk : 0 < k) (hk' : k < 1)
    (hlam : 0 < lam) (ht : 0 < t) :
    ¬ Integrable (fun x : ℝ => Real.exp (t * x)) (weibullMeasure k lam) := by
  rw [integrable_weibullMeasure_iff]
  intro hint
  have hsmall : ∀ᶠ x in atTop, (x / lam) ^ k / x < t / 2 :=
    (tendsto_order.1 (tendsto_rpow_div_id_atTop hk' hlam)).2 _ (by positivity)
  have hlarge : ∀ᶠ x in atTop,
      (1 : ℝ) ≤ (k / lam) * (x / lam) ^ (k - 1) * Real.exp ((t / 2) * x) :=
    (tendsto_mul_rpow_mul_exp_atTop hk hlam ht).eventually_ge_atTop 1
  -- A positive exponential eventually overcomes both the stretched decay and its prefactor.
  have hev : ∀ᶠ x in atTop,
      (1 : ℝ) ≤ Real.exp (t * x) * weibullPDFReal k lam x := by
    filter_upwards [hsmall, hlarge, eventually_gt_atTop (0 : ℝ)] with x hxsmall hxlarge hx
    have hpower : (x / lam) ^ k ≤ (t / 2) * x := by
      have hx0 : 0 < x := hx
      exact (div_le_iff₀ hx0).mp hxsmall.le
    rw [weibullPDFReal_of_pos hk hlam hx]
    calc
      (1 : ℝ) ≤ (k / lam) * (x / lam) ^ (k - 1) * Real.exp ((t / 2) * x) :=
        hxlarge
      _ ≤ (k / lam) * (x / lam) ^ (k - 1) *
          Real.exp (t * x - (x / lam) ^ k) := by
            gcongr
            linarith
      _ = Real.exp (t * x) *
          ((k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k)) :=
            (exp_mul_mul_exp_neg ((k / lam) * (x / lam) ^ (k - 1)) t x
              ((x / lam) ^ k)).symm
  exact MeasureTheory.not_integrable_of_eventually_le_atTop one_pos hev
    (hint.congr (ae_of_all _ fun x => by simp only [smul_eq_mul, mul_comm]))

/-- For a sublinear Weibull law, exponential integrability is equivalent to a nonpositive rate. -/
@[simp]
theorem integrable_exp_mul_id_weibullMeasure_iff_of_lt_one (hk : 0 < k) (hk' : k < 1)
    (hlam : 0 < lam) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (weibullMeasure k lam) ↔ t ≤ 0 :=
  ⟨fun h => not_lt.mp fun ht =>
    not_integrable_exp_mul_id_weibullMeasure_of_lt_one hk hk' hlam ht h,
    integrable_exp_mul_id_weibullMeasure_of_nonpos k lam⟩

/-- For a sublinear Weibull law, the exponential-integrability domain is `(-∞, 0]`. -/
@[simp]
theorem integrableExpSet_id_weibullMeasure_of_lt_one (hk : 0 < k) (hk' : k < 1)
    (hlam : 0 < lam) : integrableExpSet id (weibullMeasure k lam) = Iic 0 := by
  ext t
  simpa [integrableExpSet, id_eq] using
    integrable_exp_mul_id_weibullMeasure_iff_of_lt_one hk hk' hlam t

/-- For a shape-one Weibull law with positive scale, the exponential integrand is integrable
exactly below the reciprocal scale. -/
theorem integrable_exp_mul_id_weibullMeasure_one_iff (hlam : 0 < lam) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (weibullMeasure 1 lam) ↔ t < lam⁻¹ := by
  rw [weibullMeasure_one_eq_expMeasure]
  exact integrable_exp_mul_expMeasure_iff (inv_pos.mpr hlam)

/-- The exact exponential-integrability domain of a shape-one Weibull law. This is the shape-one
branch of `integrableExpSet_id_weibullMeasure`, which is the `simp` form. -/
theorem integrableExpSet_id_weibullMeasure_one (hlam : 0 < lam) :
    integrableExpSet id (weibullMeasure 1 lam) = Iio lam⁻¹ := by
  rw [weibullMeasure_one_eq_expMeasure, integrableExpSet_id_expMeasure (inv_pos.mpr hlam)]

/-- **The exponential-integrability trichotomy for a valid Weibull law.** The domain is all of
`ℝ` above shape one, is open with endpoint `lam⁻¹` at shape one, and is `(-∞, 0]` below shape
one. -/
@[simp]
theorem integrableExpSet_id_weibullMeasure (hk : 0 < k) (hlam : 0 < lam) :
    integrableExpSet id (weibullMeasure k lam) =
      if k < 1 then Iic 0 else if k = 1 then Iio lam⁻¹ else univ := by
  by_cases hklt : k < 1
  · simpa [hklt] using integrableExpSet_id_weibullMeasure_of_lt_one hk hklt hlam
  by_cases hkone : k = 1
  · subst k
    simpa using integrableExpSet_id_weibullMeasure_one hlam
  · have hone : 1 < k := lt_of_le_of_ne (not_lt.mp hklt) (Ne.symm hkone)
    simpa [hklt, hkone] using integrableExpSet_id_weibullMeasure_of_one_lt (lam := lam) hone

/-- The moment-generating function of a shape-one Weibull law with positive scale, evaluated
below the reciprocal scale. -/
theorem mgf_id_weibullMeasure_one (hlam : 0 < lam) (ht : t < lam⁻¹) :
    mgf id (weibullMeasure 1 lam) t = (1 - lam * t)⁻¹ := by
  rw [weibullMeasure_one_eq_expMeasure, mgf_id_expMeasure (inv_pos.mpr hlam) ht]
  have hlam0 : lam ≠ 0 := hlam.ne'
  field_simp

/-- The cumulant-generating function of a shape-one Weibull law with positive scale, evaluated
below the reciprocal scale. -/
theorem cgf_id_weibullMeasure_one (hlam : 0 < lam) (ht : t < lam⁻¹) :
    cgf id (weibullMeasure 1 lam) t = -Real.log (1 - lam * t) := by
  rw [cgf, mgf_id_weibullMeasure_one hlam ht, Real.log_inv]

end Probability

end TauCeti
