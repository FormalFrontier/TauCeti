/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Weibull.Basic
public import TauCeti.Probability.Distributions.Exponential
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Exponential moments of the Weibull distribution

The exponential moments of a Weibull law exhibit three different regimes according to its shape
`k`. They are finite at every real argument when `1 < k`, finite precisely below the reciprocal
scale when `k = 1`, and finite precisely at nonpositive arguments when `0 < k < 1`.

This file proves that trichotomy. The superlinear case follows by comparison with a Weibull tail
whose exponent has been halved; the sublinear case follows because every positive exponential
eventually dominates the density's stretched-exponential decay. At shape one, identifying the
Weibull law with an exponential law also gives closed formulas for its mgf and cgf.

## Main results

* `TauCeti.Probability.weibullMeasure_one`: shape-one Weibull is exponential;
* `TauCeti.Probability.integrable_exp_mul_id_weibullMeasure_of_nonpos`: every nonpositive
  exponential rate is integrable;
* `TauCeti.Probability.integrableExpSet_id_weibullMeasure_of_one_lt` and
  `TauCeti.Probability.integrableExpSet_id_weibullMeasure_of_lt_one`: the superlinear and
  sublinear domains;
* `TauCeti.Probability.integrableExpSet_id_weibullMeasure_one`: the shape-one domain is
  `(-∞, lam⁻¹)`;
* `TauCeti.Probability.mgf_id_weibullMeasure_one` and
  `TauCeti.Probability.cgf_id_weibullMeasure_one`: the shape-one transforms.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, **Weibull**.
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

/-- For superlinear powers, a linear function is negligible compared with the scaled power. -/
private lemma tendsto_linear_div_weibullPower (hk : 1 < k) (hlam : 0 < lam) (t : ℝ) :
    Tendsto (fun x : ℝ => t * x / (x / lam) ^ k) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hk)).const_mul (t * lam ^ k)
  have h' : Tendsto (fun x : ℝ => (t * lam ^ k) * x ^ (-(k - 1))) atTop (𝓝 0) := by
    simpa using h
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.div_rpow hx.le hlam.le, Real.rpow_neg hx.le, Real.rpow_sub_one hx.ne']
  field_simp

/-- A sublinear scaled power is negligible compared with the identity. -/
private lemma tendsto_weibullPower_div_linear (hk : k < 1) (hlam : 0 < lam) :
    Tendsto (fun x : ℝ => (x / lam) ^ k / x) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hk)).const_mul (lam ^ (-k))
  have h' : Tendsto (fun x : ℝ => lam ^ (-k) * x ^ (-(1 - k))) atTop (𝓝 0) := by
    simpa using h
  refine h'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.div_rpow hx.le hlam.le, Real.rpow_neg hlam.le, Real.rpow_neg hx.le,
    show 1 - k = -(k - 1) by ring, Real.rpow_neg hx.le,
    Real.rpow_sub_one hx.ne']
  field_simp

/-- A positive exponential dominates the polynomial prefactor in a sublinear Weibull density. -/
private lemma tendsto_weibullPrefactor_mul_exp_atTop (hk : 0 < k)
    (hlam : 0 < lam) (ht : 0 < t) :
    Tendsto (fun x : ℝ =>
      (k / lam) * (x / lam) ^ (k - 1) * Real.exp ((t / 2) * x)) atTop atTop := by
  have hbase := tendsto_exp_mul_div_rpow_atTop (1 - k) (t / 2) (by positivity)
  have hcoef : 0 < (k / lam) / lam ^ (k - 1) := by positivity
  have h := hbase.const_mul_atTop hcoef
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.div_rpow hx.le hlam.le, show 1 - k = -(k - 1) by ring,
    Real.rpow_neg hx.le]
  field_simp

/-- Halving the Weibull decay still leaves an integrable density-shaped function. -/
private lemma integrableOn_weibullHalfTail (hk : 0 < k) (hlam : 0 < lam) :
    IntegrableOn (fun x : ℝ =>
      (k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k / 2)) (Ioi 0) := by
  have hbase : IntegrableOn
      (fun z : ℝ => z ^ (k - 1) * Real.exp (-(1 / 2 : ℝ) * z ^ k)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) hk (by norm_num)
  have hcomp : IntegrableOn (fun z : ℝ =>
      (k / lam) * ((lam * z) / lam) ^ (k - 1) *
        Real.exp (-((lam * z) / lam) ^ k / 2)) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hbase.const_mul (k / lam)) (fun z _ => ?_) measurableSet_Ioi
    rw [mul_div_cancel_left₀ z hlam.ne']
    ring_nf
  simpa using (integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ => (k / lam) * (x / lam) ^ (k - 1) *
      Real.exp (-(x / lam) ^ k / 2)) 0 hlam).1 hcomp

/-- **A shape-one Weibull law is exponential.** Its scale `lam` is the reciprocal of the
exponential rate. -/
theorem weibullMeasure_one (hlam : 0 < lam) :
    weibullMeasure 1 lam = expMeasure lam⁻¹ := by
  let _ : IsProbabilityMeasure (weibullMeasure 1 lam) :=
    isProbabilityMeasure_weibullMeasure one_pos hlam
  let _ : IsProbabilityMeasure (expMeasure lam⁻¹) :=
    isProbabilityMeasure_expMeasure (inv_pos.mpr hlam)
  apply Measure.eq_of_cdf
  ext x
  exact cdf_weibullMeasure_one_eq_cdf_expMeasure hlam x

/-- Every nonpositive exponential rate is integrable under a valid Weibull law. -/
theorem integrable_exp_mul_id_weibullMeasure_of_nonpos (hk : 0 < k) (hlam : 0 < lam)
    (ht : t ≤ 0) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (weibullMeasure k lam) := by
  let _ : IsProbabilityMeasure (weibullMeasure k lam) :=
    isProbabilityMeasure_weibullMeasure hk hlam
  refine Integrable.mono' (integrable_const 1) (by fun_prop) ?_
  filter_upwards [ae_pos_weibullMeasure k lam] with x hx
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg ht hx.le

/-- Every real exponential rate is integrable when the Weibull shape is superlinear. -/
theorem integrable_exp_mul_id_weibullMeasure_of_one_lt (hk : 1 < k) (hlam : 0 < lam)
    (t : ℝ) : Integrable (fun x : ℝ => Real.exp (t * x)) (weibullMeasure k lam) := by
  by_cases ht : t ≤ 0
  · exact integrable_exp_mul_id_weibullMeasure_of_nonpos (lt_trans zero_lt_one hk) hlam ht
  have htpos : 0 < t := lt_of_not_ge ht
  rw [weibullMeasure_eq_withDensity, integrable_withDensity_iff (measurable_weibullPDF k lam)
    (ae_of_all _ fun x => weibullPDF_lt_top k lam x)]
  simp_rw [toReal_weibullPDF]
  have hratio : ∀ᶠ x in atTop, t * x / (x / lam) ^ k < (1 / 2 : ℝ) :=
    (tendsto_order.1 (tendsto_linear_div_weibullPower hk hlam t)).2 _ (by norm_num)
  obtain ⟨a, ha⟩ := eventually_atTop.mp (hratio.and (eventually_gt_atTop (0 : ℝ)))
  have hlocal : IntegrableOn
      (fun x : ℝ => Real.exp (t * x) * weibullPDFReal k lam x) (Iic a) := by
    refine (integrable_weibullPDFReal k lam).integrableOn.bdd_mul
      (c := Real.exp (t * a)) (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx htpos.le)
  have htail : IntegrableOn
      (fun x : ℝ => Real.exp (t * x) * weibullPDFReal k lam x) (Ioi a) := by
    have hdom := (integrableOn_weibullHalfTail (lt_trans zero_lt_one hk) hlam).mono_set
      (Ioi_subset_Ioi (ha a le_rfl).2.le)
    refine Integrable.mono' hdom (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxa : a ≤ x := le_of_lt hx
    have hxpos : 0 < x := (ha x hxa).2
    have hpower : 0 < (x / lam) ^ k := Real.rpow_pos_of_pos (div_pos hxpos hlam) k
    have hlin : t * x ≤ (x / lam) ^ k / 2 := by
      simpa [div_eq_mul_inv, mul_comm] using (div_le_iff₀ hpower).mp (ha x hxa).1.le
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (weibullPDFReal_nonneg k lam x)),
      weibullPDFReal_of_pos (lt_trans zero_lt_one hk) hlam hxpos]
    have hcoef : 0 ≤ (k / lam) * (x / lam) ^ (k - 1) := by positivity
    calc
      Real.exp (t * x) *
          ((k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k))
          = ((k / lam) * (x / lam) ^ (k - 1)) *
              Real.exp (t * x - (x / lam) ^ k) := by
            rw [show Real.exp (t * x) *
                ((k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k)) =
              ((k / lam) * (x / lam) ^ (k - 1)) *
                (Real.exp (t * x) * Real.exp (-(x / lam) ^ k)) by ring,
              ← Real.exp_add]
            ring_nf
      _ ≤ ((k / lam) * (x / lam) ^ (k - 1)) *
              Real.exp (-(x / lam) ^ k / 2) := by
            gcongr
            linarith
      _ = (k / lam) * (x / lam) ^ (k - 1) *
              Real.exp (-(x / lam) ^ k / 2) := by ring
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := a)]
  exact hlocal.union htail

/-- For a superlinear Weibull law, the exponential-integrability domain is all of `ℝ`. -/
@[simp]
theorem integrableExpSet_id_weibullMeasure_of_one_lt (hk : 1 < k) (hlam : 0 < lam) :
    integrableExpSet id (weibullMeasure k lam) = univ := by
  ext t
  simp [integrableExpSet, integrable_exp_mul_id_weibullMeasure_of_one_lt hk hlam]

/-- Positive exponential rates are not integrable when the Weibull shape is sublinear. -/
theorem not_integrable_exp_mul_id_weibullMeasure_of_lt_one (hk : 0 < k) (hk' : k < 1)
    (hlam : 0 < lam) (ht : 0 < t) :
    ¬ Integrable (fun x : ℝ => Real.exp (t * x)) (weibullMeasure k lam) := by
  rw [weibullMeasure_eq_withDensity, integrable_withDensity_iff (measurable_weibullPDF k lam)
    (ae_of_all _ fun x => weibullPDF_lt_top k lam x)]
  simp_rw [toReal_weibullPDF]
  intro hint
  have hsmall : ∀ᶠ x in atTop, (x / lam) ^ k / x < t / 2 :=
    (tendsto_order.1 (tendsto_weibullPower_div_linear hk' hlam)).2 _ (by positivity)
  have hlarge : ∀ᶠ x in atTop,
      (1 : ℝ) ≤ (k / lam) * (x / lam) ^ (k - 1) * Real.exp ((t / 2) * x) :=
    (tendsto_weibullPrefactor_mul_exp_atTop hk hlam ht).eventually_ge_atTop 1
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
          ((k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k)) := by
            rw [show Real.exp (t * x) *
                ((k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k)) =
              ((k / lam) * (x / lam) ^ (k - 1)) *
                (Real.exp (t * x) * Real.exp (-(x / lam) ^ k)) by ring,
              ← Real.exp_add]
            ring_nf
  obtain ⟨a, ha⟩ := eventually_atTop.mp hev
  have hone : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi a) volume := by
    refine Integrable.mono' hint.integrableOn (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_one]
    exact ha x hx.le
  rw [integrableOn_const_iff] at hone
  simp [Real.volume_Ioi] at hone

/-- For a sublinear Weibull law, exponential integrability is equivalent to a nonpositive rate. -/
@[simp]
theorem integrable_exp_mul_id_weibullMeasure_of_lt_one_iff (hk : 0 < k) (hk' : k < 1)
    (hlam : 0 < lam) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (weibullMeasure k lam) ↔ t ≤ 0 := by
  exact ⟨fun h => not_lt.mp fun ht =>
    not_integrable_exp_mul_id_weibullMeasure_of_lt_one hk hk' hlam ht h,
    integrable_exp_mul_id_weibullMeasure_of_nonpos hk hlam⟩

/-- For a sublinear Weibull law, the exponential-integrability domain is `(-∞, 0]`. -/
@[simp]
theorem integrableExpSet_id_weibullMeasure_of_lt_one (hk : 0 < k) (hk' : k < 1)
    (hlam : 0 < lam) : integrableExpSet id (weibullMeasure k lam) = Iic 0 := by
  ext t
  simpa [integrableExpSet, id_eq] using
    integrable_exp_mul_id_weibullMeasure_of_lt_one_iff hk hk' hlam t

/-- At shape one, the exponential integrand is integrable exactly below the reciprocal scale. -/
@[simp]
theorem integrable_exp_mul_id_weibullMeasure_one_iff (hlam : 0 < lam) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (weibullMeasure 1 lam) ↔ t < lam⁻¹ := by
  rw [weibullMeasure_one hlam]
  exact integrable_exp_mul_expMeasure_iff (inv_pos.mpr hlam)

/-- The exact exponential-integrability domain of a shape-one Weibull law. -/
@[simp]
theorem integrableExpSet_id_weibullMeasure_one (hlam : 0 < lam) :
    integrableExpSet id (weibullMeasure 1 lam) = Iio lam⁻¹ := by
  ext t
  simpa [integrableExpSet, id_eq] using
    integrable_exp_mul_id_weibullMeasure_one_iff hlam t

/-- **The exponential-integrability trichotomy for a valid Weibull law.** The domain is all of
`ℝ` above shape one, is open with endpoint `lam⁻¹` at shape one, and is `(-∞, 0]` below shape
one. -/
theorem integrableExpSet_id_weibullMeasure (hk : 0 < k) (hlam : 0 < lam) :
    integrableExpSet id (weibullMeasure k lam) =
      if k < 1 then Iic 0 else if k = 1 then Iio lam⁻¹ else univ := by
  by_cases hklt : k < 1
  · simpa [hklt] using integrableExpSet_id_weibullMeasure_of_lt_one hk hklt hlam
  by_cases hkone : k = 1
  · subst k
    simpa using integrableExpSet_id_weibullMeasure_one hlam
  · have hone : 1 < k := lt_of_le_of_ne (not_lt.mp hklt) (Ne.symm hkone)
    simpa [hklt, hkone] using integrableExpSet_id_weibullMeasure_of_one_lt hone hlam

/-- The moment-generating function of a shape-one Weibull law. -/
theorem mgf_id_weibullMeasure_one (hlam : 0 < lam) (ht : t < lam⁻¹) :
    mgf id (weibullMeasure 1 lam) t = (1 - lam * t)⁻¹ := by
  rw [weibullMeasure_one hlam, mgf_id_expMeasure (inv_pos.mpr hlam) ht]
  have hlam0 : lam ≠ 0 := hlam.ne'
  field_simp

/-- The cumulant-generating function of a shape-one Weibull law. -/
theorem cgf_id_weibullMeasure_one (hlam : 0 < lam) (ht : t < lam⁻¹) :
    cgf id (weibullMeasure 1 lam) t = Real.log (1 - lam * t)⁻¹ := by
  rw [cgf, mgf_id_weibullMeasure_one hlam ht]

end Probability

end TauCeti
