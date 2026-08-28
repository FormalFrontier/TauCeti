/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Density
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Moments.Variance
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# The Weibull distribution

The Weibull law with shape `k` and scale `lam` has density
`(k / lam) * (x / lam) ^ (k - 1) * exp (-(x / lam) ^ k)` on the positive
half-line. This file defines the law, proves that it is a probability measure exactly when both
parameters are positive, computes its cdf and all natural moments, and deduces its mean and
variance.

Invalid parameters produce the zero measure. This convention makes `weibullMeasure` a total,
jointly measurable family without pretending that a nonpositive shape or scale defines a
probability law.

The proofs use two successive changes of variables. Scaling by `lam` removes the scale, then
`y = x ^ k` turns the density into `exp (-y)`. The same reduction identifies the upper tail.
Natural moments reduce to Euler's Gamma integral.

## Main definitions and results

* `weibullPDFReal`, `weibullPDF` and `weibullMeasure` define the density and law;
* `isProbabilityMeasure_weibullMeasure_iff` characterizes the valid parameter range;
* `cdf_weibullMeasure_eq` gives the closed cdf;
* `integral_pow_weibullMeasure` gives every natural moment;
* `integral_id_weibullMeasure` and `variance_id_weibullMeasure` give the mean and variance;
* `cdf_weibullMeasure_one_eq_cdf_expMeasure` recovers the exponential cdf at shape one;
* `measurable_weibullMeasure` makes the family available for kernel constructions.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, **Weibull**.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), chapter on Weibull distributions.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

open scoped ENNReal Nat

namespace TauCeti

namespace Probability

variable {k lam x : ℝ}

/-! ### Density and measure -/

/-- The real-valued Weibull density with shape `k` and scale `lam`.

It is defined to be zero unless `k`, `lam`, and the sample point are all positive. -/
def weibullPDFReal (k lam x : ℝ) : ℝ :=
  if 0 < k ∧ 0 < lam ∧ 0 < x then
    (k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k)
  else 0

/-- The Weibull density, valued in `ℝ≥0∞`. -/
def weibullPDF (k lam x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (weibullPDFReal k lam x)

/-- The Weibull law with shape `k` and scale `lam`.

For invalid parameters this is the zero measure. -/
def weibullMeasure (k lam : ℝ) : Measure ℝ :=
  volume.withDensity (weibullPDF k lam)

/-- The `ℝ≥0∞`-valued density is the nonnegative coercion of the real density. -/
theorem weibullPDF_eq_ofReal (k lam x : ℝ) :
    weibullPDF k lam x = ENNReal.ofReal (weibullPDFReal k lam x) := by
  rw [weibullPDF]

/-- The real density has its usual formula at valid parameters and a positive point. -/
@[simp]
theorem weibullPDFReal_of_pos (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x) :
    weibullPDFReal k lam x =
      (k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k) := by
  simp [weibullPDFReal, hk, hlam, hx]

/-- The density vanishes on the nonpositive half-line. -/
@[simp]
theorem weibullPDFReal_of_nonpos (hx : x ≤ 0) (k lam : ℝ) :
    weibullPDFReal k lam x = 0 := by
  simp [weibullPDFReal, not_lt.mpr hx]

/-- The density vanishes when the shape is nonpositive. -/
@[simp]
theorem weibullPDFReal_of_shape_nonpos (hk : k ≤ 0) (lam x : ℝ) :
    weibullPDFReal k lam x = 0 := by
  simp [weibullPDFReal, not_lt.mpr hk]

/-- The density vanishes when the scale is nonpositive. -/
@[simp]
theorem weibullPDFReal_of_scale_nonpos (hlam : lam ≤ 0) (k x : ℝ) :
    weibullPDFReal k lam x = 0 := by
  simp [weibullPDFReal, not_lt.mpr hlam]

/-- The `ℝ≥0∞`-valued density vanishes on the nonpositive half-line. -/
@[simp]
theorem weibullPDF_of_nonpos (hx : x ≤ 0) (k lam : ℝ) : weibullPDF k lam x = 0 := by
  rw [weibullPDF_eq_ofReal, weibullPDFReal_of_nonpos hx, ENNReal.ofReal_zero]

/-- The `ℝ≥0∞`-valued density vanishes when the shape is nonpositive. -/
@[simp]
theorem weibullPDF_of_shape_nonpos (hk : k ≤ 0) (lam x : ℝ) : weibullPDF k lam x = 0 := by
  rw [weibullPDF_eq_ofReal, weibullPDFReal_of_shape_nonpos hk, ENNReal.ofReal_zero]

/-- The `ℝ≥0∞`-valued density vanishes when the scale is nonpositive. -/
@[simp]
theorem weibullPDF_of_scale_nonpos (hlam : lam ≤ 0) (k x : ℝ) : weibullPDF k lam x = 0 := by
  rw [weibullPDF_eq_ofReal, weibullPDFReal_of_scale_nonpos hlam, ENNReal.ofReal_zero]

/-- At valid parameters and a positive point, the `ℝ≥0∞` density has the usual formula. -/
@[simp]
theorem weibullPDF_of_pos (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x) :
    weibullPDF k lam x = ENNReal.ofReal
      ((k / lam) * (x / lam) ^ (k - 1) * Real.exp (-(x / lam) ^ k)) := by
  rw [weibullPDF_eq_ofReal, weibullPDFReal_of_pos hk hlam hx]

/-- The real-valued Weibull density is nonnegative. -/
theorem weibullPDFReal_nonneg (k lam x : ℝ) : 0 ≤ weibullPDFReal k lam x := by
  rw [weibullPDFReal]
  split_ifs with h
  · exact mul_nonneg (mul_nonneg (div_nonneg h.1.le h.2.1.le)
      (Real.rpow_nonneg (div_nonneg h.2.2.le h.2.1.le) _)) (Real.exp_pos _).le
  · exact le_rfl

/-- At valid parameters the density is strictly positive precisely on the positive half-line. -/
theorem weibullPDFReal_pos_iff (hk : 0 < k) (hlam : 0 < lam) :
    0 < weibullPDFReal k lam x ↔ 0 < x := by
  constructor
  · contrapose!
    intro hx
    rw [weibullPDFReal_of_nonpos hx k lam]
  · intro hx
    rw [weibullPDFReal_of_pos hk hlam hx]
    positivity

/-- The two density representations agree under `ENNReal.toReal`. -/
@[simp]
theorem toReal_weibullPDF (k lam x : ℝ) :
    (weibullPDF k lam x).toReal = weibullPDFReal k lam x :=
  ENNReal.toReal_ofReal (weibullPDFReal_nonneg k lam x)

/-- The real Weibull density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_weibullPDFReal (k lam : ℝ) : Measurable (weibullPDFReal k lam) := by
  by_cases hvalid : 0 < k ∧ 0 < lam
  · rcases hvalid with ⟨hk, hlam⟩
    have heq : weibullPDFReal k lam = fun x ↦
        if 0 < x then (k / lam) * Real.exp (Real.log (x / lam) * (k - 1)) *
          Real.exp (-Real.exp (Real.log (x / lam) * k)) else 0 := by
      funext x
      by_cases hx : 0 < x
      · rw [weibullPDFReal_of_pos hk hlam hx, ite_eq_left hx,
          Real.rpow_def_of_pos (div_pos hx hlam), Real.rpow_def_of_pos (div_pos hx hlam)]
      · rw [weibullPDFReal_of_nonpos (not_lt.mp hx) k lam, ite_eq_right hx]
    rw [heq]
    refine Measurable.ite (measurableSet_lt measurable_const measurable_id) (by fun_prop)
      measurable_const
  · have heq : weibullPDFReal k lam = 0 := by
      funext x
      rw [weibullPDFReal]
      simp only [Pi.zero_apply]
      exact ite_eq_right (fun hx ↦ hvalid ⟨hx.1, hx.2.1⟩)
    rw [heq]
    fun_prop

/-- The `ℝ≥0∞`-valued Weibull density is measurable in the sample point. -/
@[fun_prop]
theorem measurable_weibullPDF (k lam : ℝ) : Measurable (weibullPDF k lam) :=
  (measurable_weibullPDFReal k lam).ennreal_ofReal

/-- If either parameter is invalid, the Weibull measure is zero. -/
@[simp]
theorem weibullMeasure_of_not_pos (h : ¬ (0 < k ∧ 0 < lam)) : weibullMeasure k lam = 0 := by
  have hpdf : weibullPDF k lam = 0 := by
    funext y
    simp only [weibullPDF, weibullPDFReal]
    rw [ite_eq_right (fun hy ↦ h ⟨hy.1, hy.2.1⟩), ENNReal.ofReal_zero]
    rfl
  rw [weibullMeasure, hpdf, withDensity_zero]

/-! ### Normalization and tails -/

/-- The unit-scale kernel appearing after the substitution `x = lam * z`. -/
private def weibullKernel (k z : ℝ) : ℝ :=
  k * z ^ (k - 1) * Real.exp (-z ^ k)

/-- Scaling a valid density by its scale produces the unit-scale kernel. -/
private lemma scale_mul_weibullPDFReal (hk : 0 < k) (hlam : 0 < lam) (hz : 0 < x) :
    lam * weibullPDFReal k lam (lam * x) = weibullKernel k x := by
  rw [weibullPDFReal_of_pos hk hlam (mul_pos hlam hz)]
  simp only [weibullKernel]
  have hlam0 : lam ≠ 0 := hlam.ne'
  rw [mul_div_cancel_left₀ x hlam0]
  field_simp

/-- The unit-scale Weibull kernel is integrable on the positive half-line. -/
private lemma integrableOn_weibullKernel (hk : 0 < k) :
    IntegrableOn (weibullKernel k) (Ioi 0) := by
  have h := (integrableOn_Ioi_comp_rpow_iff (fun y : ℝ ↦ Real.exp (-y)) hk.ne').2
    (integrableOn_exp_neg_Ioi 0)
  unfold weibullKernel
  simpa only [abs_of_pos hk, smul_eq_mul] using h

/-- The real density is integrable for all parameters. -/
theorem integrable_weibullPDFReal (k lam : ℝ) : Integrable (weibullPDFReal k lam) := by
  by_cases hvalid : 0 < k ∧ 0 < lam
  · rcases hvalid with ⟨hk, hlam⟩
    have hcomp : IntegrableOn (fun z ↦ weibullPDFReal k lam (lam * z)) (Ioi 0) := by
      refine IntegrableOn.congr_fun ((integrableOn_weibullKernel hk).const_mul lam⁻¹) ?_
        measurableSet_Ioi
      intro z hz
      dsimp only
      rw [← scale_mul_weibullPDFReal hk hlam hz]
      field_simp
    have hpos : IntegrableOn (weibullPDFReal k lam) (Ioi 0) := by
      simpa using (integrableOn_Ioi_comp_mul_left_iff
        (weibullPDFReal k lam) 0 hlam).1 hcomp
    have hnonpos : IntegrableOn (weibullPDFReal k lam) (Iic 0) := by
      refine integrableOn_zero.congr_fun (fun z hz ↦ ?_) measurableSet_Iic
      exact (weibullPDFReal_of_nonpos hz k lam).symm
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact hnonpos.union hpos
  · have hzero : weibullPDFReal k lam = fun _ ↦ 0 := by
      funext z
      simp only [weibullPDFReal]
      rw [ite_eq_right (fun hz ↦ hvalid ⟨hz.1, hz.2.1⟩)]
    rw [hzero]
    exact integrable_zero ℝ ℝ volume

/-- The unit-scale kernel has total mass one. -/
private lemma integral_weibullKernel (hk : 0 < k) :
    ∫ z in Ioi (0 : ℝ), weibullKernel k z = 1 := by
  have h := integral_comp_rpow_Ioi_of_pos
    (g := fun y : ℝ ↦ Real.exp (-y)) hk
  unfold weibullKernel
  simpa only [smul_eq_mul, integral_exp_neg_Ioi_zero] using h

/-- The real Weibull density has total mass one at valid parameters. -/
theorem integral_weibullPDFReal (hk : 0 < k) (hlam : 0 < lam) :
    ∫ y, weibullPDFReal k lam y = 1 := by
  rw [← integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic
      (integrable_weibullPDFReal k lam), compl_Iic]
  have hleft : ∫ y in Iic (0 : ℝ), weibullPDFReal k lam y = 0 := by
    exact integral_eq_zero_of_ae (ae_restrict_mem measurableSet_Iic |>.mono
      fun y hy ↦ weibullPDFReal_of_nonpos hy k lam)
  have hzero : lam * (0 : ℝ) = 0 := mul_zero lam
  rw [hleft, zero_add, ← hzero,
    ← integral_comp_mul_left_Ioi' (weibullPDFReal k lam) 0 hlam, smul_eq_mul,
    ← integral_const_mul]
  calc
    ∫ z in Ioi (0 : ℝ), lam * weibullPDFReal k lam (lam * z)
        = ∫ z in Ioi (0 : ℝ), weibullKernel k z := by
            exact setIntegral_congr_fun measurableSet_Ioi
              (fun z hz ↦ scale_mul_weibullPDFReal hk hlam hz)
    _ = 1 := integral_weibullKernel hk

/-- The `ℝ≥0∞`-valued Weibull density has total mass one. -/
theorem lintegral_weibullPDF_eq_one (hk : 0 < k) (hlam : 0 < lam) :
    ∫⁻ y, weibullPDF k lam y = 1 := by
  simp_rw [weibullPDF_eq_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_weibullPDFReal k lam)
      (ae_of_all _ fun y ↦ weibullPDFReal_nonneg k lam y),
    integral_weibullPDFReal hk hlam, ENNReal.ofReal_one]

/-- For positive shape and scale the Weibull law is a probability measure. -/
theorem isProbabilityMeasure_weibullMeasure (hk : 0 < k) (hlam : 0 < lam) :
    IsProbabilityMeasure (weibullMeasure k lam) := by
  constructor
  rw [weibullMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_weibullPDF_eq_one hk hlam]

/-- The Weibull law is a probability measure exactly for positive shape and scale. -/
@[simp]
theorem isProbabilityMeasure_weibullMeasure_iff :
    IsProbabilityMeasure (weibullMeasure k lam) ↔ 0 < k ∧ 0 < lam := by
  constructor
  · intro hp
    by_contra h
    rw [weibullMeasure_of_not_pos h] at hp
    have hone : (0 : Measure ℝ) Set.univ = 1 :=
      @IsProbabilityMeasure.measure_univ ℝ _ (0 : Measure ℝ) hp
    have hzero_eq_one : (0 : ℝ≥0∞) = 1 := hone
    exact zero_ne_one hzero_eq_one
  · rintro ⟨hk, hlam⟩
    exact isProbabilityMeasure_weibullMeasure hk hlam

/-- The upper tail integral of a valid Weibull density. -/
theorem integral_weibullPDFReal_Ioi (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x) :
    ∫ y in Ioi x, weibullPDFReal k lam y = Real.exp (-(x / lam) ^ k) := by
  have hxlam : 0 < x / lam := div_pos hx hlam
  have hc : 0 ≤ (x / lam) ^ k := (Real.rpow_pos_of_pos hxlam k).le
  have hroot : ((x / lam) ^ k) ^ k⁻¹ = x / lam := by
    rw [← Real.rpow_mul hxlam.le, mul_inv_cancel₀ hk.ne', Real.rpow_one]
  calc
    ∫ y in Ioi x, weibullPDFReal k lam y
        = lam * ∫ z in Ioi (x / lam), weibullPDFReal k lam (lam * z) := by
            have hscale := integral_comp_mul_left_Ioi'
              (weibullPDFReal k lam) (x / lam) hlam
            simpa only [smul_eq_mul, mul_div_cancel₀ x hlam.ne'] using hscale.symm
    _ = ∫ z in Ioi (x / lam), weibullKernel k z := by
          rw [← integral_const_mul]
          exact setIntegral_congr_fun measurableSet_Ioi
            (fun z hz ↦ scale_mul_weibullPDFReal hk hlam (lt_trans hxlam hz))
    _ = ∫ z in Ioi (((x / lam) ^ k) ^ k⁻¹),
          (k * z ^ (k - 1)) • Real.exp (-(z ^ k)) := by
          rw [hroot]
          exact setIntegral_congr_fun measurableSet_Ioi fun z _ ↦ by
            simp [weibullKernel, smul_eq_mul]
    _ = ∫ y in Ioi ((x / lam) ^ k), Real.exp (-y) :=
          by
            simpa only [smul_eq_mul] using
              (integral_comp_rpow_Ioi_of_pos'
                (g := fun y : ℝ ↦ Real.exp (-y)) hk hc)
    _ = Real.exp (-(x / lam) ^ k) := integral_exp_neg_Ioi _

/-! ### Density interface and cumulative distribution function -/

variable {Omega : Type*} [MeasurableSpace Omega] {P : Measure Omega} {X : Omega → ℝ}

/-- A random variable with a Weibull law has a Lebesgue density. -/
theorem hasPDF_of_hasLaw_weibullMeasure (hX : HasLaw X (weibullMeasure k lam) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_weibullPDF k lam).aemeasurable hX

/-- The density of a random variable with a Weibull law is `weibullPDF`. -/
theorem pdf_eq_weibullPDF_of_hasLaw_weibullMeasure
    (hX : HasLaw X (weibullMeasure k lam) P) :
    pdf X P volume =ᵐ[volume] weibullPDF k lam :=
  pdf_eq_of_hasLaw_withDensity (measurable_weibullPDF k lam).aemeasurable hX

/-- The Radon–Nikodym derivative of a Weibull law is its density. -/
theorem rnDeriv_weibullMeasure (k lam : ℝ) :
    (weibullMeasure k lam).rnDeriv volume =ᵐ[volume] weibullPDF k lam :=
  Measure.rnDeriv_withDensity volume (measurable_weibullPDF k lam)

/-- Integrating the density computes the real mass of a measurable set. -/
private lemma measureReal_weibullMeasure {s : Set ℝ} (hs : MeasurableSet s) :
    (weibullMeasure k lam).real s = ∫ y in s, weibullPDFReal k lam y := by
  rw [measureReal_def, weibullMeasure, withDensity_apply _ hs]
  simp_rw [weibullPDF_eq_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_weibullPDFReal k lam).integrableOn
      (ae_of_all _ fun y ↦ weibullPDFReal_nonneg k lam y),
    ENNReal.toReal_ofReal (integral_nonneg fun y ↦ weibullPDFReal_nonneg k lam y)]

/-- The real upper-tail mass of a valid Weibull law. -/
theorem measureReal_Ioi_weibullMeasure (hk : 0 < k) (hlam : 0 < lam) (hx : 0 < x) :
    (weibullMeasure k lam).real (Ioi x) = Real.exp (-(x / lam) ^ k) := by
  rw [measureReal_weibullMeasure measurableSet_Ioi,
    integral_weibullPDFReal_Ioi hk hlam hx]

/-- The cdf of a valid Weibull law. -/
theorem cdf_weibullMeasure_eq (hk : 0 < k) (hlam : 0 < lam) (x : ℝ) :
    cdf (weibullMeasure k lam) x =
      if x ≤ 0 then 0 else 1 - Real.exp (-(x / lam) ^ k) := by
  have hp : IsProbabilityMeasure (weibullMeasure k lam) :=
    isProbabilityMeasure_weibullMeasure hk hlam
  rw [cdf_eq_real]
  split_ifs with hx
  · rw [measureReal_weibullMeasure measurableSet_Iic]
    exact integral_eq_zero_of_ae (ae_restrict_mem measurableSet_Iic |>.mono
      fun y hy ↦ weibullPDFReal_of_nonpos (hy.trans hx) k lam)
  · rw [← compl_Ioi, measureReal_compl measurableSet_Ioi,
      measureReal_Ioi_weibullMeasure hk hlam (not_le.mp hx)]
    simp

/-- At shape one, the Weibull cdf is the cdf of the exponential law of rate `lam⁻¹`. -/
theorem cdf_weibullMeasure_one_eq_cdf_expMeasure (hlam : 0 < lam) (x : ℝ) :
    cdf (weibullMeasure 1 lam) x = cdf (expMeasure lam⁻¹) x := by
  rw [cdf_weibullMeasure_eq one_pos hlam, cdf_expMeasure_eq (inv_pos.mpr hlam)]
  by_cases hx : x ≤ 0
  · rcases lt_or_eq_of_le hx with hxlt | rfl
    · simp [hx, not_le.mpr hxlt]
    · simp
  · have hx' : 0 ≤ x := (not_le.mp hx).le
    simp only [ite_eq_right hx, ite_eq_left hx', Real.rpow_one]
    congr 3
    field_simp

/-! ### Natural moments, mean, and variance -/

/-- Combine a positive real power with a natural power. -/
private lemma rpow_sub_one_mul_pow (hz : 0 < x) (k : ℝ) (n : ℕ) :
    x ^ (k - 1) * x ^ n = x ^ (k + (n : ℝ) - 1) := by
  rw [← Real.rpow_natCast x n, ← Real.rpow_add hz]
  congr 1
  ring

/-- The weighted density defining the `n`th moment is integrable. -/
private lemma integrable_weibullPDFReal_mul_pow (hk : 0 < k) (hlam : 0 < lam) (n : ℕ) :
    Integrable (fun y ↦ weibullPDFReal k lam y * y ^ n) := by
  have hq : (-1 : ℝ) < k + (n : ℝ) - 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hbase := integrableOn_rpow_mul_exp_neg_rpow (p := k)
    (s := k + (n : ℝ) - 1) hq hk
  have hkernel : IntegrableOn (fun z : ℝ ↦ weibullKernel k z * z ^ n) (Ioi 0) := by
    refine IntegrableOn.congr_fun (hbase.const_mul k) (fun z hz ↦ ?_) measurableSet_Ioi
    simp only [weibullKernel]
    rw [← rpow_sub_one_mul_pow hz k n]
    ring
  have hcomp : IntegrableOn
      (fun z ↦ weibullPDFReal k lam (lam * z) * (lam * z) ^ n) (Ioi 0) := by
    refine IntegrableOn.congr_fun
      ((hkernel.const_mul (lam ^ n)).const_mul lam⁻¹) (fun z hz ↦ ?_) measurableSet_Ioi
    rw [mul_pow, ← scale_mul_weibullPDFReal hk hlam hz]
    field_simp
  have hpos : IntegrableOn (fun y ↦ weibullPDFReal k lam y * y ^ n) (Ioi 0) := by
    simpa using (integrableOn_Ioi_comp_mul_left_iff
      (fun y ↦ weibullPDFReal k lam y * y ^ n) 0 hlam).1 hcomp
  have hnonpos : IntegrableOn (fun y ↦ weibullPDFReal k lam y * y ^ n) (Iic 0) := by
    refine integrableOn_zero.congr_fun (fun y hy ↦ ?_) measurableSet_Iic
    simp [weibullPDFReal_of_nonpos hy k lam]
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact hnonpos.union hpos

/-- The unit-scale integral underlying the `n`th Weibull moment. -/
private lemma integral_weibullKernel_mul_pow (hk : 0 < k) (n : ℕ) :
    ∫ z in Ioi (0 : ℝ), weibullKernel k z * z ^ n =
      Real.Gamma (1 + (n : ℝ) / k) := by
  have hq : (-1 : ℝ) < k + (n : ℝ) - 1 := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h := integral_rpow_mul_exp_neg_rpow (p := k)
    (q := k + (n : ℝ) - 1) hk hq
  have harg : (k + (n : ℝ) - 1 + 1) / k = 1 + (n : ℝ) / k := by
    field_simp
    ring
  calc
    ∫ z in Ioi (0 : ℝ), weibullKernel k z * z ^ n
        = k * ∫ z in Ioi (0 : ℝ),
            z ^ (k + (n : ℝ) - 1) * Real.exp (-z ^ k) := by
          rw [← integral_const_mul]
          exact setIntegral_congr_fun measurableSet_Ioi fun z hz ↦ by
            simp only [weibullKernel]
            rw [← rpow_sub_one_mul_pow hz k n]
            ring
    _ = Real.Gamma (1 + (n : ℝ) / k) := by
          rw [h, harg]
          field_simp

/-- Every natural power is integrable under a Weibull measure. -/
theorem integrable_pow_weibullMeasure (k lam : ℝ) (n : ℕ) :
    Integrable (fun y ↦ y ^ n) (weibullMeasure k lam) := by
  by_cases hvalid : 0 < k ∧ 0 < lam
  · rcases hvalid with ⟨hk, hlam⟩
    rw [weibullMeasure, integrable_withDensity_iff (measurable_weibullPDF k lam)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
    simp_rw [toReal_weibullPDF]
    exact (integrable_weibullPDFReal_mul_pow hk hlam n).congr
      (ae_of_all _ fun y ↦ by ring)
  · simp [weibullMeasure_of_not_pos hvalid]

/-- The `n`th raw moment of a valid Weibull law. -/
@[simp]
theorem integral_pow_weibullMeasure (hk : 0 < k) (hlam : 0 < lam) (n : ℕ) :
    ∫ y, y ^ n ∂weibullMeasure k lam =
      lam ^ n * Real.Gamma (1 + (n : ℝ) / k) := by
  rw [weibullMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_weibullPDF k lam) (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [toReal_weibullPDF, smul_eq_mul]
  rw [← integral_add_compl (s := Iic (0 : ℝ)) measurableSet_Iic
      (integrable_weibullPDFReal_mul_pow hk hlam n), compl_Iic]
  have hleft : ∫ y in Iic (0 : ℝ), weibullPDFReal k lam y * y ^ n = 0 := by
    exact integral_eq_zero_of_ae (ae_restrict_mem measurableSet_Iic |>.mono
      fun y hy ↦ by simp [weibullPDFReal_of_nonpos hy k lam])
  have hzero : lam * (0 : ℝ) = 0 := mul_zero lam
  rw [hleft, zero_add, ← hzero,
    ← integral_comp_mul_left_Ioi'
      (fun y ↦ weibullPDFReal k lam y * y ^ n) 0 hlam, smul_eq_mul,
    ← integral_const_mul]
  calc
    ∫ z in Ioi (0 : ℝ), lam * (weibullPDFReal k lam (lam * z) * (lam * z) ^ n)
        = lam ^ n * ∫ z in Ioi (0 : ℝ), weibullKernel k z * z ^ n := by
          rw [← integral_const_mul]
          exact setIntegral_congr_fun measurableSet_Ioi fun z hz ↦ by
            rw [mul_pow]
            calc
              lam * (weibullPDFReal k lam (lam * z) * (lam ^ n * z ^ n)) =
                  lam ^ n * ((lam * weibullPDFReal k lam (lam * z)) * z ^ n) := by ring
              _ = lam ^ n * (weibullKernel k z * z ^ n) := by
                rw [scale_mul_weibullPDFReal hk hlam hz]
    _ = lam ^ n * Real.Gamma (1 + (n : ℝ) / k) := by
          rw [integral_weibullKernel_mul_pow hk n]

/-- The mean of a valid Weibull law. -/
@[simp]
theorem integral_id_weibullMeasure (hk : 0 < k) (hlam : 0 < lam) :
    ∫ y, y ∂weibullMeasure k lam = lam * Real.Gamma (1 + 1 / k) := by
  simpa using integral_pow_weibullMeasure hk hlam 1

/-- The variance of a valid Weibull law. -/
theorem variance_id_weibullMeasure (hk : 0 < k) (hlam : 0 < lam) :
    variance id (weibullMeasure k lam) =
      lam ^ 2 * (Real.Gamma (1 + 2 / k) - Real.Gamma (1 + 1 / k) ^ 2) := by
  have hp : IsProbabilityMeasure (weibullMeasure k lam) :=
    isProbabilityMeasure_weibullMeasure hk hlam
  have hmem : MemLp id 2 (weibullMeasure k lam) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2
      (by simpa using integrable_pow_weibullMeasure k lam 2)
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq, integral_pow_weibullMeasure hk hlam,
    integral_id_weibullMeasure hk hlam]
  ring_nf

/-! ### Parameter measurability -/

/-- The Weibull density is jointly measurable in shape, scale, and sample point. -/
@[fun_prop]
theorem measurable_uncurry_weibullPDF :
    Measurable fun q : (ℝ × ℝ) × ℝ ↦ weibullPDF q.1.1 q.1.2 q.2 := by
  have heq : (fun q : (ℝ × ℝ) × ℝ ↦ weibullPDF q.1.1 q.1.2 q.2) = fun q ↦
      ENNReal.ofReal (if 0 < q.1.1 ∧ 0 < q.1.2 ∧ 0 < q.2 then
        (q.1.1 / q.1.2) * Real.exp (Real.log (q.2 / q.1.2) * (q.1.1 - 1)) *
          Real.exp (-Real.exp (Real.log (q.2 / q.1.2) * q.1.1)) else 0) := by
    funext q
    rw [weibullPDF, weibullPDFReal]
    split_ifs with h
    · rw [Real.rpow_def_of_pos (div_pos h.2.2 h.2.1),
        Real.rpow_def_of_pos (div_pos h.2.2 h.2.1)]
    · rfl
  rw [heq]
  refine (Measurable.ite ?_ (by fun_prop) measurable_const).ennreal_ofReal
  have hkset : MeasurableSet {q : (ℝ × ℝ) × ℝ | (0 : ℝ) < q.1.1} :=
    measurableSet_lt (measurable_const : Measurable fun _ : (ℝ × ℝ) × ℝ ↦ (0 : ℝ))
      measurable_fst.fst
  have hlamset : MeasurableSet {q : (ℝ × ℝ) × ℝ | (0 : ℝ) < q.1.2} :=
    measurableSet_lt (measurable_const : Measurable fun _ : (ℝ × ℝ) × ℝ ↦ (0 : ℝ))
      measurable_fst.snd
  have hxset : MeasurableSet {q : (ℝ × ℝ) × ℝ | (0 : ℝ) < q.2} :=
    measurableSet_lt (measurable_const : Measurable fun _ : (ℝ × ℝ) × ℝ ↦ (0 : ℝ))
      measurable_snd
  have hset : {q : (ℝ × ℝ) × ℝ | (0 : ℝ) < q.1.1 ∧ 0 < q.1.2 ∧ 0 < q.2} =
      {q | (0 : ℝ) < q.1.1} ∩ {q | (0 : ℝ) < q.1.2} ∩ {q | (0 : ℝ) < q.2} := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    exact and_assoc.symm
  rw [hset]
  exact (hkset.inter hlamset).inter hxset

/-- The Weibull family is measurable in shape and scale. -/
@[fun_prop]
theorem measurable_weibullMeasure :
    Measurable fun p : ℝ × ℝ ↦ weibullMeasure p.1 p.2 :=
  measurable_withDensity (μ := volume) measurable_uncurry_weibullPDF

end Probability

end TauCeti
