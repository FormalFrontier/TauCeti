/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Moments.MGFAnalytic
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import TauCeti.MeasureTheory.Integral.ExpDecay

/-!
# Elementary theory of the exponential distribution

This file completes the elementary moment and transform API for Mathlib's exponential measure,
parametrized by its rate.  For a positive rate `r`, it identifies the exact exponential-moment
domain, computes the moment- and cumulant-generating functions and the characteristic function,
and deduces the mean and variance.  It also states the memoryless property using conditional
probability.

The real integral calculations are adapted from
[mathlib4#35504](https://github.com/leanprover-community/mathlib4/pull/35504) by Joakim Björnander
(Apache 2.0).  The exact converse for the moment domain uses
`TauCeti.integrableOn_exp_mul_Ioi_iff`.

## Main results

* `ProbabilityTheory.integrableExpSet_id_expMeasure`: the exact domain `(-∞, r)`.
* `ProbabilityTheory.mgf_id_expMeasure` and `ProbabilityTheory.cgf_id_expMeasure`: the real
  transforms on that domain.
* `ProbabilityTheory.charFun_expMeasure`: the characteristic function.
* `ProbabilityTheory.integral_id_expMeasure` and `ProbabilityTheory.variance_id_expMeasure`: the
  mean and variance.
* `ProbabilityTheory.memoryless_expMeasure`: the conditional tail is unchanged by elapsed time.
* `ProbabilityTheory.map_min_expMeasure`: the minimum of independent exponentials.
-/

public section

noncomputable section

open scoped ENNReal NNReal

open MeasureTheory Real Set

namespace ProbabilityTheory

variable {r t : ℝ}

/-- Rewrite integrals against `expMeasure r` as Lebesgue integrals weighted by its density. -/
private lemma integral_expMeasure_eq_integral_density
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (r : ℝ) (f : ℝ → E) :
    ∫ x, f x ∂(expMeasure r) = ∫ x, (exponentialPDF r x).toReal • f x := by
  have hmeas : Measurable (gammaPDF 1 r) :=
    (measurable_gammaPDFReal 1 r).ennreal_ofReal
  simpa only [expMeasure, gammaMeasure, exponentialPDF, exponentialPDFReal, gammaPDF] using
    integral_withDensity_eq_integral_toReal_smul
      (μ := volume) (f := gammaPDF 1 r) (g := f) hmeas
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)

/-- The exponential integrand is integrable exactly below the rate. -/
lemma integrable_exp_mul_expMeasure_iff (hr : 0 < r) :
    Integrable (fun x => exp (t * x)) (expMeasure r) ↔ t < r := by
  -- Expose the with-density definition to apply the exact integrability criterion.
  change Integrable (fun x => exp (t * x))
      (volume.withDensity (exponentialPDF r)) ↔ t < r
  have hmeas : Measurable (exponentialPDF r) := by
    unfold exponentialPDF
    exact (measurable_exponentialPDFReal r).ennreal_ofReal
  rw [integrable_withDensity_iff hmeas
    (ae_of_all _ fun x => by simp [exponentialPDF])]
  have hfun : (fun x : ℝ => exp (t * x) * (exponentialPDF r x).toReal) =
      (Set.Ici (0 : ℝ)).indicator (fun x => r * exp ((t - r) * x)) := by
    funext x
    by_cases hx : 0 ≤ x
    · have hxmem : x ∈ Ici 0 := hx
      rw [Set.indicator_of_mem hxmem, exponentialPDF_of_nonneg hx,
        ENNReal.toReal_ofReal (by positivity)]
      calc
        exp (t * x) * (r * exp (-(r * x))) = r * (exp (t * x) * exp (-(r * x))) := by ring
        _ = r * exp ((t - r) * x) := by rw [← exp_add]; congr 2; ring
    · have hxmem : x ∉ Ici 0 := hx
      rw [Set.indicator_of_notMem hxmem, exponentialPDF_of_neg (lt_of_not_ge hx)]
      simp
  rw [hfun, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi]
  -- Unfold `IntegrableOn` to remove the nonzero constant on the restricted measure.
  change Integrable (fun x => r * exp ((t - r) * x))
      (volume.restrict (Set.Ioi 0)) ↔ t < r
  rw [integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hr.ne')]
  simpa only [IntegrableOn, sub_lt_zero] using
    (TauCeti.integrableOn_exp_mul_Ioi_iff (a := t - r) (c := 0))

/-- The exact exponential-integrability domain of an exponential law with positive rate. -/
@[simp]
theorem integrableExpSet_id_expMeasure (hr : 0 < r) :
    integrableExpSet id (expMeasure r) = Set.Iio r := by
  ext t
  simpa [integrableExpSet] using
    (integrable_exp_mul_expMeasure_iff (r := r) (t := t) hr)

/-- The integral of `exp (t * x)` against `expMeasure r`, for `t < r`. -/
lemma integral_exp_mul_expMeasure (hr : 0 < r) (ht : t < r) :
    ∫ x, exp (t * x) ∂(expMeasure r) = r / (r - t) := by
  rw [integral_expMeasure_eq_integral_density]
  simp only [smul_eq_mul]
  have hIci0 :
      ∫ x, (exponentialPDF r x).toReal * exp (t * x) =
        ∫ x in Ici 0, (exponentialPDF r x).toReal * exp (t * x) := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    simp [exponentialPDF_of_neg (by simpa [mem_Ici] using hx)]
  have hIci :
      ∫ x in Ici 0, (exponentialPDF r x).toReal * exp (t * x) =
        ∫ x in Ici 0, r * exp ((t - r) * x) := by
    refine setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
    rw [exponentialPDF_of_nonneg hx, ENNReal.toReal_ofReal (by positivity),
      mul_assoc, mul_comm _ (exp (t * x)), ← exp_add]
    congr 2
    ring
  rw [hIci0, hIci, integral_Ici_eq_integral_Ioi, integral_const_mul]
  rw [integral_exp_mul_Ioi (sub_neg.mpr ht) 0]
  simp only [mul_zero, exp_zero, neg_div, ← div_neg, neg_sub, mul_one_div]

/-- The moment-generating function of an exponential law with positive rate. -/
theorem mgf_id_expMeasure (hr : 0 < r) (ht : t < r) :
    mgf id (expMeasure r) t = r / (r - t) := by
  simpa [mgf, id_eq] using integral_exp_mul_expMeasure (r := r) (t := t) hr ht

/-- The cumulant-generating function of an exponential law with positive rate. -/
theorem cgf_id_expMeasure (hr : 0 < r) (ht : t < r) :
    cgf id (expMeasure r) t = log (r / (r - t)) := by
  rw [cgf, mgf_id_expMeasure hr ht]

/-- The characteristic function of an exponential law with positive rate. -/
theorem charFun_expMeasure (hr : 0 < r) (t : ℝ) :
    charFun (expMeasure r) t = (r : ℂ) / (r - Complex.I * t) := by
  rw [charFun_apply_real, integral_expMeasure_eq_integral_density]
  have hIci0 :
      ∫ x, (exponentialPDF r x).toReal • Complex.exp (t * x * Complex.I) =
        ∫ x in Ici 0, (exponentialPDF r x).toReal • Complex.exp (t * x * Complex.I) := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    simp [exponentialPDF_of_neg (by simpa [mem_Ici] using hx)]
  have hIci :
      ∫ x in Ici 0, (exponentialPDF r x).toReal • Complex.exp (t * x * Complex.I) =
        ∫ x : ℝ in Ici 0, (r : ℂ) *
          Complex.exp ((-(r : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
    rw [exponentialPDF_of_nonneg hx, ENNReal.toReal_ofReal (by positivity),
      Complex.real_smul]
    push_cast
    calc
      (r : ℂ) * Complex.exp (-(r * x)) * Complex.exp (t * x * Complex.I) =
          (r : ℂ) * Complex.exp
            (-(r : ℂ) * (x : ℂ) + (t : ℂ) * (x : ℂ) * Complex.I) := by
            rw [mul_assoc, ← Complex.exp_add]
            simp only [neg_mul]
      _ = (r : ℂ) * Complex.exp ((-(r : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) := by
        congr 2
        ring
  rw [hIci0, hIci, integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_exp_mul_complex_Ioi (by simpa using neg_lt_zero.mpr hr) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hden : -(r : ℂ) + (t : ℂ) * Complex.I =
      -((r : ℂ) - (t : ℂ) * Complex.I) := by ring
  rw [hden]
  simp only [div_neg]
  congr 2
  ring

/-- The identity belongs to every finite `Lᵖ` space under a positive-rate exponential law. -/
lemma memLp_id_expMeasure (hr : 0 < r) (p : ℝ≥0) :
    MemLp id p (expMeasure r) := by
  apply memLp_of_mem_interior_integrableExpSet
  rw [integrableExpSet_id_expMeasure hr, interior_Iio]
  exact hr

/-- The mean of an exponential law with positive rate `r` is `r⁻¹`. -/
@[simp]
theorem integral_id_expMeasure (hr : 0 < r) : ∫ x, x ∂(expMeasure r) = r⁻¹ := by
  rw [integral_expMeasure_eq_integral_density]
  simp only [smul_eq_mul]
  have hIci0 :
      ∫ x, (exponentialPDF r x).toReal * x =
        ∫ x in Ici 0, (exponentialPDF r x).toReal * x := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    simp [exponentialPDF_of_neg (by simpa [mem_Ici] using hx)]
  have hIci :
      ∫ x in Ici 0, (exponentialPDF r x).toReal * x =
        ∫ x in Ici 0, r * (x * exp (-(r * x))) := by
    refine setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
    rw [exponentialPDF_of_nonneg hx, ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [hIci0, hIci, integral_Ici_eq_integral_Ioi, integral_const_mul]
  have hpow : ∫ a : ℝ in Ioi 0, a * exp (-(r * a)) = 1 / r ^ 2 := by
    simpa using TauCeti.integral_pow_mul_exp_neg_mul_Ioi 1 hr
  rw [hpow]
  norm_num
  field_simp [hr.ne']

/-- The second raw moment of an exponential law with positive rate. -/
private lemma integral_sq_expMeasure (hr : 0 < r) :
    ∫ x, x ^ 2 ∂(expMeasure r) = 2 * r⁻¹ ^ 2 := by
  rw [integral_expMeasure_eq_integral_density]
  simp only [smul_eq_mul]
  have hIci0 :
      ∫ x, (exponentialPDF r x).toReal * x ^ 2 =
        ∫ x in Ici 0, (exponentialPDF r x).toReal * x ^ 2 := by
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    simp [exponentialPDF_of_neg (by simpa [mem_Ici] using hx)]
  have hIci :
      ∫ x in Ici 0, (exponentialPDF r x).toReal * x ^ 2 =
        ∫ x in Ici 0, r * (x ^ 2 * exp (-(r * x))) := by
    refine setIntegral_congr_fun measurableSet_Ici fun x hx => ?_
    rw [exponentialPDF_of_nonneg hx, ENNReal.toReal_ofReal (by positivity)]
    ring
  rw [hIci0, hIci, integral_Ici_eq_integral_Ioi, integral_const_mul]
  rw [TauCeti.integral_pow_mul_exp_neg_mul_Ioi 2 hr]
  norm_num
  field_simp [hr.ne']

/-- The variance of an exponential law with positive rate `r` is `r⁻²`. -/
@[simp]
theorem variance_id_expMeasure (hr : 0 < r) : Var[id; expMeasure r] = r⁻¹ ^ 2 := by
  let μ : Measure ℝ := expMeasure r
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_expMeasure hr
  rw [variance_eq_sub (memLp_id_expMeasure hr 2)]
  have hsq : ∫ x, (id ^ 2) x ∂μ = 2 * r⁻¹ ^ 2 := by
    simpa [id, μ] using integral_sq_expMeasure hr
  have hid : ∫ x, id x ∂μ = r⁻¹ := by
    simpa [id, μ] using integral_id_expMeasure hr
  rw [hsq, hid]
  ring

/-- The tail probability of a positive-rate exponential law. -/
lemma measure_Ioi_expMeasure (hr : 0 < r) {x : ℝ} (hx : 0 ≤ x) :
    (expMeasure r) (Ioi x) = ENNReal.ofReal (exp (-(r * x))) := by
  let _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  calc
    (expMeasure r) (Ioi x) = (cdf (expMeasure r)).measure (Ioi x) := by simp [measure_cdf]
    _ = ENNReal.ofReal (1 - cdf (expMeasure r) x) := by
      simpa using StieltjesFunction.measure_Ioi
        (f := cdf (expMeasure r))
        (ProbabilityTheory.tendsto_cdf_atTop (μ := expMeasure r)) x
    _ = ENNReal.ofReal (exp (-(r * x))) := by
      rw [cdf_expMeasure_eq hr x, ite_eq_left hx]
      ring_nf

/-- The memoryless property of a positive-rate exponential law, stated with conditional
probability: after surviving for time `s`, the chance of surviving a further time `t` is the
original tail probability at `t`. -/
theorem memoryless_expMeasure (hr : 0 < r) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    cond (expMeasure r) (Ioi s) (Ioi (s + t)) = (expMeasure r) (Ioi t) := by
  have hst : Ioi s ∩ Ioi (s + t) = Ioi (s + t) := by
    rw [Set.inter_eq_right]
    intro x hx
    exact lt_of_le_of_lt (le_add_of_nonneg_right ht) hx
  rw [cond_apply measurableSet_Ioi, hst, measure_Ioi_expMeasure hr hs,
    measure_Ioi_expMeasure hr (add_nonneg hs ht), measure_Ioi_expMeasure hr ht]
  rw [← ENNReal.ofReal_inv_of_pos (exp_pos _), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

/-- The law of the minimum of two independent exponential variables is exponential, with rate the
sum of the two rates. -/
theorem map_min_expMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hXY : IndepFun X Y P) (hX : HasLaw X (expMeasure r) P)
    (hY : HasLaw Y (expMeasure s) P) :
    P.map (fun ω => min (X ω) (Y ω)) = expMeasure (r + s) := by
  have hmin : AEMeasurable (fun ω => min (X ω) (Y ω)) P :=
    hX.aemeasurable.min hY.aemeasurable
  let _ : IsProbabilityMeasure (P.map fun ω => min (X ω) (Y ω)) :=
    Measure.isProbabilityMeasure_map hmin
  let _ : IsProbabilityMeasure (expMeasure (r + s)) :=
    isProbabilityMeasure_expMeasure (add_pos hr hs)
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hmin measurableSet_Iic,
    cdf_expMeasure_eq (add_pos hr hs) x]
  have hevent : {ω | min (X ω) (Y ω) ≤ x} =
      (X ⁻¹' Ioi x ∩ Y ⁻¹' Ioi x)ᶜ := by
    ext ω
    simp only [mem_ofPred_eq, mem_compl_iff, mem_inter_iff, mem_preimage, mem_Ioi,
      not_and_or, not_lt, min_le_iff]
  -- Normalize the mapped lower-tail event to the predicate used by `hevent`.
  change P.real {ω | min (X ω) (Y ω) ≤ x} = _
  rw [hevent, measureReal_compl₀]
  swap
  · exact (hX.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi).inter
      (hY.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi)
  rw [probReal_univ]
  have hind := hXY.measure_inter_preimage_eq_mul (Ioi x) (Ioi x)
    measurableSet_Ioi measurableSet_Ioi
  have hindReal := congr_arg ENNReal.toReal hind
  simp only [ENNReal.toReal_mul] at hindReal
  have hindReal' : P.real (X ⁻¹' Ioi x ∩ Y ⁻¹' Ioi x) =
      P.real (X ⁻¹' Ioi x) * P.real (Y ⁻¹' Ioi x) := hindReal
  have hXtail : P.real (X ⁻¹' Ioi x) = (expMeasure r).real (Ioi x) :=
    hX.measureReal_eq measurableSet_Ioi
  have hYtail : P.real (Y ⁻¹' Ioi x) = (expMeasure s).real (Ioi x) :=
    hY.measureReal_eq measurableSet_Ioi
  rw [hindReal', hXtail, hYtail]
  have hIoi : Ioi x = (Iic x)ᶜ := by ext; simp
  have htail_r : (expMeasure r).real (Ioi x) =
      1 - (if 0 ≤ x then 1 - exp (-(r * x)) else 0) := by
    let _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
    rw [hIoi, measureReal_compl measurableSet_Iic,
      probReal_univ, ← cdf_eq_real, cdf_expMeasure_eq hr x]
  have htail_s : (expMeasure s).real (Ioi x) =
      1 - (if 0 ≤ x then 1 - exp (-(s * x)) else 0) := by
    let _ : IsProbabilityMeasure (expMeasure s) := isProbabilityMeasure_expMeasure hs
    rw [hIoi, measureReal_compl measurableSet_Iic,
      probReal_univ, ← cdf_eq_real, cdf_expMeasure_eq hs x]
  rw [htail_r, htail_s]
  by_cases hx : 0 ≤ x
  · simp only [ite_eq_left hx]
    ring_nf
    rw [← exp_add]
    congr 2
  · simp only [ite_eq_right hx, sub_zero, mul_one]
    norm_num

/-- The minimum of two independent random variables with exponential laws has an exponential law
whose rate is the sum of their rates. -/
theorem hasLaw_min_expMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X Y : Ω → ℝ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hXY : IndepFun X Y P) (hX : HasLaw X (expMeasure r) P)
    (hY : HasLaw Y (expMeasure s) P) :
    HasLaw (fun ω => min (X ω) (Y ω)) (expMeasure (r + s)) P :=
  ⟨hX.aemeasurable.min hY.aemeasurable, map_min_expMeasure hr hs hXY hX hY⟩

end ProbabilityTheory
