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
* `ProbabilityTheory.measure_Ioi_expMeasure`: the tail probability.
* `ProbabilityTheory.memoryless_expMeasure`: the conditional tail is unchanged by elapsed time.
* `ProbabilityTheory.hasLaw_min_expMeasure_of_indepFun`: the minimum of independent exponentials.
-/

public section

noncomputable section

open scoped ENNReal NNReal Topology

open Filter MeasureTheory Real Set

namespace ProbabilityTheory

variable {r t : ℝ}

/-- `expMeasure r` is the Lebesgue measure weighted by the exponential density. -/
private lemma expMeasure_eq_withDensity (r : ℝ) :
    expMeasure r = volume.withDensity (exponentialPDF r) := rfl

private lemma measurable_exponentialPDF (r : ℝ) : Measurable (exponentialPDF r) := by
  unfold exponentialPDF
  exact (measurable_exponentialPDFReal r).ennreal_ofReal

/-- Every integral against `expMeasure r` is the half-line integral of the integrand weighted by
the exponential density.  This is the single reduction used by all the moment and transform
computations below. -/
private lemma integral_expMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hr : 0 ≤ r) (f : ℝ → E) :
    ∫ x, f x ∂(expMeasure r) = ∫ x in Ioi 0, (r * exp (-(r * x))) • f x := by
  rw [expMeasure_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul (measurable_exponentialPDF r)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hIci :
      ∫ x, (exponentialPDF r x).toReal • f x =
        ∫ x in Ici 0, (exponentialPDF r x).toReal • f x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp [exponentialPDF_of_neg (by simpa [mem_Ici] using hx)]).symm
  have hdens :
      ∫ x in Ici 0, (exponentialPDF r x).toReal • f x =
        ∫ x in Ici 0, (r * exp (-(r * x))) • f x :=
    setIntegral_congr_fun measurableSet_Ici fun x hx => by
      rw [exponentialPDF_of_nonneg hx,
        ENNReal.toReal_ofReal (mul_nonneg hr (exp_pos _).le)]
  rw [hIci, hdens, integral_Ici_eq_integral_Ioi]

/-- The exponential integrand is integrable exactly below the rate. -/
lemma integrable_exp_mul_expMeasure_iff (hr : 0 < r) :
    Integrable (fun x => exp (t * x)) (expMeasure r) ↔ t < r := by
  rw [expMeasure_eq_withDensity, integrable_withDensity_iff (measurable_exponentialPDF r)
    (ae_of_all _ fun x => by simp [exponentialPDF])]
  have hfun : (fun x : ℝ => exp (t * x) * (exponentialPDF r x).toReal) =
      (Set.Ici (0 : ℝ)).indicator (fun x => r * exp ((t - r) * x)) := by
    funext x
    by_cases hx : 0 ≤ x
    · have hxmem : x ∈ Ici 0 := hx
      rw [Set.indicator_of_mem hxmem, exponentialPDF_of_nonneg hx,
        ENNReal.toReal_ofReal (mul_nonneg hr.le (exp_pos _).le)]
      calc
        exp (t * x) * (r * exp (-(r * x))) = r * (exp (t * x) * exp (-(r * x))) := by ring
        _ = r * exp ((t - r) * x) := by rw [← exp_add]; congr 2; ring
    · have hxmem : x ∉ Ici 0 := hx
      rw [Set.indicator_of_notMem hxmem, exponentialPDF_of_neg (lt_of_not_ge hx)]
      simp
  rw [hfun, integrable_indicator_iff measurableSet_Ici,
    integrableOn_Ici_iff_integrableOn_Ioi, IntegrableOn,
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hr.ne')]
  simpa only [IntegrableOn, sub_lt_zero] using
    (TauCeti.integrableOn_exp_mul_Ioi_iff (a := t - r) (c := 0))

/-- The exact exponential-integrability domain of an exponential law with positive rate. -/
@[simp]
theorem integrableExpSet_fun_id_expMeasure (hr : 0 < r) :
    integrableExpSet (fun x : ℝ => x) (expMeasure r) = Set.Iio r := by
  ext t
  simpa [integrableExpSet] using
    (integrable_exp_mul_expMeasure_iff (r := r) (t := t) hr)

/-- The exact exponential-integrability domain of an exponential law with positive rate. -/
@[simp]
theorem integrableExpSet_id_expMeasure (hr : 0 < r) :
    integrableExpSet id (expMeasure r) = Set.Iio r :=
  integrableExpSet_fun_id_expMeasure hr

/-- The moment-generating function of an exponential law with positive rate. -/
theorem mgf_fun_id_expMeasure (hr : 0 < r) (ht : t < r) :
    mgf (fun x : ℝ => x) (expMeasure r) t = r / (r - t) := by
  have h : ∫ x : ℝ, exp (t * x) ∂(expMeasure r) = r / (r - t) := by
    rw [integral_expMeasure hr.le]
    have hint : ∀ x : ℝ, (r * exp (-(r * x))) • exp (t * x) = r * exp ((t - r) * x) := by
      intro x
      rw [smul_eq_mul, mul_assoc, ← exp_add]
      congr 2
      ring
    simp only [hint]
    rw [integral_const_mul, integral_exp_mul_Ioi (sub_neg.mpr ht) 0]
    simp only [mul_zero, exp_zero, neg_div, ← div_neg, neg_sub, mul_one_div]
  simpa [mgf] using h

/-- The moment-generating function of an exponential law with positive rate. -/
theorem mgf_id_expMeasure (hr : 0 < r) (ht : t < r) :
    mgf id (expMeasure r) t = r / (r - t) :=
  mgf_fun_id_expMeasure hr ht

/-- The cumulant-generating function of an exponential law with positive rate. -/
theorem cgf_id_expMeasure (hr : 0 < r) (ht : t < r) :
    cgf id (expMeasure r) t = log (r / (r - t)) := by
  rw [cgf, mgf_id_expMeasure hr ht]

/-- The characteristic function of an exponential law with positive rate. -/
theorem charFun_expMeasure (hr : 0 < r) (t : ℝ) :
    charFun (expMeasure r) t = (r : ℂ) / (r - Complex.I * t) := by
  rw [charFun_apply_real, integral_expMeasure hr.le]
  have hint : ∀ x : ℝ, (r * exp (-(r * x))) • Complex.exp (t * x * Complex.I) =
      (r : ℂ) * Complex.exp ((-(r : ℂ) + (t : ℂ) * Complex.I) * (x : ℂ)) := by
    intro x
    rw [Complex.real_smul]
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  simp only [hint]
  rw [integral_const_mul,
    integral_exp_mul_complex_Ioi (by simpa using neg_lt_zero.mpr hr) 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hden : -(r : ℂ) + (t : ℂ) * Complex.I =
      -((r : ℂ) - (t : ℂ) * Complex.I) := by ring
  rw [hden]
  simp only [div_neg]
  congr 2
  ring

/-- The identity belongs to every finite `Lᵖ` space under a positive-rate exponential law.
Stated for `fun x => x` so that it can be fed to the `variance` API below; `memLp_id_expMeasure`
is the public form. -/
private lemma memLp_fun_id_expMeasure (hr : 0 < r) (p : ℝ≥0) :
    MemLp (fun x : ℝ => x) p (expMeasure r) := by
  apply memLp_of_mem_interior_integrableExpSet
  rw [integrableExpSet_fun_id_expMeasure hr, interior_Iio]
  exact hr

/-- The identity belongs to every finite `Lᵖ` space under a positive-rate exponential law. -/
lemma memLp_id_expMeasure (hr : 0 < r) (p : ℝ≥0) : MemLp id p (expMeasure r) :=
  memLp_fun_id_expMeasure hr p

section Moments

/-- Zero lies in the interior of the exponential-integrability domain, so the
moment-generating function is differentiable there. -/
private lemma zero_mem_interior_integrableExpSet_expMeasure (hr : 0 < r) :
    (0 : ℝ) ∈ interior (integrableExpSet (fun x : ℝ => x) (expMeasure r)) := by
  rw [integrableExpSet_fun_id_expMeasure hr, interior_Iio]
  exact hr

/-- Near the origin the moment-generating function is the rational function `t ↦ r / (r - t)`. -/
private lemma mgf_eventuallyEq_expMeasure (hr : 0 < r) :
    mgf (fun x : ℝ => x) (expMeasure r) =ᶠ[𝓝 0] fun t => r / (r - t) := by
  filter_upwards [Iio_mem_nhds hr] with t ht using mgf_fun_id_expMeasure hr ht

/-- The derivative of `t ↦ r / (r - t)` below the rate. -/
private lemma hasDerivAt_div_sub (u : ℝ) (hu : u < r) :
    HasDerivAt (fun v : ℝ => r / (r - v)) (r / (r - u) ^ 2) u := by
  have hne : r - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt hu)
  have hden : HasDerivAt (fun v : ℝ => r - v) (-1) u :=
    (hasDerivAt_id' (x := u)).const_sub r
  have hval : (0 * (r - u) - r * (-1)) / (r - u) ^ 2 = r / (r - u) ^ 2 := by ring
  exact hval ▸ (hasDerivAt_const u r).fun_div hden hne

/-- The mean of an exponential law with positive rate `r` is `r⁻¹`. -/
@[simp]
theorem integral_id_expMeasure (hr : 0 < r) : ∫ x, x ∂(expMeasure r) = r⁻¹ := by
  have h := deriv_mgf_zero (X := fun x : ℝ => x) (μ := expMeasure r)
    (zero_mem_interior_integrableExpSet_expMeasure hr)
  rw [(mgf_eventuallyEq_expMeasure hr).deriv_eq,
    (hasDerivAt_div_sub 0 hr).deriv] at h
  rw [← h, sub_zero, pow_two, ← div_div, div_self hr.ne', one_div]

/-- The variance of an exponential law with positive rate `r` is `r⁻²`. -/
@[simp]
theorem variance_fun_id_expMeasure (hr : 0 < r) :
    Var[fun x : ℝ => x; expMeasure r] = r⁻¹ ^ 2 := by
  have _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have hne : r ≠ 0 := hr.ne'
  have hsq : ∫ x : ℝ, x ^ 2 ∂(expMeasure r) = 2 * r⁻¹ ^ 2 := by
    have h := iteratedDeriv_mgf_zero (X := fun x : ℝ => x) (μ := expMeasure r)
      (zero_mem_interior_integrableExpSet_expMeasure hr) 2
    have hderiv : deriv (fun v : ℝ => r / (r - v)) =ᶠ[𝓝 0] fun u : ℝ => r / (r - u) ^ 2 := by
      filter_upwards [Iio_mem_nhds hr] with u hu using (hasDerivAt_div_sub u hu).deriv
    have hsecond : HasDerivAt (fun u : ℝ => r / (r - u) ^ 2)
        ((0 * (r - 0) ^ 2 - r * (2 * (r - 0) ^ 1 * (-1))) / ((r - 0) ^ 2) ^ 2) 0 := by
      have hden_ne : (r - 0) ^ 2 ≠ 0 := pow_ne_zero _ (by simpa using hr.ne')
      have hden : HasDerivAt (fun v : ℝ => r - v) (-1) 0 :=
        (hasDerivAt_id' (x := (0 : ℝ))).const_sub r
      exact (hasDerivAt_const (0 : ℝ) r).fun_div (hden.pow 2) hden_ne
    rw [(mgf_eventuallyEq_expMeasure hr).iteratedDeriv_eq 2, iteratedDeriv_succ,
      iteratedDeriv_one, hderiv.deriv_eq, hsecond.deriv] at h
    simp only [Pi.pow_apply] at h
    rw [← h, sub_zero]
    field_simp
    ring
  rw [variance_eq_sub (memLp_fun_id_expMeasure hr 2)]
  have hid : ∫ x : ℝ, x ∂(expMeasure r) = r⁻¹ := integral_id_expMeasure hr
  simp only [Pi.pow_apply]
  rw [hsq, hid]
  ring

/-- The variance of an exponential law with positive rate `r` is `r⁻²`. -/
@[simp]
theorem variance_id_expMeasure (hr : 0 < r) : Var[id; expMeasure r] = r⁻¹ ^ 2 :=
  variance_fun_id_expMeasure hr

end Moments

/-- The real-valued tail probability of a positive-rate exponential law. -/
lemma measureReal_Ioi_expMeasure (hr : 0 < r) (x : ℝ) :
    (expMeasure r).real (Ioi x) = if 0 ≤ x then exp (-(r * x)) else 1 := by
  have _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, ← cdf_eq_real,
    cdf_expMeasure_eq hr x]
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx, ite_eq_left hx]
    ring
  · rw [ite_eq_right hx, ite_eq_right hx]
    ring

/-- The tail probability of a positive-rate exponential law. -/
lemma measure_Ioi_expMeasure (hr : 0 < r) (x : ℝ) :
    (expMeasure r) (Ioi x) = ENNReal.ofReal (if 0 ≤ x then exp (-(r * x)) else 1) := by
  have _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  rw [← measureReal_Ioi_expMeasure hr x, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- The memoryless property of a positive-rate exponential law, stated with conditional
probability: after surviving for time `s`, the chance of surviving a further time `t` is the
original tail probability at `t`. -/
theorem memoryless_expMeasure (hr : 0 < r) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    cond (expMeasure r) (Ioi s) (Ioi (s + t)) = (expMeasure r) (Ioi t) := by
  have hst : Ioi s ∩ Ioi (s + t) = Ioi (s + t) := by
    rw [Set.inter_eq_right]
    intro x hx
    exact lt_of_le_of_lt (le_add_of_nonneg_right ht) hx
  rw [cond_apply measurableSet_Ioi, hst, measure_Ioi_expMeasure hr s,
    measure_Ioi_expMeasure hr (s + t), measure_Ioi_expMeasure hr t,
    ite_eq_left hs, ite_eq_left (add_nonneg hs ht), ite_eq_left ht]
  rw [← ENNReal.ofReal_inv_of_pos (exp_pos _), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

/-- The minimum of two independent random variables with exponential laws has an exponential law
whose rate is the sum of their rates. -/
theorem hasLaw_min_expMeasure_of_indepFun {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {X Y : Ω → ℝ} {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hXY : IndepFun X Y P) (hX : HasLaw X (expMeasure r) P)
    (hY : HasLaw Y (expMeasure s) P) :
    HasLaw (fun ω => min (X ω) (Y ω)) (expMeasure (r + s)) P := by
  have hmin : AEMeasurable (fun ω => min (X ω) (Y ω)) P :=
    hX.aemeasurable.min hY.aemeasurable
  have _ : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have _ : IsProbabilityMeasure P := hX.isProbabilityMeasure
  have _ : IsProbabilityMeasure (P.map fun ω => min (X ω) (Y ω)) :=
    Measure.isProbabilityMeasure_map hmin
  have _ : IsProbabilityMeasure (expMeasure (r + s)) :=
    isProbabilityMeasure_expMeasure (add_pos hr hs)
  refine ⟨hmin, ?_⟩
  apply Measure.eq_of_cdf
  ext x
  rw [cdf_eq_real, map_measureReal_apply_of_aemeasurable hmin measurableSet_Iic,
    cdf_expMeasure_eq (add_pos hr hs) x]
  have hevent : (fun ω => min (X ω) (Y ω)) ⁻¹' Iic x =
      (X ⁻¹' Ioi x ∩ Y ⁻¹' Ioi x)ᶜ := by
    ext ω
    simp only [mem_preimage, mem_Iic, mem_compl_iff, mem_inter_iff, mem_Ioi,
      not_and_or, not_lt, min_le_iff]
  rw [hevent, measureReal_compl₀
    ((hX.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi).inter
      (hY.aemeasurable.nullMeasurableSet_preimage measurableSet_Ioi)), probReal_univ]
  have hind := hXY.measure_inter_preimage_eq_mul (Ioi x) (Ioi x)
    measurableSet_Ioi measurableSet_Ioi
  have hindReal := congr_arg ENNReal.toReal hind
  simp only [ENNReal.toReal_mul, ← measureReal_def] at hindReal
  have hXtail : P.real (X ⁻¹' Ioi x) = (expMeasure r).real (Ioi x) :=
    hX.measureReal_eq measurableSet_Ioi
  have hYtail : P.real (Y ⁻¹' Ioi x) = (expMeasure s).real (Ioi x) :=
    hY.measureReal_eq measurableSet_Ioi
  rw [hindReal, hXtail, hYtail, measureReal_Ioi_expMeasure hr x,
    measureReal_Ioi_expMeasure hs x]
  by_cases hx : 0 ≤ x
  · have hexp : -(r * x) + -(s * x) = -((r + s) * x) := by ring
    rw [ite_eq_left hx, ite_eq_left hx, ite_eq_left hx, ← exp_add, hexp]
  · rw [ite_eq_right hx, ite_eq_right hx, ite_eq_right hx]
    norm_num

end ProbabilityTheory
