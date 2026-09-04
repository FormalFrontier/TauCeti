/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.MGFAnalytic
public import TauCeti.Probability.Distributions.NegativeBinomial.Basic

import TauCeti.Probability.Distributions.Dirac

/-!
# Transforms and moments of the negative-binomial distribution

This file develops the analytic API of the real cast of the negative-binomial law. For positive
shape `r` and success probability `0 < p ≤ 1`, its exponential moments exist exactly when
`(1 - p) exp t < 1`. The resulting moment-generating, cumulant-generating, and characteristic
functions yield the usual mean `r(1 - p) / p` and variance `r(1 - p) / p²`.

The shape-zero formulas are recorded separately because that boundary law is Dirac at zero for
valid success probabilities and hence has all exponential moments; when `p < 1`, this differs from
the positive-shape domain bounded by a pole. The statements respect the totalization of
`negativeBinomialMeasure` outside its probability range.

## Main results

* `integrableExpSet_id_map_cast_negativeBinomialMeasure` gives the exact exponential-integrability
  domain for positive shape.
* `mgf_id_map_cast_negativeBinomialMeasure`, `cgf_id_map_cast_negativeBinomialMeasure`, and
  `charFun_map_cast_negativeBinomialMeasure` compute the three standard transforms.
* `integral_id_map_cast_negativeBinomialMeasure` and
  `variance_id_map_cast_negativeBinomialMeasure` compute the first two moments.

The transform formulas follow the generalized binomial series. See N. L. Johnson, A. W. Kemp,
and S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley, 2005, Chapter 5.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology

namespace TauCeti

namespace Probability

/-- The exponential integrand for the real cast of a positive-shape negative-binomial law is
integrable exactly when `(1 - p) exp t < 1`. -/
theorem integrable_exp_mul_id_map_cast_negativeBinomialMeasure_iff
    {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1) (t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x))
        ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) ↔
      (1 - p) * exp t < 1 := by
  have hcomp : ((fun x : ℝ ↦ exp (t * x)) ∘ (Nat.cast : ℕ → ℝ)) =
      fun n : ℕ ↦ exp t ^ n := by
    funext n
    rw [Function.comp_apply, mul_comm, Real.exp_nat_mul]
  rw [(MeasurableEmbedding.natCast (α := ℝ)).integrable_map_iff, hcomp,
    integrable_pow_negativeBinomialMeasure_iff hr hp hp1,
    abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hp1) (exp_nonneg t))]

/-- The exact moment-generating domain of the real cast of a positive-shape negative-binomial
law. -/
theorem integrableExpSet_id_map_cast_negativeBinomialMeasure
    {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1) :
    integrableExpSet id
        ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) =
      {t | (1 - p) * exp t < 1} := by
  ext t
  exact integrable_exp_mul_id_map_cast_negativeBinomialMeasure_iff hr hp hp1 t

/-- The moment-generating function of the real cast of a valid negative-binomial law. -/
theorem mgf_id_map_cast_negativeBinomialMeasure
    {r p : ℝ} (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1)
    {t : ℝ} (ht : (1 - p) * exp t < 1) :
    mgf id ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) t =
      Real.rpow (p / (1 - (1 - p) * exp t)) r := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [negativeBinomialMeasure_zero hp hp1, Measure.map_dirac' (by fun_prop)]
    simp [mgf_dirac']
  have habs : |(1 - p) * exp t| < 1 := by
    rwa [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hp1) (exp_nonneg t))]
  have hpgf := pgf_exp (id : ℕ → ℕ) (negativeBinomialMeasure r p) t
  rw [pgf_negativeBinomialMeasure hr hp hp1 habs] at hpgf
  rw [mgf_id_map (Measurable.of_discrete.aemeasurable :
    AEMeasurable (Nat.cast : ℕ → ℝ) (negativeBinomialMeasure r p))]
  exact hpgf.symm

/-- The cumulant-generating function of the real cast of a valid negative-binomial law. -/
theorem cgf_id_map_cast_negativeBinomialMeasure
    {r p : ℝ} (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1)
    {t : ℝ} (ht : (1 - p) * exp t < 1) :
    cgf id ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) t =
      log (Real.rpow (p / (1 - (1 - p) * exp t)) r) := by
  rw [cgf, mgf_id_map_cast_negativeBinomialMeasure hr hp hp1 ht]

private lemma zero_mem_interior_integrableExpSet {r p : ℝ}
    (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1) :
    0 ∈ interior (integrableExpSet id
      ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ))) := by
  rw [integrableExpSet_id_map_cast_negativeBinomialMeasure hr hp hp1,
    (isOpen_lt (by fun_prop : Continuous fun t : ℝ ↦ (1 - p) * exp t)
      continuous_const).interior_eq]
  simpa using hp

private lemma cgf_eventuallyEq {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1) :
    cgf id ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) =ᶠ[𝓝 0]
      fun t ↦ r * (log p - log (1 - (1 - p) * exp t)) := by
  have hdom : {t : ℝ | (1 - p) * exp t < 1} ∈ 𝓝 0 :=
    (isOpen_lt (by fun_prop : Continuous fun t : ℝ ↦ (1 - p) * exp t)
      continuous_const).mem_nhds (by simpa using hp)
  filter_upwards [hdom] with t ht
  rw [cgf_id_map_cast_negativeBinomialMeasure hr.le hp hp1 ht]
  -- Expose real-power notation so the logarithm API can normalize the local formula.
  change log ((p / (1 - (1 - p) * exp t)) ^ r) = _
  rw [Real.log_rpow (div_pos hp (sub_pos.mpr ht)),
    Real.log_div hp.ne' (sub_pos.mpr ht).ne']

private lemma hasDerivAt_cgf_formula (r p t : ℝ)
    (hden : 1 - (1 - p) * exp t ≠ 0) :
    HasDerivAt (fun u ↦ r * (log p - log (1 - (1 - p) * exp u)))
      (r * ((1 - p) * exp t / (1 - (1 - p) * exp t))) t := by
  have hd : HasDerivAt (fun u ↦ 1 - (1 - p) * exp u) (-((1 - p) * exp t)) t :=
    ((Real.hasDerivAt_exp t).const_mul (1 - p)).const_sub 1
  simpa only [Pi.sub_apply, zero_sub, neg_div, neg_neg] using
    ((hasDerivAt_const t (log p)).sub (hd.log hden)).const_mul r

private lemma hasDerivAt_cgf_formula_deriv (r p t : ℝ)
    (hden : 1 - (1 - p) * exp t ≠ 0) :
    HasDerivAt (fun u ↦ r * ((1 - p) * exp u / (1 - (1 - p) * exp u)))
      (r * ((1 - p) * exp t / (1 - (1 - p) * exp t) ^ 2)) t := by
  have hn : HasDerivAt (fun u ↦ (1 - p) * exp u) ((1 - p) * exp t) t :=
    (Real.hasDerivAt_exp t).const_mul (1 - p)
  have hd : HasDerivAt (fun u ↦ 1 - (1 - p) * exp u) (-((1 - p) * exp t)) t :=
    hn.const_sub 1
  have hraw : HasDerivAt (fun u ↦ r * ((1 - p) * exp u / (1 - (1 - p) * exp u)))
      (r * ((((1 - p) * exp t) * (1 - (1 - p) * exp t) -
        ((1 - p) * exp t) * (-((1 - p) * exp t))) /
          (1 - (1 - p) * exp t) ^ 2)) t := by
    simpa only [Pi.div_apply] using (hn.div hd hden).const_mul r
  convert hraw using 1
  ring

private theorem integral_id_map_cast_negativeBinomialMeasure_of_pos
    {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∫ x, x ∂((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) =
      r * (1 - p) / p := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1
  have hzero := zero_mem_interior_integrableExpSet hr hp hp1
  calc
    ∫ x, x ∂((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) =
        deriv (cgf id ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ))) 0 := by
      simpa only [id_eq, probReal_univ, div_one] using (deriv_cgf_zero hzero).symm
    _ = deriv (fun t ↦ r * (log p - log (1 - (1 - p) * exp t))) 0 :=
      (cgf_eventuallyEq hr hp hp1).deriv_eq
    _ = r * (1 - p) / p := by
      rw [(hasDerivAt_cgf_formula r p 0 (by simpa using hp.ne')).deriv]
      simp only [exp_zero, mul_one]
      field_simp [hp.ne']
      ring

/-- The mean of the real cast of a valid negative-binomial law is `r(1 - p) / p`. This includes
the shape-zero boundary. -/
theorem integral_id_map_cast_negativeBinomialMeasure
    {r p : ℝ} (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∫ x, x ∂((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) =
      r * (1 - p) / p := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [negativeBinomialMeasure_zero hp hp1, Measure.map_dirac' (by fun_prop)]
    norm_num
  · exact integral_id_map_cast_negativeBinomialMeasure_of_pos hr hp hp1

private theorem variance_id_map_cast_negativeBinomialMeasure_of_pos
    {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hp1 : p ≤ 1) :
    variance id ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) =
      r * (1 - p) / p ^ 2 := by
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1
  have hzero := zero_mem_interior_integrableExpSet hr hp hp1
  calc
    variance id ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) =
        iteratedDeriv 2
          (cgf id ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ))) 0 := by
      rw [iteratedDeriv_two_cgf_eq_integral hzero, deriv_cgf_zero hzero,
        variance_eq_integral (by fun_prop)]
      simp
    _ = iteratedDeriv 2 (fun t ↦ r * (log p - log (1 - (1 - p) * exp t))) 0 :=
      Filter.EventuallyEq.iteratedDeriv_eq 2 (cgf_eventuallyEq hr hp hp1)
    _ = r * (1 - p) / p ^ 2 := by
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      have hdom : {t : ℝ | (1 - p) * exp t < 1} ∈ 𝓝 0 :=
        (isOpen_lt (by fun_prop : Continuous fun t : ℝ ↦ (1 - p) * exp t)
          continuous_const).mem_nhds (by simpa using hp)
      have hfirst :
          deriv (fun t ↦ r * (log p - log (1 - (1 - p) * exp t))) =ᶠ[𝓝 0]
            fun t ↦ r * ((1 - p) * exp t / (1 - (1 - p) * exp t)) := by
        filter_upwards [hdom] with t ht
        exact (hasDerivAt_cgf_formula r p t (sub_pos.mpr ht).ne').deriv
      rw [hfirst.deriv_eq,
        (hasDerivAt_cgf_formula_deriv r p 0 (by simpa using hp.ne')).deriv]
      simp only [exp_zero, mul_one]
      field_simp [hp.ne']
      ring

/-- The variance of the real cast of a valid negative-binomial law is `r(1 - p) / p²`. This
includes the shape-zero boundary. -/
theorem variance_id_map_cast_negativeBinomialMeasure
    {r p : ℝ} (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1) :
    variance id ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) =
      r * (1 - p) / p ^ 2 := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [negativeBinomialMeasure_zero hp hp1, Measure.map_dirac' (by fun_prop)]
    norm_num
  · exact variance_id_map_cast_negativeBinomialMeasure_of_pos hr hp hp1

/-- The characteristic function of the real cast of a valid negative-binomial law. -/
theorem charFun_map_cast_negativeBinomialMeasure
    {r p : ℝ} (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1) (t : ℝ) :
    charFun ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) t =
      ((p : ℂ) /
        (1 - (1 - (p : ℂ)) * Complex.exp (Complex.I * t))) ^ (r : ℂ) := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [negativeBinomialMeasure_zero hp hp1, Measure.map_dirac' (by fun_prop)]
    simp
  let _ := isProbabilityMeasure_negativeBinomialMeasure hr.le hp hp1
  -- The binomial-series argument lies in the open unit disk, including at `p = 1`.
  let q : ℂ := (1 - (p : ℂ)) * Complex.exp (Complex.I * t)
  have hq_norm : ‖q‖ < 1 := by
    -- Unfold the local series argument so norm multiplicativity applies to its two factors.
    change ‖(1 - (p : ℂ)) * Complex.exp (Complex.I * t)‖ < 1
    rw [norm_mul, Complex.norm_exp]
    have him : (Complex.I * (t : ℂ)).re = 0 := by simp
    rw [him, Real.exp_zero, mul_one]
    simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ 1 - p)] using sub_lt_self 1 hp
  have hsum :=
    (hasSum_multichoose_mul_geometric_complex_of_norm_lt_one (r := (r : ℂ)) hq_norm).mul_right
      (Real.rpow p r : ℂ)
  have hmultichoose (n : ℕ) :
      Ring.multichoose (r : ℂ) n = ((Ring.multichoose r n : ℝ) : ℂ) :=
    (Ring.map_multichoose Complex.ofRealHom r n).symm
  simp_rw [hmultichoose] at hsum
  -- The denominator lies in the right half-plane, so its principal logarithm avoids the cut.
  have hw_re : 0 < (1 - q).re := by
    have hq_re : q.re ≤ ‖q‖ := Complex.re_le_norm q
    -- Normalize the real part of the denominator to the scalar inequality implied by `‖q‖ < 1`.
    change 0 < 1 - q.re
    linarith
  have hw_ne : 1 - q ≠ 0 := by
    intro h
    rw [h] at hw_re
    norm_num at hw_re
  have hw_arg : (1 - q).arg ≠ Real.pi := by
    intro h
    exact (not_lt_of_ge hw_re.le) (Complex.arg_eq_pi_iff.mp h).1
  have hratio_ne : (p : ℂ) / (1 - q) ≠ 0 :=
    div_ne_zero (by exact_mod_cast hp.ne') hw_ne
  -- The branch information above justifies combining the two principal complex powers.
  have hvalue :
      (1 / (1 - q) ^ (r : ℂ)) * (Real.rpow p r : ℂ) =
        ((p : ℂ) / (1 - q)) ^ (r : ℂ) := by
    have hp_ne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have hratio : (p : ℂ) / (1 - q) = (1 - q)⁻¹ * (p : ℂ) := by ring
    rw [Complex.cpow_def_of_ne_zero hratio_ne, hratio,
      Complex.log_mul_ofReal p hp _ (inv_ne_zero hw_ne), Complex.log_inv _ hw_arg,
      Complex.ofReal_log hp.le, add_mul, Complex.exp_add, neg_mul, Complex.exp_neg,
      ← Complex.cpow_def_of_ne_zero hp_ne, ← Complex.cpow_def_of_ne_zero hw_ne,
      ← Complex.ofReal_cpow hp.le]
    -- Align the real-power notation with the coercion lemma used in the preceding rewrite.
    simp only [show Real.rpow p r = p ^ r from rfl]
    ring_nf
  have hweight_ne_top (k : ℕ) : negativeBinomialWeight r p k ≠ ⊤ := by
    rw [← negativeBinomialMeasure_singleton hr.le hp hp1]
    exact measure_ne_top _ _
  -- Expand the discrete integral and identify it termwise with the complex binomial series.
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop),
    negativeBinomialMeasure_eq_sum_dirac hr.le hp hp1,
    integral_sum_dirac hweight_ne_top]
  simp only [Complex.real_smul]
  dsimp only [q] at hsum hvalue
  rw [← hvalue, ← hsum.tsum_eq]
  congr with k
  have hexp : Complex.exp (((t : ℂ) * ((k : ℝ) : ℂ)) * Complex.I) =
      Complex.exp (Complex.I * t) ^ k := by
    have hmul : ((t : ℂ) * ((k : ℝ) : ℂ)) * Complex.I = k * (Complex.I * t) := by
      push_cast
      ring
    rw [hmul, Complex.exp_nat_mul]
  rw [negativeBinomialWeight_toReal hr.le hp.le hp1,
    negativeBinomialWeightReal_eq_coeff hr k, hexp]
  rw [mul_pow]
  push_cast
  ring

private theorem negativeBinomialMeasure_zero_eq_ite (p : ℝ) :
    negativeBinomialMeasure 0 p =
      if 0 < p ∧ p ≤ 1 then Measure.dirac 0 else 0 := by
  by_cases h : 0 < p ∧ p ≤ 1
  · rw [ite_eq_left h, negativeBinomialMeasure_zero h.1 h.2]
  · rw [ite_eq_right h]
    apply negativeBinomialMeasure_eq_zero_of_invalid
    simpa using h

/-- At shape zero, the real cast of a negative-binomial law has every exponential moment for all
success parameters, including those where the totalized measure is zero. -/
@[simp]
theorem integrableExpSet_id_map_cast_negativeBinomialMeasure_zero (p : ℝ) :
    integrableExpSet id ((negativeBinomialMeasure 0 p).map (Nat.cast : ℕ → ℝ)) = univ := by
  rw [negativeBinomialMeasure_zero_eq_ite]
  split_ifs
  · simp
  · simp [integrableExpSet]

/-- At shape zero, the moment-generating function is one for valid success probabilities and zero
for the totalized zero measure outside that range. -/
@[simp]
theorem mgf_id_map_cast_negativeBinomialMeasure_zero (p t : ℝ) :
    mgf id ((negativeBinomialMeasure 0 p).map (Nat.cast : ℕ → ℝ)) t =
      if 0 < p ∧ p ≤ 1 then 1 else 0 := by
  rw [negativeBinomialMeasure_zero_eq_ite]
  split_ifs <;> simp [mgf_dirac']

/-- At shape zero, the cumulant-generating function is identically zero for every success
parameter. -/
@[simp]
theorem cgf_id_map_cast_negativeBinomialMeasure_zero (p t : ℝ) :
    cgf id ((negativeBinomialMeasure 0 p).map (Nat.cast : ℕ → ℝ)) t = 0 := by
  rw [cgf, negativeBinomialMeasure_zero_eq_ite]
  split_ifs <;> simp [mgf_dirac']

/-- At shape zero, the real cast of a negative-binomial law has mean zero for every success
parameter. -/
@[simp]
theorem integral_id_map_cast_negativeBinomialMeasure_zero (p : ℝ) :
    ∫ x, x ∂((negativeBinomialMeasure 0 p).map (Nat.cast : ℕ → ℝ)) = 0 := by
  rw [negativeBinomialMeasure_zero_eq_ite]
  split_ifs <;> simp

/-- At shape zero, the real cast of a negative-binomial law has variance zero for every success
parameter. -/
@[simp]
theorem variance_id_map_cast_negativeBinomialMeasure_zero (p : ℝ) :
    variance id ((negativeBinomialMeasure 0 p).map (Nat.cast : ℕ → ℝ)) = 0 := by
  rw [negativeBinomialMeasure_zero_eq_ite]
  split_ifs <;> simp

/-- At shape zero, the characteristic function is one for valid success probabilities and zero
for the totalized zero measure outside that range. -/
@[simp]
theorem charFun_map_cast_negativeBinomialMeasure_zero (p t : ℝ) :
    charFun ((negativeBinomialMeasure 0 p).map (Nat.cast : ℕ → ℝ)) t =
      if 0 < p ∧ p ≤ 1 then 1 else 0 := by
  rw [negativeBinomialMeasure_zero_eq_ite]
  split_ifs <;> simp

/-- A real random variable with a valid negative-binomial law has mean `r(1 - p) / p`. -/
theorem integral_of_hasLaw_map_cast_negativeBinomialMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {r p : ℝ}
    (hX : HasLaw X ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) P)
    (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1) :
    P[X] = r * (1 - p) / p := by
  rw [hX.integral_eq, integral_id_map_cast_negativeBinomialMeasure hr hp hp1]

/-- A real random variable with a valid negative-binomial law has variance `r(1 - p) / p²`. -/
theorem variance_of_hasLaw_map_cast_negativeBinomialMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {r p : ℝ}
    (hX : HasLaw X ((negativeBinomialMeasure r p).map (Nat.cast : ℕ → ℝ)) P)
    (hr : 0 ≤ r) (hp : 0 < p) (hp1 : p ≤ 1) :
    variance X P = r * (1 - p) / p ^ 2 := by
  rw [hX.variance_eq, variance_id_map_cast_negativeBinomialMeasure hr hp hp1]

end Probability

end TauCeti

end
