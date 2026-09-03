/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

import TauCeti.Analysis.SpecialFunctions.Beta
public import TauCeti.Probability.Density
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Probability.Distributions.Cauchy
public import Mathlib.Probability.Moments.Variance
import TauCeti.Analysis.SpecialFunctions.Gamma
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Student's t distribution

Student's t law with `ν` degrees of freedom is the symmetric law on the line with density
proportional to `(1 + x ^ 2 / ν) ^ (-(ν + 1) / 2)`. This file defines it, proves that it is a
probability measure for `0 < ν`, identifies it as a `MeasureTheory.HasPDF` law with that density,
records its reflection symmetry, establishes the sharp first- and second-moment thresholds and
formulas, and identifies the one degree of freedom member of the family with the standard Cauchy
law.

**Boundary.** The number of degrees of freedom must be positive for the density to normalize, so
both `studentTPDFReal` and `studentTMeasure` are *defined* to vanish for `ν ≤ 0`
(`studentTMeasure_of_nonpos`); every formula describing the probability law carries `0 < ν` as a
hypothesis.

## Main definitions

* `TauCeti.Probability.studentTPDFReal` — the real-valued density;
* `TauCeti.Probability.studentTPDF` — its `ℝ≥0∞`-valued companion;
* `TauCeti.Probability.studentTMeasure` — the law, as `volume.withDensity studentTPDF`.

## Main results

* `isProbabilityMeasure_studentTMeasure` — it is a probability measure when `0 < ν`;
* `hasPDF_of_hasLaw_studentTMeasure`, `pdf_eq_studentTPDF_of_hasLaw_studentTMeasure` and
  `rnDeriv_studentTMeasure` — the `HasPDF` bridge, the density, and the Radon–Nikodym derivative;
* `studentTMeasure_map_neg` — the law is invariant under reflection in the origin;
* `integrable_id_studentTMeasure_iff` and `integral_id_studentTMeasure` — within the nondegenerate
  family the mean exists exactly when `1 < ν`, while its Bochner integral is zero for every
  parameter;
* `integrable_sq_studentTMeasure_iff`, `integral_sq_studentTMeasure` and
  `variance_id_studentTMeasure` — the second moment exists exactly when `2 < ν`, and then both it
  and the variance equal `ν / (ν - 2)`;
* `studentTMeasure_one` — one degree of freedom gives the standard Cauchy law
  `ProbabilityTheory.cauchyMeasure 0 1`;
* `measurable_studentTMeasure` — the family is measurable in its parameter, so it can be used as a
  kernel.

## Implementation

The whole analytic content is the normalization. Scaling by `√ν` with
`MeasureTheory.integral_comp_mul_left` reduces the total mass of `(1 + x ^ 2 / ν) ^ (-(ν + 1) / 2)`
to that of the Cauchy-type kernel `(1 + x ^ 2) ^ (-(ν + 1) / 2)`, which is
`TauCeti.integral_one_add_sq_rpow`: the value `Β(1 / 2, ν / 2)` of Euler's second beta integral.
Writing that value as a quotient of Gamma values cancels the normalizing constant exactly. The
positive moment results reduce to the same beta integral, while the sharp failures use a positive
multiple of `x⁻¹` as a lower bound on the corresponding weighted density in the right tail.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, the **Student's t** target.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 28.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

open scoped ENNReal Real

namespace TauCeti

namespace Probability

variable {ν x : ℝ}

/-! ### The density -/

/-- The density of Student's t law with `ν` degrees of freedom, as a real-valued function.

For `ν ≤ 0` there is no such law and the density is `0`. -/
def studentTPDFReal (ν x : ℝ) : ℝ :=
  if 0 < ν then
    Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)) *
      (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))
  else 0

/-- The density of Student's t law, as a function valued in `ℝ≥0∞`. -/
def studentTPDF (ν x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (studentTPDFReal ν x)

/-- Outside the valid parameter range the density vanishes. -/
@[simp]
theorem studentTPDFReal_of_nonpos (hν : ν ≤ 0) (x : ℝ) : studentTPDFReal ν x = 0 := by
  rw [studentTPDFReal, ite_eq_right (not_lt.mpr hν)]

/-- For a positive number of degrees of freedom the density is the Student t formula. -/
@[simp]
theorem studentTPDFReal_of_pos (hν : 0 < ν) (x : ℝ) :
    studentTPDFReal ν x =
      Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)) *
        (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := by
  rw [studentTPDFReal, ite_eq_left hν]

/-- For a positive number of degrees of freedom the `ℝ≥0∞`-valued density is the Student t
formula. -/
@[simp]
theorem studentTPDF_of_pos (hν : 0 < ν) (x : ℝ) :
    studentTPDF ν x = ENNReal.ofReal
      (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)) *
        (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
  rw [studentTPDF, studentTPDFReal_of_pos hν]

/-- Outside the valid parameter range the `ℝ≥0∞`-valued density vanishes. -/
@[simp]
theorem studentTPDF_of_nonpos (hν : ν ≤ 0) (x : ℝ) : studentTPDF ν x = 0 := by
  rw [studentTPDF, studentTPDFReal_of_nonpos hν, ENNReal.ofReal_zero]

/-- The normalizing constant of Student's t law is positive. -/
theorem studentT_const_pos (hν : 0 < ν) :
    0 < Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)) :=
  div_pos (Real.Gamma_pos_of_pos (by linarith))
    (mul_pos (Real.sqrt_pos.mpr (by positivity)) (Real.Gamma_pos_of_pos (by linarith)))

/-- For a positive number of degrees of freedom the density is strictly positive everywhere: the
Student t law has no vanishing tail. -/
theorem studentTPDFReal_pos (hν : 0 < ν) (x : ℝ) : 0 < studentTPDFReal ν x := by
  rw [studentTPDFReal_of_pos hν]
  exact mul_pos (studentT_const_pos hν) (Real.rpow_pos_of_pos (by positivity) _)

/-- The Student t density is nonnegative at every parameter, valid or not. -/
theorem studentTPDFReal_nonneg (ν x : ℝ) : 0 ≤ studentTPDFReal ν x := by
  rcases lt_or_ge 0 ν with hν | hν
  · exact (studentTPDFReal_pos hν x).le
  · rw [studentTPDFReal_of_nonpos hν]

/-- The two Student t densities agree under `ENNReal.toReal`; the density is never infinite. -/
@[simp]
theorem toReal_studentTPDF (ν x : ℝ) : (studentTPDF ν x).toReal = studentTPDFReal ν x :=
  ENNReal.toReal_ofReal (studentTPDFReal_nonneg ν x)

/-- The Student t density is even in the sample point. -/
@[simp]
theorem studentTPDFReal_neg (ν x : ℝ) : studentTPDFReal ν (-x) = studentTPDFReal ν x := by
  rw [studentTPDFReal, studentTPDFReal, neg_sq]

/-- The `ℝ≥0∞`-valued Student t density is even in the sample point. -/
@[simp]
theorem studentTPDF_neg (ν x : ℝ) : studentTPDF ν (-x) = studentTPDF ν x := by
  rw [studentTPDF, studentTPDF, studentTPDFReal_neg]

/-- The real-valued Student t density is measurable. -/
@[fun_prop]
theorem measurable_studentTPDFReal (ν : ℝ) : Measurable (studentTPDFReal ν) := by
  by_cases hν : 0 < ν
  · have h : studentTPDFReal ν = fun y =>
        Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)) *
          Real.exp (Real.log (1 + y ^ 2 / ν) * (-((ν + 1) / 2))) := by
      funext y
      rw [studentTPDFReal_of_pos hν, Real.rpow_def_of_pos (by positivity)]
    rw [h]
    fun_prop
  · have h : studentTPDFReal ν = fun _ => (0 : ℝ) :=
      funext fun y => studentTPDFReal_of_nonpos (not_lt.mp hν) y
    rw [h]
    exact measurable_const

/-- The `ℝ≥0∞`-valued Student t density is measurable. -/
@[fun_prop]
theorem measurable_studentTPDF (ν : ℝ) : Measurable (studentTPDF ν) :=
  (measurable_studentTPDFReal ν).ennreal_ofReal

/-! ### The measure and its total mass -/

/-- Student's t probability measure with `ν` degrees of freedom.

For `ν ≤ 0` this is the zero measure, not a probability measure; see
`studentTMeasure_of_nonpos`. -/
def studentTMeasure (ν : ℝ) : Measure ℝ :=
  volume.withDensity (studentTPDF ν)

/-- Outside the valid parameter range Student's t law is the zero measure. -/
@[simp]
theorem studentTMeasure_of_nonpos (hν : ν ≤ 0) : studentTMeasure ν = 0 := by
  have h : studentTPDF ν = 0 := by
    funext y
    rw [studentTPDF_of_nonpos hν]
    rfl
  rw [studentTMeasure, h, withDensity_zero]

/-- The Student t density is integrable on the whole line for every parameter. -/
theorem integrable_studentTPDFReal (ν : ℝ) : Integrable (studentTPDFReal ν) := by
  by_cases hν : 0 < ν
  · have hs : (1 : ℝ) / 2 < (ν + 1) / 2 := by linarith
    have h := (integrable_one_add_sq_div_rpow hν hs).const_mul
      (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)))
    exact (integrable_congr (ae_of_all _ fun y => studentTPDFReal_of_pos hν y)).mpr h
  · have h : studentTPDFReal ν = fun _ => (0 : ℝ) :=
      funext fun y => studentTPDFReal_of_nonpos (not_lt.mp hν) y
    rw [h]
    exact integrable_zero ℝ ℝ volume

/-- The Student t density integrates to `1`. -/
theorem integral_studentTPDFReal (hν : 0 < ν) : ∫ x, studentTPDFReal ν x = 1 := by
  have hs : (1 : ℝ) / 2 < (ν + 1) / 2 := by linarith
  have hG1 : Real.Gamma ((ν + 1) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hG2 : Real.Gamma (ν / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hsq : √(ν * π) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have hsub : (ν + 1) / 2 - 1 / 2 = ν / 2 := by ring
  have hsum : (1 : ℝ) / 2 + ν / 2 = (ν + 1) / 2 := by ring
  simp_rw [studentTPDFReal_of_pos hν]
  rw [integral_const_mul, integral_one_add_sq_div_rpow hν hs, hsub, ProbabilityTheory.beta,
    Real.Gamma_one_half_eq, hsum, Real.sqrt_mul hν.le]
  field_simp

/-- The `ℝ≥0∞`-valued Student t density has total mass `1`. -/
theorem lintegral_studentTPDF_eq_one (hν : 0 < ν) : ∫⁻ x, studentTPDF ν x = 1 := by
  simp_rw [studentTPDF]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_studentTPDFReal ν)
      (ae_of_all _ fun y => studentTPDFReal_nonneg ν y),
    integral_studentTPDFReal hν, ENNReal.ofReal_one]

/-- **For a positive number of degrees of freedom Student's t law is a probability measure.** -/
theorem isProbabilityMeasure_studentTMeasure (hν : 0 < ν) :
    IsProbabilityMeasure (studentTMeasure ν) := by
  constructor
  rw [studentTMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, lintegral_studentTPDF_eq_one hν]

/-! ### Absolute continuity -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A random variable with a Student t law has a density. -/
theorem hasPDF_of_hasLaw_studentTMeasure (hX : HasLaw X (studentTMeasure ν) P) :
    HasPDF X P volume :=
  hasPDF_of_hasLaw_withDensity (measurable_studentTPDF ν).aemeasurable hX

/-- The density of a Student t law is `studentTPDF`. -/
theorem pdf_eq_studentTPDF_of_hasLaw_studentTMeasure (hX : HasLaw X (studentTMeasure ν) P) :
    pdf X P volume =ᵐ[volume] studentTPDF ν :=
  pdf_eq_of_hasLaw_withDensity (measurable_studentTPDF ν).aemeasurable hX

/-- The Radon–Nikodym derivative of a Student t law against Lebesgue measure is `studentTPDF`. -/
theorem rnDeriv_studentTMeasure (ν : ℝ) :
    (studentTMeasure ν).rnDeriv volume =ᵐ[volume] studentTPDF ν :=
  Measure.rnDeriv_withDensity volume (measurable_studentTPDF ν)

/-! ### Symmetry -/

/-- Student's t law is invariant under reflection in the origin: its density is even and Lebesgue
measure is reflection invariant. -/
theorem studentTMeasure_map_neg (ν : ℝ) :
    (studentTMeasure ν).map (fun x => -x) = studentTMeasure ν := by
  refine Measure.ext fun t ht => ?_
  have hpre : MeasurableSet ((fun x : ℝ => -x) ⁻¹' t) := ht.preimage measurable_neg
  rw [Measure.map_apply measurable_neg ht, studentTMeasure,
    withDensity_apply _ hpre, withDensity_apply _ ht]
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage_emb
    (Homeomorph.neg ℝ).measurableEmbedding (studentTPDF ν) t
  simpa only [studentTPDF_neg] using h

/-! ### Moments -/

private lemma studentTKernel_id_factor (hν : 0 < ν) (x : ℝ) :
    (x / √(1 + x ^ 2 / ν)) * (1 + x ^ 2 / ν) ^ (-(ν / 2)) =
      x * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := by
  have hbase : 0 < 1 + x ^ 2 / ν := by positivity
  rw [Real.sqrt_eq_rpow, div_eq_mul_inv, ← Real.rpow_neg hbase.le, mul_assoc,
    ← Real.rpow_add hbase]
  congr 2
  ring

private lemma integrable_id_mul_studentTKernel (hν : 1 < ν) :
    Integrable (fun x : ℝ =>
      x * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
  have hνpos : 0 < ν := lt_trans zero_lt_one hν
  have hkernel : Integrable (fun x : ℝ => (1 + x ^ 2 / ν) ^ (-(ν / 2))) :=
    integrable_one_add_sq_div_rpow hνpos (by linarith)
  have hbounded : ∀ x : ℝ, ‖x / √(1 + x ^ 2 / ν)‖ ≤ √ν := by
    intro x
    have hbase : 0 < 1 + x ^ 2 / ν := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (Real.sqrt_pos.mpr hbase),
      div_le_iff₀ (Real.sqrt_pos.mpr hbase)]
    have hsq : |x| ^ 2 ≤ (√ν * √(1 + x ^ 2 / ν)) ^ 2 := by
      rw [sq_abs, mul_pow, Real.sq_sqrt hνpos.le, Real.sq_sqrt hbase.le]
      have hmul : ν * (1 + x ^ 2 / ν) = ν + x ^ 2 := by field_simp
      rw [hmul]
      linarith
    have hprod_nonneg : 0 ≤ √ν * √(1 + x ^ 2 / ν) :=
      mul_nonneg (Real.sqrt_nonneg ν) (Real.sqrt_nonneg (1 + x ^ 2 / ν))
    nlinarith [abs_nonneg x]
  have hproduct : Integrable (fun x : ℝ =>
      (x / √(1 + x ^ 2 / ν)) * (1 + x ^ 2 / ν) ^ (-(ν / 2))) :=
    hkernel.bdd_mul (measurable_id.div
      (Real.continuous_sqrt.measurable.comp (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ hbounded)
  exact hproduct.congr (ae_of_all _ fun x => studentTKernel_id_factor hνpos x)

private theorem integrable_id_studentTMeasure_of_one_lt (hν : 1 < ν) :
    Integrable id (studentTMeasure ν) := by
  have hνpos : 0 < ν := lt_trans zero_lt_one hν
  rw [studentTMeasure, integrable_withDensity_iff (measurable_studentTPDF ν)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [id_eq, toReal_studentTPDF, studentTPDFReal_of_pos hνpos]
  have h := (integrable_id_mul_studentTKernel hν).const_mul
    (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)))
  exact h.congr (ae_of_all _ fun x => by ring)

private theorem studentTPDFReal_tail_lower_bound (hν : 0 < ν) (q : ℕ)
    (hνq : ν ≤ (q : ℝ)) :
    ∀ᶠ x : ℝ in atTop,
      (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2))) *
          (1 + ν⁻¹) ^ (-(((q : ℝ) + 1) / 2)) * x⁻¹ ≤
        x ^ q * studentTPDFReal ν x := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  -- On the right tail, compare the kernel base with a constant multiple of `x²`, then use
  -- `ν ≤ q` to compare the two negative exponents.
  have hbase_pos : 0 < 1 + x ^ 2 / ν := by positivity
  have hbase_one : 1 ≤ 1 + x ^ 2 / ν :=
    le_add_of_nonneg_right (div_nonneg (sq_nonneg x) hν.le)
  have hconst_pos : 0 < 1 + ν⁻¹ := by positivity
  have hdensity_pos :
      0 < Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)) :=
    studentT_const_pos hν
  have hbase_le : 1 + x ^ 2 / ν ≤ (1 + ν⁻¹) * x ^ 2 := by
    have hx_sq : 1 ≤ x ^ 2 := (one_le_sq_iff₀ hx0.le).2 hx
    rw [div_eq_mul_inv]
    nlinarith [mul_nonneg (zero_le_one.trans hx_sq) (inv_nonneg.mpr hν.le)]
  have hexp : -(((q : ℝ) + 1) / 2) ≤ -((ν + 1) / 2) := by
    norm_num at hνq ⊢
    linarith
  have hpow₁ : (1 + x ^ 2 / ν) ^ (-(((q : ℝ) + 1) / 2)) ≤
      (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) :=
    Real.rpow_le_rpow_of_exponent_le hbase_one hexp
  have hpow₂ : ((1 + ν⁻¹) * x ^ 2) ^ (-(((q : ℝ) + 1) / 2)) ≤
      (1 + x ^ 2 / ν) ^ (-(((q : ℝ) + 1) / 2)) :=
    Real.rpow_le_rpow_of_nonpos hbase_pos hbase_le (by
      have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
      linarith)
  -- Splitting the comparison kernel exposes exactly `x ^ q * x ^ (-(q + 1)) = x⁻¹`.
  have hsplit : ((1 + ν⁻¹) * x ^ 2) ^ (-(((q : ℝ) + 1) / 2)) =
      (1 + ν⁻¹) ^ (-(((q : ℝ) + 1) / 2)) * x ^ (-((q : ℝ) + 1)) := by
    rw [Real.mul_rpow hconst_pos.le (sq_nonneg x), ← Real.rpow_two x,
      ← Real.rpow_mul hx0.le]
    congr 2
    ring
  have hxpow : x ^ (q : ℝ) * x ^ (-((q : ℝ) + 1)) = x⁻¹ := by
    rw [← Real.rpow_add hx0]
    have hexponent : (q : ℝ) + -((q : ℝ) + 1) = -1 := by ring
    rw [hexponent, Real.rpow_neg_one]
  rw [studentTPDFReal_of_pos hν]
  calc
    (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2))) *
          (1 + ν⁻¹) ^ (-(((q : ℝ) + 1) / 2)) * x⁻¹ =
        (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2))) *
          (x ^ q * ((1 + ν⁻¹) * x ^ 2) ^ (-(((q : ℝ) + 1) / 2))) := by
            rw [hsplit, ← Real.rpow_natCast x q, ← hxpow]
            ring
    _ ≤ (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2))) *
          (x ^ q * (1 + x ^ 2 / ν) ^ (-(((q : ℝ) + 1) / 2))) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hpow₂ (pow_nonneg hx0.le q)) hdensity_pos.le
    _ ≤ x ^ q *
          (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)) *
            (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
            calc
              _ ≤ (Real.Gamma ((ν + 1) / 2) /
                    (√(ν * π) * Real.Gamma (ν / 2))) *
                  (x ^ q * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hpow₁ (pow_nonneg hx0.le q))
                  hdensity_pos.le
              _ = _ := by ring
    _ = _ := by ring

private theorem not_integrable_pow_studentTMeasure (hν : 0 < ν) (q : ℕ)
    (hνq : ν ≤ (q : ℝ)) :
    ¬ Integrable (fun x : ℝ => x ^ q) (studentTMeasure ν) := by
  intro hint
  rw [studentTMeasure, integrable_withDensity_iff (measurable_studentTPDF ν)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hint
  simp_rw [toReal_studentTPDF] at hint
  let c : ℝ :=
    (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2))) *
      (1 + ν⁻¹) ^ (-(((q : ℝ) + 1) / 2))
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hbound : ∀ᶠ x : ℝ in atTop,
      c * x⁻¹ ≤ x ^ q * studentTPDFReal ν x := by
    simpa only [c] using studentTPDFReal_tail_lower_bound hν q hνq
  obtain ⟨a, ha⟩ := eventually_atTop.mp
    (hbound.and (eventually_ge_atTop (1 : ℝ)))
  have hinv : IntegrableOn (fun x : ℝ => x⁻¹) (Ioi a) volume := by
    refine Integrable.mono' (hint.const_mul c⁻¹).integrableOn (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rcases ha x hx.le with ⟨hpdf, hx1⟩
    have hx0 : 0 < x := zero_lt_one.trans_le hx1
    calc
      ‖x⁻¹‖ = x⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
      _ = c⁻¹ * (c * x⁻¹) := by field_simp
      _ ≤ c⁻¹ * (x ^ q * studentTPDFReal ν x) :=
        mul_le_mul_of_nonneg_left hpdf (inv_nonneg.mpr hc.le)
  exact not_integrableOn_Ioi_inv hinv

/-- The identity is integrable under a nondegenerate Student t law exactly when the number of
degrees of freedom exceeds one. -/
@[simp]
theorem integrable_id_studentTMeasure_iff (hν : 0 < ν) :
    Integrable id (studentTMeasure ν) ↔ 1 < ν := by
  constructor
  · intro hint
    by_contra h
    have hnot := not_integrable_pow_studentTMeasure hν 1 (by
      simpa using (not_lt.mp h : ν ≤ 1))
    have hint' : Integrable (fun x : ℝ => x) (studentTMeasure ν) := by
      refine hint.congr (ae_of_all _ fun x => ?_)
      rfl
    apply hnot
    simpa only [pow_one] using hint'
  · exact integrable_id_studentTMeasure_of_one_lt

/-- The Bochner integral of the identity under a Student t measure is zero for every parameter,
including by convention when the identity is not integrable. -/
@[simp]
theorem integral_id_studentTMeasure (ν : ℝ) :
    ∫ x, x ∂studentTMeasure ν = 0 := by
  by_cases hint : Integrable (fun x : ℝ => x) (studentTMeasure ν)
  · have hpres : MeasurePreserving (fun x : ℝ => -x)
        (studentTMeasure ν) (studentTMeasure ν) :=
      ⟨measurable_neg, studentTMeasure_map_neg ν⟩
    have hrefl : ∫ x, -x ∂studentTMeasure ν = ∫ x, x ∂studentTMeasure ν := by
      simpa only [Function.comp_apply, id_eq] using
        hpres.integral_comp (Homeomorph.neg ℝ).measurableEmbedding id
    have hneg : Integrable (fun x : ℝ => -x) (studentTMeasure ν) := hint.neg
    have hsum : (∫ x, x ∂studentTMeasure ν) + ∫ x, -x ∂studentTMeasure ν = 0 := by
      rw [← integral_add hint hneg]
      simp
    linarith
  · exact integral_undef hint

private lemma studentTKernel_sq (hν : 0 < ν) (x : ℝ) :
    x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) =
      ν * ((1 + x ^ 2 / ν) ^ (-((ν - 1) / 2)) -
        (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
  have hbase : 0 < 1 + x ^ 2 / ν := by positivity
  have hshift :
      (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2)) =
        (1 + x ^ 2 / ν) * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := by
    calc
      (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2)) =
          (1 + x ^ 2 / ν) ^ (1 + -((ν + 1) / 2)) := by
        apply congrArg (fun t : ℝ => (1 + x ^ 2 / ν) ^ t)
        ring
      _ = (1 + x ^ 2 / ν) ^ 1 *
          (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := Real.rpow_add hbase _ _
      _ = (1 + x ^ 2 / ν) *
          (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := by rw [Real.rpow_one]
  rw [hshift]
  field_simp
  ring

private lemma integrable_sq_mul_studentTKernel (hν : 2 < ν) :
    Integrable (fun x : ℝ =>
      x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
  have hνpos : 0 < ν := lt_trans zero_lt_two hν
  have hshift : Integrable (fun x : ℝ =>
      (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2))) :=
    integrable_one_add_sq_div_rpow hνpos (by linarith)
  have hbase : Integrable (fun x : ℝ =>
      (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) :=
    integrable_one_add_sq_div_rpow hνpos (by linarith)
  exact ((hshift.sub hbase).const_mul ν).congr
    (ae_of_all _ fun x => (studentTKernel_sq hνpos x).symm)

private theorem integrable_sq_studentTMeasure_of_two_lt (hν : 2 < ν) :
    Integrable (fun x : ℝ => x ^ 2) (studentTMeasure ν) := by
  have hνpos : 0 < ν := lt_trans zero_lt_two hν
  rw [studentTMeasure, integrable_withDensity_iff (measurable_studentTPDF ν)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [toReal_studentTPDF, studentTPDFReal_of_pos hνpos]
  have h := (integrable_sq_mul_studentTKernel hν).const_mul
    (Real.Gamma ((ν + 1) / 2) / (√(ν * π) * Real.Gamma (ν / 2)))
  exact h.congr (ae_of_all _ fun x => by ring)

private lemma beta_sub_beta_add_one (hν : 2 < ν) :
    beta (1 / 2) ((ν - 2) / 2) - beta (1 / 2) (ν / 2) =
      beta (3 / 2) ((ν - 2) / 2) := by
  let b := (ν - 2) / 2
  have hb : b ≠ 0 := by
    dsimp [b]
    linarith
  have hsum : b + 1 / 2 ≠ 0 := by
    dsimp [b]
    linarith
  have hright : beta (1 / 2) (b + 1) =
      b / (b + 1 / 2) * beta (1 / 2) b := by
    rw [beta_comm (1 / 2) (b + 1), beta_add_one_left hb hsum,
      beta_comm b (1 / 2)]
  have hleft : beta (1 / 2 + 1) b =
      (1 / 2) / (1 / 2 + b) * beta (1 / 2) b :=
    beta_add_one_left (by norm_num) (by simpa [add_comm] using hsum)
  have hνdiv : ν / 2 = b + 1 := by
    dsimp [b]
    ring
  have hthree : (3 : ℝ) / 2 = 1 / 2 + 1 := by ring
  rw [hνdiv, hthree, hright, hleft]
  have hcoeff : 1 - b / (b + 1 / 2) = (1 / 2) / (1 / 2 + b) := by
    have hsum' : 1 / 2 + b ≠ 0 := by simpa [add_comm] using hsum
    have hbhalf : b + 1 / 2 = 1 / 2 + b := by ring
    rw [hbhalf]
    apply (eq_div_iff hsum').2
    rw [sub_mul, one_mul, div_mul_cancel₀ b hsum']
    ring
  calc
    beta (1 / 2) b - b / (b + 1 / 2) * beta (1 / 2) b =
        (1 - b / (b + 1 / 2)) * beta (1 / 2) b := by ring
    _ = (1 / 2) / (1 / 2 + b) * beta (1 / 2) b := by rw [hcoeff]

private lemma integral_sq_mul_studentTKernel (hν : 2 < ν) :
    ∫ x : ℝ, x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) =
      ν * √ν * beta (3 / 2) ((ν - 2) / 2) := by
  have hνpos : 0 < ν := lt_trans zero_lt_two hν
  have hshift : Integrable (fun x : ℝ =>
      (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2))) :=
    integrable_one_add_sq_div_rpow hνpos (by linarith)
  have hbase : Integrable (fun x : ℝ =>
      (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) :=
    integrable_one_add_sq_div_rpow hνpos (by linarith)
  have hminus : (ν - 1) / 2 - 1 / 2 = (ν - 2) / 2 := by ring
  have hplus : (ν + 1) / 2 - 1 / 2 = ν / 2 := by ring
  calc
    ∫ x : ℝ, x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) =
        ∫ x : ℝ, ν * ((1 + x ^ 2 / ν) ^ (-((ν - 1) / 2)) -
          (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
      exact integral_congr_ae (ae_of_all _ fun x => studentTKernel_sq hνpos x)
    _ = ν * ((∫ x : ℝ, (1 + x ^ 2 / ν) ^ (-((ν - 1) / 2))) -
          ∫ x : ℝ, (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) := by
      rw [integral_const_mul, integral_sub hshift hbase]
    _ = ν * (√ν * beta (1 / 2) ((ν - 1) / 2 - 1 / 2) -
          √ν * beta (1 / 2) ((ν + 1) / 2 - 1 / 2)) := by
      rw [integral_one_add_sq_div_rpow hνpos (by linarith),
        integral_one_add_sq_div_rpow hνpos (by linarith)]
    _ = ν * √ν * beta (3 / 2) ((ν - 2) / 2) := by
      rw [hminus, hplus, ← mul_sub, beta_sub_beta_add_one hν]
      ring

/-- The second raw moment of a Student t law is `ν / (ν - 2)` when `2 < ν`. -/
@[simp]
theorem integral_sq_studentTMeasure (hν : 2 < ν) :
    ∫ x, x ^ 2 ∂studentTMeasure ν = ν / (ν - 2) := by
  have hνpos : 0 < ν := lt_trans zero_lt_two hν
  have hbpos : 0 < (ν - 2) / 2 := by linarith
  have hGν : Real.Gamma (ν / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hGb : Real.Gamma ((ν - 2) / 2) ≠ 0 := (Real.Gamma_pos_of_pos hbpos).ne'
  have hGs : Real.Gamma ((ν + 1) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hsqrtν : √ν ≠ 0 := (Real.sqrt_pos.mpr hνpos).ne'
  have hsqrtπ : √π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hsub : ν - 2 ≠ 0 := by linarith
  have hthree : (3 : ℝ) / 2 = 1 / 2 + 1 := by ring
  have hgammaSum : (1 : ℝ) / 2 + 1 + (ν - 2) / 2 = (ν + 1) / 2 := by ring
  have hνhalf : ν / 2 = (ν - 2) / 2 + 1 := by ring
  rw [studentTMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_studentTPDF ν) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [toReal_studentTPDF, smul_eq_mul, studentTPDFReal_of_pos hνpos]
  calc
    ∫ x : ℝ, (Real.Gamma ((ν + 1) / 2) /
          (√(ν * π) * Real.Gamma (ν / 2)) *
          (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2))) * x ^ 2 =
        Real.Gamma ((ν + 1) / 2) /
          (√(ν * π) * Real.Gamma (ν / 2)) *
          ∫ x : ℝ, x ^ 2 * (1 + x ^ 2 / ν) ^ (-((ν + 1) / 2)) := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    _ = Real.Gamma ((ν + 1) / 2) /
          (√(ν * π) * Real.Gamma (ν / 2)) *
          (ν * √ν * beta (3 / 2) ((ν - 2) / 2)) := by
      rw [integral_sq_mul_studentTKernel hν]
    _ = ν / (ν - 2) := by
      rw [ProbabilityTheory.beta, hthree,
        Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0),
        Real.Gamma_one_half_eq, hgammaSum, hνhalf,
        Real.Gamma_add_one (ne_of_gt hbpos), Real.sqrt_mul hνpos.le]
      field_simp

/-- Squaring is integrable under a nondegenerate Student t law exactly when the number of degrees
of freedom exceeds two. -/
@[simp]
theorem integrable_sq_studentTMeasure_iff (hν : 0 < ν) :
    Integrable (fun x : ℝ => x ^ 2) (studentTMeasure ν) ↔ 2 < ν := by
  constructor
  · intro hint
    by_contra h
    exact not_integrable_pow_studentTMeasure hν 2 (by
      simpa using (not_lt.mp h : ν ≤ 2)) hint
  · exact integrable_sq_studentTMeasure_of_two_lt

/-- At or below two degrees of freedom, the second raw moment of a nondegenerate Student t law
diverges. -/
theorem not_integrable_sq_studentTMeasure (hν : 0 < ν) (hν2 : ν ≤ 2) :
    ¬ Integrable (fun x : ℝ => x ^ 2) (studentTMeasure ν) := by
  rw [integrable_sq_studentTMeasure_iff hν]
  exact not_lt.mpr hν2

/-- The variance of a Student t law is `ν / (ν - 2)` when `2 < ν`. -/
@[simp]
theorem variance_id_studentTMeasure (hν : 2 < ν) :
    variance id (studentTMeasure ν) = ν / (ν - 2) := by
  have _ : IsProbabilityMeasure (studentTMeasure ν) :=
    isProbabilityMeasure_studentTMeasure (lt_trans zero_lt_two hν)
  have hmem : MemLp id 2 (studentTMeasure ν) :=
    (memLp_two_iff_integrable_sq measurable_id'.aestronglyMeasurable).2
      (by simpa using integrable_sq_studentTMeasure_of_two_lt hν)
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_studentTMeasure hν, integral_id_studentTMeasure]
  ring

/-! ### One degree of freedom -/

/-- With one degree of freedom the Student t density is the standard Cauchy density. -/
theorem studentTPDFReal_one (x : ℝ) : studentTPDFReal 1 x = cauchyPDFReal 0 1 x := by
  have h1 : ((1 : ℝ) + 1) / 2 = 1 := by norm_num
  rw [studentTPDFReal_of_pos one_pos, cauchyPDFReal, h1, Real.Gamma_one,
    Real.sqrt_mul zero_le_one, Real.sqrt_one, one_mul, Real.Gamma_one_half_eq,
    Real.rpow_neg_one, Real.mul_self_sqrt Real.pi_pos.le]
  push_cast
  rw [div_one, sub_zero, one_pow, add_comm (x ^ 2) 1]
  ring

/-- **Student's t law with one degree of freedom is the standard Cauchy law.** -/
theorem studentTMeasure_one : studentTMeasure 1 = cauchyMeasure 0 1 := by
  rw [studentTMeasure, cauchyMeasure_of_scale_ne_zero 0 one_ne_zero]
  congr 1
  funext x
  rw [studentTPDF, studentTPDFReal_one, cauchyPDF]

/-! ### Parameter measurability -/

/-- The Student t density is jointly measurable in the degrees of freedom and the sample point. -/
@[fun_prop]
theorem measurable_uncurry_studentTPDF :
    Measurable fun q : ℝ × ℝ => studentTPDF q.1 q.2 := by
  have heq : (fun q : ℝ × ℝ => studentTPDF q.1 q.2) = fun q =>
      ENNReal.ofReal (if 0 < q.1 then
        Real.Gamma ((q.1 + 1) / 2) / (√(q.1 * π) * Real.Gamma (q.1 / 2)) *
          Real.exp (Real.log (1 + q.2 ^ 2 / q.1) * (-((q.1 + 1) / 2))) else 0) := by
    funext q
    rw [studentTPDF, studentTPDFReal]
    split_ifs with h
    · rw [Real.rpow_def_of_pos (by positivity)]
    · rfl
  rw [heq]
  refine (Measurable.ite ?_ ?_ measurable_const).ennreal_ofReal
  · exact measurableSet_lt (measurable_const : Measurable fun _ : ℝ × ℝ => (0 : ℝ)) measurable_fst
  · have hG1 : Measurable fun q : ℝ × ℝ => Real.Gamma ((q.1 + 1) / 2) :=
      Real.measurable_Gamma.comp (by fun_prop)
    have hG2 : Measurable fun q : ℝ × ℝ => Real.Gamma (q.1 / 2) :=
      Real.measurable_Gamma.comp (by fun_prop)
    have hsqrt : Measurable fun q : ℝ × ℝ => √(q.1 * π) :=
      Real.continuous_sqrt.measurable.comp (by fun_prop)
    exact (hG1.div (hsqrt.mul hG2)).mul (by fun_prop)

/-- The Student t family is measurable in its degrees of freedom. -/
@[fun_prop]
theorem measurable_studentTMeasure : Measurable fun ν : ℝ => studentTMeasure ν :=
  measurable_withDensity (μ := volume) measurable_uncurry_studentTPDF

end Probability

end TauCeti
