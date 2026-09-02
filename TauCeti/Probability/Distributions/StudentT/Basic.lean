/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

import TauCeti.Analysis.SpecialFunctions.Beta
public import TauCeti.Probability.Density
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Probability.Distributions.Cauchy
import TauCeti.Analysis.SpecialFunctions.Gamma
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Student's t distribution

Student's t law with `ν` degrees of freedom is the symmetric law on the line with density
proportional to `(1 + x ^ 2 / ν) ^ (-(ν + 1) / 2)`. This file defines it, proves that it is a
probability measure for `0 < ν`, identifies it as a `MeasureTheory.HasPDF` law with that density,
records its reflection symmetry, and identifies the one degree of freedom member of the family
with the standard Cauchy law.

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
* `studentTMeasure_one` — one degree of freedom gives the standard Cauchy law
  `ProbabilityTheory.cauchyMeasure 0 1`;
* `measurable_studentTMeasure` — the family is measurable in its parameter, so it can be used as a
  kernel.

## Implementation

The whole analytic content is the normalization. Scaling by `√ν` with
`MeasureTheory.integral_comp_mul_left` reduces the total mass of `(1 + x ^ 2 / ν) ^ (-(ν + 1) / 2)`
to that of the Cauchy-type kernel `(1 + x ^ 2) ^ (-(ν + 1) / 2)`, which is
`TauCeti.integral_one_add_sq_rpow`: the value `Β(1 / 2, ν / 2)` of Euler's second beta integral.
Writing that value as a quotient of Gamma values cancels the normalizing constant exactly.

## References

* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 3, the **Student's t** target.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2, 2nd ed.,
  Wiley (1995), ch. 28.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

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
